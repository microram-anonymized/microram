// Public history checkpoint codec (version 1 single head, version 2 retained
// window) and atomic durable file replacement. Public, variable-time code that
// runs outside the private traversal; layout in DESIGN.md, "Durable public
// restart material".

#include "checkpoint.hpp"

#include <algorithm>
#include <array>
#include <cerrno>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fcntl.h>
#include <limits>
#include <stdexcept>
#include <sys/stat.h>
#include <unistd.h>
#include <utility>

namespace ethereum_mpt {
namespace {

constexpr std::array<std::uint8_t, 8> magic{'E', 'M', 'P', 'T', 'C', 'P', 'T', 0};
constexpr std::size_t header_bytes = 176;
constexpr std::size_t history_header_bytes = 80;
constexpr std::size_t version_bytes = 152;
constexpr std::size_t checksum_bytes = 32;
constexpr std::size_t fixed_account_bytes = 100;
constexpr std::size_t storage_bytes = 64;
constexpr std::size_t minimum_bytes = header_bytes + checksum_bytes;

[[noreturn]] void invalid(const char* message) {
    throw std::invalid_argument(std::string("public checkpoint: ") + message);
}

[[noreturn]] void io_error(const char* operation, int error = errno) {
    throw std::runtime_error(std::string("public checkpoint: ") + operation +
                             ": " + std::strerror(error));
}

std::size_t bounded_count(std::uint64_t count, std::size_t maximum) {
    if (count > maximum) invalid("count exceeds configured limit");
    return static_cast<std::size_t>(count);
}

std::size_t encoded_size(std::size_t accounts, std::size_t slots,
                         CheckpointLimits limits, std::size_t versions = 1,
                         bool history = false) {
    // Check both arithmetic and the configured limit without any multiplication
    // or addition that could overflow. Vector's bound also covers ptrdiff_t.
    const auto maximum = std::min(limits.max_file_bytes, Bytes{}.max_size());
    if (versions == 0 || versions > limits.max_versions ||
        accounts > limits.max_accounts || slots > limits.max_storage_slots)
        invalid("count exceeds configured limit");
    std::size_t minimum = minimum_bytes;
    if (history) {
        minimum = history_header_bytes + checksum_bytes;
        if (maximum < minimum || versions > (maximum - minimum) / version_bytes)
            invalid("file exceeds configured byte limit");
        minimum += versions * version_bytes;
    }
    if (maximum < minimum ||
        accounts > (maximum - minimum) / fixed_account_bytes)
        invalid("file exceeds configured byte limit");
    const auto base = minimum + accounts * fixed_account_bytes;
    if (slots > (maximum - base) / storage_bytes)
        invalid("file exceeds configured byte limit");
    return base + slots * storage_bytes;
}

std::size_t storage_count(const PublicState& state, std::size_t maximum) {
    std::size_t slots = 0;
    for (const auto& [address, account] : state) {
        (void)address;
        if (account.storage.size() > maximum - slots)
            invalid("storage count exceeds configured limit");
        slots += account.storage.size();
    }
    return slots;
}

void validate_root(const PublicCheckpoint& checkpoint) {
    if (checkpoint.block.block_id == Hash{}) invalid("zero block ID");
    if (snapshot_from_state(checkpoint.state).accounts.root_hash() !=
        checkpoint.block.state_root)
        invalid("state root mismatch");
}

template <std::size_t N>
void append(Bytes& output, const std::array<std::uint8_t, N>& value) {
    output.insert(output.end(), value.begin(), value.end());
}

void append_integer(Bytes& output, std::uint64_t value, std::size_t width) {
    for (std::size_t i = width; i != 0; --i)
        output.push_back(static_cast<std::uint8_t>(value >> ((i - 1) * 8)));
}

void append_checkpoint(Bytes& bytes, const PublicCheckpoint& checkpoint, std::size_t slots) {
    append(bytes, checkpoint.block.block_id);
    append(bytes, checkpoint.block.parent_id);
    append(bytes, checkpoint.block.state_root);
    append_integer(bytes, checkpoint.block.number, 8);
    append(bytes, checkpoint.fingerprint);
    append_integer(bytes, checkpoint.state.size(), 8);
    append_integer(bytes, slots, 8);
    for (const auto& [address, account] : checkpoint.state) {
        append(bytes, address);
        append_integer(bytes, account.nonce, 8);
        append(bytes, account.balance);
        append(bytes, account.code_hash);
        append_integer(bytes, account.storage.size(), 8);
        for (const auto& [slot, value] : account.storage) {
            append(bytes, slot);
            append(bytes, value);
        }
    }
}

class Reader {
 public:
    Reader(const Bytes& bytes, std::size_t end) : bytes_(bytes), end_(end) {}

    template <std::size_t N>
    std::array<std::uint8_t, N> array() {
        require(N);
        std::array<std::uint8_t, N> value{};
        std::copy_n(bytes_.data() + position_, N, value.data());
        position_ += N;
        return value;
    }

    std::uint64_t integer(std::size_t width) {
        require(width);
        std::uint64_t value = 0;
        for (std::size_t i = 0; i < width; ++i)
            value = (value << 8) | bytes_[position_++];
        return value;
    }

    std::size_t remaining() const { return end_ - position_; }

 private:
    void require(std::size_t count) const {
        if (count > remaining()) invalid("truncated file");
    }

    const Bytes& bytes_;
    std::size_t end_, position_ = 0;
};

std::uint64_t read_prefix(Reader& reader, std::size_t size) {
    if (reader.array<8>() != magic) invalid("incorrect magic");
    const auto version = reader.integer(4);
    if (reader.integer(4) != 0) invalid("nonzero reserved field");
    if (reader.integer(8) != size) invalid("file length mismatch");
    return version;
}

void validate_file(const Bytes& bytes, CheckpointLimits limits) {
    if (bytes.size() < minimum_bytes) invalid("truncated file");
    if (bytes.size() > limits.max_file_bytes)
        invalid("file exceeds configured byte limit");
}

void validate_checksum(const Bytes& bytes) {
    const auto checksum = keccak256(bytes.data(), bytes.size() - checksum_bytes);
    if (!std::equal(checksum.begin(), checksum.end(), bytes.end() - checksum_bytes))
        invalid("checksum mismatch");
}

PublicCheckpoint read_metadata(Reader& reader) {
    PublicCheckpoint checkpoint;
    checkpoint.block.block_id = reader.array<32>();
    checkpoint.block.parent_id = reader.array<32>();
    checkpoint.block.state_root = reader.array<32>();
    checkpoint.block.number = reader.integer(8);
    checkpoint.fingerprint = reader.array<32>();
    return checkpoint;
}

void read_state(Reader& reader, PublicCheckpoint& checkpoint, std::size_t accounts,
                std::size_t slots) {
    // Both products are bounded by encoded_size before this is called. Keep
    // subsequent version records outside this version's parse budget.
    const auto body_bytes = accounts * fixed_account_bytes + slots * storage_bytes;
    if (body_bytes > reader.remaining()) invalid("truncated state records");
    const auto trailing_bytes = reader.remaining() - body_bytes;
    std::size_t consumed_slots = 0;
    Address previous_address{};
    for (std::size_t i = 0; i < accounts; ++i) {
        const auto address = reader.array<20>();
        if (i != 0 && !(previous_address < address))
            invalid("account addresses are not strictly ascending");
        previous_address = address;
        PublicAccountState account;
        account.nonce = reader.integer(8);
        account.balance = reader.array<32>();
        account.code_hash = reader.array<32>();
        const auto count = bounded_count(reader.integer(8), slots - consumed_slots);
        const auto next_accounts_bytes = (accounts - i - 1) * fixed_account_bytes;
        if (reader.remaining() < trailing_bytes + next_accounts_bytes ||
            count > (reader.remaining() - trailing_bytes - next_accounts_bytes) / storage_bytes)
            invalid("truncated storage records");
        consumed_slots += count;
        Word previous_slot{};
        for (std::size_t j = 0; j < count; ++j) {
            const auto slot = reader.array<32>();
            const auto value = reader.array<32>();
            if (j != 0 && !(previous_slot < slot))
                invalid("storage slots are not strictly ascending");
            if (value == Word{}) invalid("zero storage value");
            previous_slot = slot;
            account.storage.emplace_hint(account.storage.end(), slot, value);
        }
        checkpoint.state.emplace_hint(checkpoint.state.end(), address, std::move(account));
    }
    if (consumed_slots != slots || reader.remaining() != trailing_bytes)
        invalid("storage count mismatch or trailing bytes");
}

class FileDescriptor {
 public:
    explicit FileDescriptor(int fd) : fd_(fd) {}
    FileDescriptor(const FileDescriptor&) = delete;
    FileDescriptor& operator=(const FileDescriptor&) = delete;
    ~FileDescriptor() { if (fd_ >= 0) ::close(fd_); }
    int get() const { return fd_; }
    void close_checked() {
        const auto fd = fd_;
        // Do not retry close on EINTR: on Linux the descriptor is already closed
        // and another thread could reuse it before the retry.
        fd_ = -1;
        if (::close(fd) != 0) io_error("closing temporary file");
    }

 private:
    int fd_;
};

class TemporaryFile {
 public:
    explicit TemporaryFile(std::string path) : path_(std::move(path)) {}
    ~TemporaryFile() { if (created_ && !renamed_) ::unlink(path_.c_str()); }
    int create() {
        const auto fd = ::mkstemp(path_.data());
        if (fd < 0) io_error("creating temporary file");
        created_ = true;
        return fd;
    }
    const char* path() const { return path_.c_str(); }
    void renamed() { renamed_ = true; }

 private:
    std::string path_;
    bool created_ = false, renamed_ = false;
};

std::string parent_directory(const std::string& path) {
    if (path.empty() || path.find('\0') != std::string::npos)
        invalid("invalid file path");
    const auto slash = path.find_last_of('/');
    const auto basename = path.substr(slash == std::string::npos ? 0 : slash + 1);
    if (basename.empty() || basename == "." || basename == "..")
        invalid("path must name a file");
    if (slash == std::string::npos) return ".";
    return slash == 0 ? "/" : path.substr(0, slash);
}

void sync_file(int fd, const char* operation) {
    while (::fsync(fd) != 0) {
        if (errno != EINTR) io_error(operation);
    }
}

std::size_t io_chunk(std::size_t remaining) {
    return std::min(remaining,
                    static_cast<std::size_t>(std::numeric_limits<ssize_t>::max()));
}

}  // namespace

Bytes encode_public_checkpoint(const PublicCheckpoint& checkpoint,
                               CheckpointLimits limits) {
    if (checkpoint.state.size() > limits.max_accounts)
        invalid("account count exceeds configured limit");
    const auto slots = storage_count(checkpoint.state, limits.max_storage_slots);
    const auto size = encoded_size(checkpoint.state.size(), slots, limits);
    validate_root(checkpoint);
    Bytes bytes;
    bytes.reserve(size);
    append(bytes, magic);
    append_integer(bytes, 1, 4);
    append_integer(bytes, 0, 4);
    append_integer(bytes, size, 8);
    append_checkpoint(bytes, checkpoint, slots);
    append(bytes, keccak256(bytes));
    return bytes;
}

PublicCheckpoint decode_public_checkpoint(const Bytes& bytes,
                                         CheckpointLimits limits) {
    validate_file(bytes, limits);
    Reader reader(bytes, bytes.size() - checksum_bytes);
    if (read_prefix(reader, bytes.size()) != 1) invalid("unsupported version");
    auto checkpoint = read_metadata(reader);
    const auto accounts = bounded_count(reader.integer(8), limits.max_accounts);
    const auto slots = bounded_count(reader.integer(8), limits.max_storage_slots);
    if (encoded_size(accounts, slots, limits) != bytes.size())
        invalid("record counts do not match file length");
    validate_checksum(bytes);
    if (checkpoint.block.block_id == Hash{}) invalid("zero block ID");

    read_state(reader, checkpoint, accounts, slots);
    validate_root(checkpoint);
    return checkpoint;
}

Bytes encode_public_history_checkpoint(const PublicHistoryCheckpoint& checkpoint,
                                       CheckpointLimits limits) {
    if (checkpoint.versions.empty() || checkpoint.versions.size() > limits.max_versions)
        invalid("version count exceeds configured limit or is zero");
    std::size_t accounts = 0, slots = 0;
    for (const auto& version : checkpoint.versions) {
        if (version.state.size() > limits.max_accounts - accounts)
            invalid("account count exceeds configured limit");
        accounts += version.state.size();
        slots += storage_count(version.state, limits.max_storage_slots - slots);
    }
    const auto size = encoded_size(accounts, slots, limits, checkpoint.versions.size(), true);
    // Limits precede trie reconstruction and serialized-image allocation.
    validate_public_history_checkpoint(checkpoint);
    Bytes bytes;
    bytes.reserve(size);
    append(bytes, magic);
    append_integer(bytes, 2, 4);
    append_integer(bytes, 0, 4);
    append_integer(bytes, size, 8);
    append(bytes, checkpoint.served_head);
    append_integer(bytes, checkpoint.versions.size(), 8);
    append_integer(bytes, accounts, 8);
    append_integer(bytes, slots, 8);
    for (const auto& version : checkpoint.versions)
        append_checkpoint(bytes, version, storage_count(version.state, slots));
    append(bytes, keccak256(bytes));
    return bytes;
}

PublicHistoryCheckpoint decode_public_history_checkpoint(const Bytes& bytes,
                                                         CheckpointLimits limits) {
    validate_file(bytes, limits);
    Reader reader(bytes, bytes.size() - checksum_bytes);
    const auto format = read_prefix(reader, bytes.size());
    if (format == 1) {
        auto version = decode_public_checkpoint(bytes, limits);
        const auto head = version.block.block_id;
        // A legacy file leaves parent metadata opaque, but promotion must
        // satisfy the history invariant that retained parents precede children.
        // With one version, the only possible retained parent is itself.
        if (version.block.parent_id == head) invalid("retained version is its own parent");
        PublicHistoryCheckpoint checkpoint{head, {}};
        checkpoint.versions.push_back(std::move(version));
        return checkpoint;
    }
    if (format != 2) invalid("unsupported version");
    PublicHistoryCheckpoint checkpoint;
    checkpoint.served_head = reader.array<32>();
    const auto versions = bounded_count(reader.integer(8), limits.max_versions);
    const auto accounts = bounded_count(reader.integer(8), limits.max_accounts);
    const auto slots = bounded_count(reader.integer(8), limits.max_storage_slots);
    if (encoded_size(accounts, slots, limits, versions, true) != bytes.size())
        invalid("record counts do not match file length");
    validate_checksum(bytes);
    // The complete window's counts and size are checked before allocating its
    // public states or rebuilding any canonical trie.
    checkpoint.versions.reserve(versions);
    std::size_t consumed_accounts = 0, consumed_slots = 0;
    for (std::size_t i = 0; i < versions; ++i) {
        auto version = read_metadata(reader);
        const auto version_accounts = bounded_count(reader.integer(8), accounts - consumed_accounts);
        const auto version_slots = bounded_count(reader.integer(8), slots - consumed_slots);
        consumed_accounts += version_accounts;
        consumed_slots += version_slots;
        read_state(reader, version, version_accounts, version_slots);
        checkpoint.versions.push_back(std::move(version));
    }
    if (consumed_accounts != accounts || consumed_slots != slots || reader.remaining() != 0)
        invalid("history count mismatch or trailing bytes");
    validate_public_history_checkpoint(checkpoint);
    return checkpoint;
}

namespace {

void save_bytes(const std::string& path, const Bytes& bytes) {
    const auto parent = parent_directory(path);
    FileDescriptor directory(::open(parent.c_str(), O_RDONLY | O_DIRECTORY | O_CLOEXEC));
    if (directory.get() < 0) io_error("opening parent directory");
    TemporaryFile temporary(path + ".tmp.XXXXXX");
    FileDescriptor file(temporary.create());
    if (::fcntl(file.get(), F_SETFD, FD_CLOEXEC) != 0)
        io_error("setting temporary file close-on-exec");
    std::size_t offset = 0;
    while (offset < bytes.size()) {
        const auto written = ::write(file.get(), bytes.data() + offset,
                                     io_chunk(bytes.size() - offset));
        if (written < 0) {
            if (errno == EINTR) continue;
            io_error("writing temporary file");
        }
        if (written == 0) io_error("writing temporary file made no progress", EIO);
        offset += static_cast<std::size_t>(written);
    }
    sync_file(file.get(), "syncing temporary file");
    file.close_checked();
    if (::rename(temporary.path(), path.c_str()) != 0)
        io_error("replacing checkpoint file");
    temporary.renamed();
    sync_file(directory.get(), "checkpoint replaced; durability uncertain while syncing parent directory");
}

Bytes load_bytes(const std::string& path, CheckpointLimits limits) {
    (void)parent_directory(path);
    // O_NONBLOCK avoids waiting indefinitely when an invalid input names a
    // FIFO. Regular files are unaffected, and all other file kinds are rejected.
    FileDescriptor file(::open(path.c_str(), O_RDONLY | O_CLOEXEC | O_NONBLOCK));
    if (file.get() < 0) io_error("opening checkpoint file");
    struct stat status {};
    if (::fstat(file.get(), &status) != 0) io_error("inspecting checkpoint file");
    if (!S_ISREG(status.st_mode)) invalid("input is not a regular file");
    if (status.st_size < 0 ||
        static_cast<std::uintmax_t>(status.st_size) > limits.max_file_bytes ||
        static_cast<std::uintmax_t>(status.st_size) > Bytes{}.max_size())
        invalid("file exceeds configured byte limit");
    const auto size = static_cast<std::size_t>(status.st_size);
    if (size < minimum_bytes) invalid("truncated file");
    Bytes bytes(size);
    std::size_t offset = 0;
    while (offset < size) {
        const auto count = ::read(file.get(), bytes.data() + offset, io_chunk(size - offset));
        if (count < 0) {
            if (errno == EINTR) continue;
            io_error("reading checkpoint file");
        }
        if (count == 0) invalid("truncated file");
        offset += static_cast<std::size_t>(count);
    }
    std::uint8_t trailing = 0;
    for (;;) {
        const auto count = ::read(file.get(), &trailing, 1);
        if (count < 0) {
            if (errno == EINTR) continue;
            io_error("checking checkpoint file length");
        }
        if (count != 0) invalid("file grew while reading");
        break;
    }
    return bytes;
}

}  // namespace

void save_public_checkpoint(const std::string& path,
                            const PublicCheckpoint& checkpoint,
                            CheckpointLimits limits) {
    save_bytes(path, encode_public_checkpoint(checkpoint, limits));
}

PublicCheckpoint load_public_checkpoint(const std::string& path,
                                       CheckpointLimits limits) {
    return decode_public_checkpoint(load_bytes(path, limits), limits);
}

void save_public_history_checkpoint(const std::string& path,
                                    const PublicHistoryCheckpoint& checkpoint,
                                    CheckpointLimits limits) {
    save_bytes(path, encode_public_history_checkpoint(checkpoint, limits));
}

PublicHistoryCheckpoint load_public_history_checkpoint(const std::string& path,
                                                       CheckpointLimits limits) {
    return decode_public_history_checkpoint(load_bytes(path, limits), limits);
}

}  // namespace ethereum_mpt
