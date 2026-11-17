// Bounded encode/decode and durable save/load of public restart material: the
// retained window of published states and the selected head. Checkpoints never
// contain ORAM layout, position maps, stash contents, randomness or queries.

#pragma once

#include "version.hpp"

#include <cstddef>
#include <string>

namespace ethereum_mpt {

// Bounds apply to the complete file and cumulative account/storage counts.
// They also apply when encoding, before allocating the serialized image or
// rebuilding the canonical trie for root validation.
struct CheckpointLimits {
    std::size_t max_file_bytes = 256 * 1024 * 1024;
    std::size_t max_accounts = 1000000;
    std::size_t max_storage_slots = 4000000;
    std::size_t max_versions = 1024;
};

// Version 1, with explicit big-endian unsigned integers and no struct padding:
//   0: magic[8] = "EMPTCPT\0", 8: version u32=1, 12: reserved u32=0,
//  16: complete file size u64, 24: block ID[32], 56: parent ID[32],
//  88: state root[32], 120: block number u64, 128: fingerprint[32],
// 160: account count u64, 168: cumulative storage count u64.
// Starting at 176, each account has address[20], nonce u64, balance[32],
// code hash[32], storage count u64, then {slot[32], value[32]} records.
// Accounts and each account's slots are in strictly ascending byte order.
// The final 32 bytes are Keccak-256 of every preceding byte.
//
// This is a single public head, not an ORAM image. Decoding checks the checksum,
// canonical data, nonzero block ID and reconstructed state root. The checksum
// detects accidental corruption; it provides no authentication. Block metadata
// and the opaque delta fingerprint are not validated by Ethereum consensus.
// Callers must obtain expected block/root metadata through a trusted source and
// compare it before using a checkpoint from an untrusted source. A restart
// constructs fresh ORAM maps and does not preserve retained history/tombstones.
Bytes encode_public_checkpoint(const PublicCheckpoint& checkpoint,
                               CheckpointLimits limits = {});
PublicCheckpoint decode_public_checkpoint(const Bytes& bytes,
                                         CheckpointLimits limits = {});

// Version 2 retains the complete public window, in oldest-to-newest retention
// order. The served head may be any retained version, including an ancestor or
// a fork. The common 24-byte prefix is as above, with version=2. It is followed
// by served head[32], version count u64, cumulative account count u64 and
// cumulative storage count u64 (80 bytes total). Each version then contains
// block ID[32], parent ID[32], state root[32], number u64, fingerprint[32],
// account count u64 and storage count u64 (152 bytes), followed by the same
// account/storage records as version 1. One final checksum covers the complete
// preceding file. All resource limits apply cumulatively to the entire window.
// IDs must be unique and nonzero, the head must be retained, and retained
// parents must precede their children at exactly the previous block number.
// Missing parents are allowed because retention may have pruned them.
//
// The history decoder also promotes version-1 files to a one-version window.
// The single-checkpoint decoder rejects version 2 to avoid discarding history.
// Both formats contain public state only; neither restores ORAM state, pending
// updates, or identity tombstones for versions outside the retained window.
Bytes encode_public_history_checkpoint(const PublicHistoryCheckpoint& checkpoint,
                                       CheckpointLimits limits = {});
PublicHistoryCheckpoint decode_public_history_checkpoint(const Bytes& bytes,
                                                         CheckpointLimits limits = {});

// POSIX durable replacement: write a sibling temporary file, fsync its data,
// close it, rename it over path, then fsync the parent directory. Failures before
// rename preserve the previous checkpoint and remove the temporary file. A
// directory sync failure after rename reports that durability is uncertain;
// the new checkpoint is already visible. The parent directory must exist.
void save_public_checkpoint(const std::string& path,
                            const PublicCheckpoint& checkpoint,
                            CheckpointLimits limits = {});
PublicCheckpoint load_public_checkpoint(const std::string& path,
                                       CheckpointLimits limits = {});
void save_public_history_checkpoint(const std::string& path,
                                    const PublicHistoryCheckpoint& checkpoint,
                                    CheckpointLimits limits = {});
PublicHistoryCheckpoint load_public_history_checkpoint(const std::string& path,
                                                       CheckpointLimits limits = {});

}  // namespace ethereum_mpt
