// What each engine really allocates, against what its resolved plan models.
//
// The resolver reports a plan's memory as components (ResolvedPlan::
// memory_components): a hierarchy's byte bill by role (incremental or
// synchronous), and a tree's arenas plus its position map's bill.  None of
// them says how much of the process's memory it covers.  This tool measures
// that, by replacing the global allocator:
// every library buffer -- the huge-page arenas included -- comes from
// operator new, so a counting operator new sees every heap byte an engine
// takes, both as REQUESTED and as GRANTED by glibc (malloc_usable_size, which
// includes the allocator's own rounding).
//
// Each row resolves a plan the way a campaign row of analysis/oram_bench
// does (the budget is this host's physical cores with one reserved for the
// harness), builds the map with make_map, fills it the way the worker does (direct initialization for
// a hierarchy, insertions for a tree), then runs a mixed read/write phase.
// At each of those three checkpoints it prints the live heap and the phase's
// peak, and at the end it checks that destruction returned every byte.
//
//   cpu_oram_allocation_audit [--capacities LIST] [--shapes k:v,...]
//                             [--schemes LIST] [--cores N] [--accesses F]
//
// Output: one JSON object per row on stdout (AUDIT_ROW), then a table on
// stderr.  The numbers are this host's: allocator rounding and thread stacks
// are the only host-dependent parts, and neither changes what the library
// requests.  Every row runs in this one process, so the peak RSS (VmHWM) is
// reset before each row (/proc/self/clear_refs); where that is refused, the
// row's `hwm` is null.  Exit status: 0 when every row ran and returned every
// byte at destruction, 1 when a row failed or leaked, 2 for a usage error.

#include <execinfo.h>
#include <fcntl.h>
#include <unistd.h>

#include <algorithm>
#include <atomic>
#include <cctype>
#include <chrono>
#include <cinttypes>
#include <climits>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <new>
#include <sstream>
#include <string>
#include <thread>
#include <vector>

#include <cpu_byteslice_oram/configuration.hpp>

#include "benchmarks/oram/cpu_byteslice_benchmark_support.hpp"
#include "benchmarks/support/counting_allocator.hpp"
#include "src/oram/table/cpu_byteslice_host_cores.hpp"

// ---------------------------------------------------------------------------
// The rows
// ---------------------------------------------------------------------------

namespace {

namespace api = cpu_byteslice_oram;
namespace bs = microram::byteslice;

// Resident set and threads, from /proc/self/status.
struct ProcStatus {
  size_t rss = 0, hwm = 0;
  unsigned threads = 0;
};

ProcStatus ReadStatus() {
  ProcStatus out;
  std::ifstream in("/proc/self/status");
  std::string line;
  while (std::getline(in, line)) {
    unsigned long long v = 0;
    if (std::sscanf(line.c_str(), "VmRSS: %llu kB", &v) == 1) out.rss = v * 1024;
    if (std::sscanf(line.c_str(), "VmHWM: %llu kB", &v) == 1) out.hwm = v * 1024;
    if (std::sscanf(line.c_str(), "Threads: %llu", &v) == 1) out.threads = v;
  }
  return out;
}

// Resets this process's peak RSS (VmHWM) to its current RSS (Linux 4.0 and
// later), so the next row's `hwm` is that row's own peak and not an earlier,
// larger row's.  No heap allocation.  False when the kernel refuses.
bool ResetPeakRss() {
  const int fd = open("/proc/self/clear_refs", O_WRONLY | O_CLOEXEC);
  if (fd < 0) return false;
  const bool ok = write(fd, "5", 1) == 1;
  close(fd);
  return ok;
}

const char* SchemeName(api::Scheme s) {
  switch (s) {
    case api::Scheme::kHierarchicalIncremental: return "hierarchical_incremental";
    case api::Scheme::kHierarchicalSynchronous: return "hierarchical_synchronous";
    case api::Scheme::kTree: return "tree";
    case api::Scheme::kAuto: return "auto";
  }
  return "?";
}

void Key(uint64_t id, uint8_t* out, size_t bytes) {
  std::memset(out, 0, bytes);
  uint64_t state = id * 0x9E3779B97F4A7C15ull + 1;
  for (size_t b = 0; b < bytes; b += 8) {
    const uint64_t word = bs::benchmark_support::SplitMix64(state);
    std::memcpy(out + b, &word, std::min<size_t>(8, bytes - b));
  }
  // Keep the key an injective function of id in its first bytes.
  std::memcpy(out, &id, std::min<size_t>(sizeof(id), bytes));
}

void Value(uint64_t id, uint8_t* out, size_t bytes) {
  for (size_t b = 0; b < bytes; ++b) out[b] = static_cast<uint8_t>(id + b);
}

struct Phase {
  audit::Snapshot heap;  // the library's allocations (outside every HarnessScope)
  audit::Snapshot all;   // the process's: library + harness
  ProcStatus status;
  double seconds = 0;
};

// Names a site by its innermost library frames, through addr2line on this
// binary.  For names, compile with -g -fno-pie and link with -no-pie
// (benchmarks/oram/README.md); otherwise a site is its addresses.
bool g_sites_mode = false;
// --steady-sites: attribute the ACCESS phase's allocations instead.
bool g_steady_sites = false;

bool Boring(const std::string& name) {
  static const char* const kSkip[] = {
      "operator new", "std::", "__gnu_cxx::", "audit::", "AllocateAligned64",
      "AllocateTallied", "MakeTalliedArray", "malloc", "??", "_M_", "__new_allocator"};
  for (const char* skip : kSkip) {
    if (name.find(skip) != std::string::npos) return true;
  }
  return false;
}

std::string ShortName(std::string name) {
  // Drop argument lists and template arguments: the function is the point.
  std::string out;
  int depth = 0;
  for (char c : name) {
    if (c == '<' || c == '(') ++depth;
    if (depth == 0) out += c;
    if ((c == '>' || c == ')') && depth > 0) --depth;
  }
  for (const char* prefix : {"microram::byteslice::levelarena::",
                             "microram::byteslice::", "microram::tree::",
                             "microram::", "cpu_byteslice_oram::"}) {
    size_t at;
    while ((at = out.find(prefix)) != std::string::npos) out.erase(at, std::strlen(prefix));
  }
  return out;
}

std::vector<std::string> NameSites(const audit::SiteLive* sites, size_t n,
                                   int max_names = 3) {
  // /proc/self/exe inside the command would name addr2line itself.
  char self[4096];
  const ssize_t len = readlink("/proc/self/exe", self, sizeof(self) - 1);
  if (len <= 0) return std::vector<std::string>(n, "?");
  self[len] = '\0';
  std::string cmd = std::string("addr2line -a -f -C -i -e ") + self;
  char hex[32];
  for (size_t i = 0; i < n; ++i) {
    for (int f = 3; f < sites[i].depth; ++f) {
      std::snprintf(hex, sizeof(hex), " %p", sites[i].frames[f]);
      cmd += hex;
    }
  }
  std::vector<std::pair<uintptr_t, std::vector<std::string>>> groups;
  if (FILE* pipe = popen(cmd.c_str(), "r")) {
    char line[4096];
    bool function_line = false;
    while (std::fgets(line, sizeof(line), pipe)) {
      std::string text(line);
      if (!text.empty() && text.back() == '\n') text.pop_back();
      if (text.rfind("0x", 0) == 0) {
        groups.push_back({std::stoull(text, nullptr, 16), {}});
        function_line = true;
      } else if (function_line && !groups.empty()) {
        groups.back().second.push_back(text);
        function_line = false;
      } else {
        function_line = true;  // a file:line; the next line names a function
      }
    }
    pclose(pipe);
  }
  std::vector<std::string> out;
  size_t g = 0;
  for (size_t i = 0; i < n; ++i) {
    std::string where;
    int named = 0;
    for (int f = 3; f < sites[i].depth && g < groups.size(); ++f, ++g) {
      for (const std::string& name : groups[g].second) {
        if (named >= max_names || Boring(name)) continue;
        const std::string shortened = ShortName(name);
        if (where.find(shortened) != std::string::npos) continue;
        where += (named++ ? " < " : "") + shortened;
      }
    }
    out.push_back(where.empty() ? "?" : where);
  }
  return out;
}

// The first `n` frames of a ' < ' chain.
std::string ShortChain(const std::string& chain, int n) {
  size_t at = 0;
  for (int i = 0; i < n; ++i) {
    at = chain.find(" < ", at);
    if (at == std::string::npos) return chain;
    if (i + 1 < n) at += 3;
  }
  return chain.substr(0, at);
}

// ROLE ATTRIBUTION.  A site's function chain (innermost first, ' < '
// between frames) names the library component that made the allocation.  The
// first rule that matches wins; a chain no rule matches is `unattributed` and
// is reported with its names, never given a role by guess.  Two roles are
// COMBINED because the library makes one allocation for several byte roles
// and the heap cannot tell them apart:
//   arena_combined   the level arenas: per level one data buffer (mains plus
//                    the embedded tier regions, which are holes), a mask
//                    array and the slot runtimes, plus the set's tier pool;
//   sync_tables      the synchronous mode's live tables.
// analysis/allocation_reconcile.py matches their block sizes to the layout
// model's exact per-level sizes and labels anything it can only split by
// model.
// In a tree row every level-arena allocation belongs to the position map.
struct RoleRule {
  const char* role;
  std::vector<const char*> any;  // substrings of the chain (or of its first frame)
  bool first_frame_only;         // match only the innermost named frame
  bool exact = false;            // the whole chain must equal a needle
};

std::string ClassifyChain(api::Scheme scheme, const std::string& chain) {
  static const std::vector<RoleRule> kRules = {
      {"harness_runtime", {"main", "RunRow", "::RunRow"}, true, true},
      {"tree", {"TreeStorage", "TreeKnobs", "CpuReadPathOram", "ReadPathPlane", "PayloadWorkerPoolT",
                "PayloadJobSlotT", "TreeByteMap", "TreeOptions", "CpuTreeMap"}, false},
      {"online_stash", {"DensePrefixRing"}, false},
      {"scratch", {"LevelMergeScratch", "DfsResidualWorkspace", "LevelMergeJob", "ProbeScratch",
                   "BatchProbeScratch", "ParallelBatch", "LevelArenaBatchTile", "BatchForwardState"}, false},
      {"sync_tables", {"SynchronousLevels", "LiveTableSlots"}, false},
      {"plans", {"ProbeAddressing::Reserve", "LevelArenaPublisher::MakePlan"}, false},
      {"arena_combined", {"LevelArena::LevelArena", "LevelArenaSet::LevelArenaSet"}, true},
      {"metadata", {"LevelArenaEngine", "LevelArenaSet", "LevelState", "LevelSource", "LevelGroup", "LevelBoundary",
                    "LevelArenaGeometry", "LevelArenaPublisher", "ConfiguredByteMap", "PlanData", "ResolvedChoice",
                    "ConstructionHooks", "ByteMap::", "make_map", "MakeArenaEngine"}, false},
  };
  const std::string first = chain.substr(0, chain.find(" < "));
  const bool synchronous = scheme == api::Scheme::kHierarchicalSynchronous;
  std::string role = "unattributed";
  for (const RoleRule& rule : kRules) {
    const std::string& subject = rule.first_frame_only ? first : chain;
    bool hit = false;
    for (const char* needle : rule.any) {
      hit = hit || (rule.exact ? subject == needle : subject.find(needle) != std::string::npos);
    }
    if (hit) { role = rule.role; break; }
  }
  // Outside the synchronous mode, LiveTableSlots is only a count's name: what
  // it allocates are the arena engine's own bookkeeping vectors.
  if (role == "sync_tables" && !synchronous) role = "metadata";
  // The tree's only hierarchy is its position map: in a tree row, every
  // level-arena allocation (and the engine pieces around it) is the map's.
  if (scheme == api::Scheme::kTree && role != "tree" && role != "harness_runtime" && role != "unattributed") {
    for (const char* piece : {"Level", "Dense", "Batch", "Probe", "Publisher", "MakeArenaEngine"}) {
      if (chain.find(piece) != std::string::npos) role = "position_map";
    }
  }
  if (chain.find("HierarchicalPositionMap") != std::string::npos) role = "position_map";
  return role;
}

struct BlockGroup {
  std::string role, where;
  size_t bytes, count, granted;  // requested size of each block, blocks, granted total
};

struct Row {
  api::Scheme scheme;
  size_t capacity, key_bytes, value_bytes;
  bool ok = false;
  std::string error;
  size_t actual_capacity = 0;
  size_t modeled = 0, reserved = 0;
  std::vector<api::PlannedMemory> components;
  std::vector<std::pair<std::string, std::string>> choices;  // the resolved plan's, for the ladder
  unsigned planned_threads = 0;
  size_t baseline_requested = 0, baseline_granted = 0, baseline_all_requested = 0;
  unsigned baseline_threads = 0;
  bool hwm_reset = false;  // VmHWM was reset before the row: `hwm` is the row's own
  Phase constructed, filled, steady;
  audit::Snapshot destroyed{};
  uint64_t accesses = 0;
  // --sites: what is live after the fill, by allocation site.
  std::vector<std::pair<size_t, std::string>> sites;
  std::vector<BlockGroup> blocks;  // live after the fill, by site and block size
};

Row RunRow(api::Scheme scheme, size_t capacity, size_t key_bytes,
           size_t value_bytes, unsigned cores, double access_factor) {
  Row row{scheme, capacity, key_bytes, value_bytes};
  try {
    // The plan is resolved OUTSIDE the measurement: it is the caller's
    // object, and only the map's lifetime is the library's.
    api::MapSpec spec{capacity, key_bytes, value_bytes};
    api::ResourceBudget budget;
    budget.cores = cores;
    budget.harness_cores = cores > 1 ? 1 : 0;
    api::OptionOverrides overrides;
    overrides.scheme = scheme;
    const api::ResolvedPlan plan = api::resolve_options(spec, budget, {}, overrides);
    row.actual_capacity = plan.actual_capacity();
    row.modeled = plan.modeled_buffer_bytes();
    row.reserved = plan.modeled_reserved_bytes();
    row.components = plan.memory_components();
    for (const auto& c : plan.choices()) row.choices.push_back({c.field, c.value});
    row.planned_threads = static_cast<unsigned>(plan.threads().size());
    static uint64_t rows = 0;
    audit::g_row = ++rows;
    row.hwm_reset = ResetPeakRss();
    const audit::Snapshot base = audit::TakeLibrary();
    row.baseline_all_requested = audit::Take().live_requested;
    row.baseline_requested = base.live_requested;
    row.baseline_granted = base.live_granted;
    row.baseline_threads = ReadStatus().threads;
    size_t live_sites = 0, live_blocks = 0;
    if (g_sites_mode) {
      audit::ResetSites();
      audit::g_capture = true;
    }
    {
      audit::Mark();
      auto t0 = std::chrono::steady_clock::now();
      api::ConfiguredByteMap map = api::make_map(plan);
      auto t1 = std::chrono::steady_clock::now();
      row.constructed = {audit::TakeLibrary(), audit::Take(), ReadStatus(),
                         std::chrono::duration<double>(t1 - t0).count()};

      audit::Mark();
      std::vector<uint8_t> key, value, out;
      {
        audit::HarnessScope harness;  // the audit's own buffers are not the library's
        key.resize(key_bytes);
        value.resize(value_bytes);
        out.resize(value_bytes);
      }
      const uint64_t live = capacity;
      if (map.supports_direct_initialization()) {
        auto make_records = [&] {
          audit::HarnessScope harness;  // the dataset handed to initialize()
          return bs::benchmark_support::MakeGeneratedRecords(
              0, key_bytes, value_bytes,
              [&](uint64_t id, uint8_t* o) { Key(id, o, key_bytes); },
              [&](uint64_t id, uint8_t* o, size_t n) { Value(id, o, n); });
        };
        auto records = make_records();
        map.initialize(records, live);
      } else {
        for (uint64_t id = 0; id < live; ++id) {
          Key(id, key.data(), key_bytes);
          Value(id, value.data(), value_bytes);
          map.insert_or_assign(key.data(), value.data());
        }
      }
      map.finish_pending_work();
      auto t2 = std::chrono::steady_clock::now();
      row.filled = {audit::TakeLibrary(), audit::Take(), ReadStatus(),
                    std::chrono::duration<double>(t2 - t1).count()};
      if (g_sites_mode) {
        audit::g_capture = false;
        live_sites = audit::CopyLiveSites();
        live_blocks = audit::CopyLiveBlocks();
      }
      if (g_steady_sites) {
        audit::ResetSites();
        audit::g_capture = true;
      }

      // Mixed reads and overwrites over the live keys: the steady state a
      // campaign trial measures, rebuilds included.
      audit::Mark();
      row.accesses = static_cast<uint64_t>(access_factor * double(capacity));
      uint64_t state = 12345;
      for (uint64_t i = 0; i < row.accesses; ++i) {
        const uint64_t r = bs::benchmark_support::SplitMix64(state);
        const uint64_t id = r % live;
        Key(id, key.data(), key_bytes);
        if ((r >> 63) != 0) {
          Value(id + i, value.data(), value_bytes);
          map.insert_or_assign(key.data(), value.data());
        } else if (!map.find(key.data(), out.data())) {
          throw std::runtime_error("a live key was not found");
        }
      }
      map.finish_pending_work();
      auto t3 = std::chrono::steady_clock::now();
      row.steady = {audit::TakeLibrary(), audit::Take(), ReadStatus(),
                    std::chrono::duration<double>(t3 - t2).count()};
      if (g_steady_sites) {
        audit::g_capture = false;
        live_sites = audit::CopyLiveSites(/*total=*/true);
      }
    }
    row.destroyed = audit::TakeLibrary();
    row.ok = true;
    if (live_sites != 0) {
      // Merge sites that name the same library frames, largest first.
      const std::vector<std::string> names = NameSites(audit::g_site_copy, live_sites);
      for (size_t i = 0; i < live_sites; ++i) {
        bool merged = false;
        for (auto& site : row.sites) {
          if (site.second == names[i]) {
            site.first += audit::g_site_copy[i].bytes;
            merged = true;
            break;
          }
        }
        if (!merged) row.sites.push_back({audit::g_site_copy[i].bytes, names[i]});
      }
      std::sort(row.sites.begin(), row.sites.end(),
                [](const auto& a, const auto& b) { return a.first > b.first; });
    }
    if (live_blocks != 0 && live_sites != 0) {
      // Role per site from its full chain; blocks inherit their site's role.
      const std::vector<std::string> chains = NameSites(audit::g_site_copy, live_sites, 12);
      std::vector<std::string> by_index(audit::kSites + 1);
      for (size_t i = 0; i < live_sites; ++i) by_index[audit::g_site_copy[i].index] = chains[i];
      for (size_t i = 0; i < live_blocks; ++i) {
        const audit::LiveBlock& b = audit::g_block_copy[i];
        const std::string& chain = by_index[b.site];
        row.blocks.push_back({ClassifyChain(scheme, chain), ShortChain(chain, 3), b.bytes, b.count, b.granted});
      }
      std::sort(row.blocks.begin(), row.blocks.end(), [](const BlockGroup& a, const BlockGroup& b) {
        return a.bytes * a.count > b.bytes * b.count;
      });
    }
    if (row.destroyed.live_requested != row.baseline_requested) {
      audit::LiveSize sizes[32];
      const size_t n = audit::LiveFromRow(audit::g_row, sizes, 32);
      std::fprintf(stderr, "  left live by %s at %zu:", SchemeName(scheme), capacity);
      for (size_t i = 0; i < n; ++i) {
        std::fprintf(stderr, " %zux%zu", sizes[i].count, sizes[i].bytes);
      }
      std::fprintf(stderr, "\n");
    }
  } catch (const std::exception& e) {
    row.error = e.what();
  }
  return row;
}

std::string Json(const Row& r) {
  std::ostringstream o;
  auto phase = [&](const char* name, const Phase& p) {
    o << ",\"" << name << "\":{\"live_requested\":"
      << p.heap.live_requested - r.baseline_requested
      << ",\"live_granted\":" << p.heap.live_granted - r.baseline_granted
      << ",\"live_blocks\":" << p.heap.live_blocks
      << ",\"peak_requested\":" << p.heap.peak_requested - r.baseline_requested
      << ",\"peak_granted\":" << p.heap.peak_granted - r.baseline_granted
      << ",\"harness_live_requested\":"
      << (p.all.live_requested - r.baseline_all_requested) - (p.heap.live_requested - r.baseline_requested)
      << ",\"all_peak_requested\":" << p.all.peak_requested - r.baseline_all_requested
      << ",\"allocations\":" << p.heap.allocations << ",\"rss\":" << p.status.rss
      // Without a reset, VmHWM is the process's peak since exec, not this row's.
      << ",\"hwm\":" << (r.hwm_reset ? std::to_string(p.status.hwm) : std::string("null"))
      << ",\"threads\":" << p.status.threads - r.baseline_threads
      << ",\"seconds\":" << p.seconds << "}";
  };
  o << "{\"scheme\":\"" << SchemeName(r.scheme) << "\",\"capacity\":" << r.capacity
    << ",\"key_bytes\":" << r.key_bytes << ",\"value_bytes\":" << r.value_bytes
    << ",\"ok\":" << (r.ok ? "true" : "false");
  if (!r.ok) {
    o << ",\"error\":\"" << r.error << "\"}";
    return o.str();
  }
  o << ",\"actual_capacity\":" << r.actual_capacity << ",\"modeled\":" << r.modeled
    << ",\"reserved\":" << r.reserved
    << ",\"planned_threads\":" << r.planned_threads << ",\"components\":[";
  for (size_t i = 0; i < r.components.size(); ++i) {
    o << (i ? "," : "") << "{\"component\":\"" << r.components[i].component
      << "\",\"bytes\":" << r.components[i].requested_bytes << ",\"coverage\":\""
      << api::MemoryCoverageName(r.components[i].coverage) << "\"}";
  }
  o << "],\"choices\":{";
  for (size_t i = 0; i < r.choices.size(); ++i) {
    std::string value;
    for (char c : r.choices[i].second) value += (c == '"' || c == '\\') ? '\'' : c;
    o << (i ? "," : "") << "\"" << r.choices[i].first << "\":\"" << value << "\"";
  }
  o << "}";
  phase("constructed", r.constructed);
  phase("filled", r.filled);
  phase("steady", r.steady);
  o << ",\"accesses\":" << r.accesses << ",\"leaked_requested\":"
    << r.destroyed.live_requested - r.baseline_requested;
  if (!r.sites.empty()) {
    o << ",\"sites\":[";
    for (size_t i = 0; i < r.sites.size(); ++i) {
      std::string where;
      for (char c : r.sites[i].second) where += c == '"' ? '\'' : c;
      o << (i ? "," : "") << "{\"bytes\":" << r.sites[i].first << ",\"where\":\""
        << where << "\"}";
    }
    o << "]";
  }
  if (!r.blocks.empty()) {
    o << ",\"blocks\":[";
    for (size_t i = 0; i < r.blocks.size(); ++i) {
      std::string where;
      for (char c : r.blocks[i].where) where += c == '"' ? '\'' : c;
      o << (i ? "," : "") << "{\"role\":\"" << r.blocks[i].role << "\",\"where\":\"" << where
        << "\",\"bytes\":" << r.blocks[i].bytes << ",\"count\":" << r.blocks[i].count
        << ",\"granted\":" << r.blocks[i].granted << "}";
    }
    o << "]";
  }
  o << "}";
  return o.str();
}

// A whole unsigned number in `base` (0: decimal, 0x hex or 0 octal): it must
// start with a digit and nothing may follow it.
uint64_t ParseCount(const std::string& text, int base) {
  size_t used = 0;
  if (text.empty() || !std::isdigit(static_cast<unsigned char>(text[0])))
    throw std::invalid_argument("expected an unsigned integer, not '" + text + "'");
  const unsigned long long value = std::stoull(text, &used, base);
  if (used != text.size())
    throw std::invalid_argument("expected an unsigned integer, not '" + text + "'");
  return value;
}

std::vector<size_t> ParseList(const std::string& text) {
  std::vector<size_t> out;
  std::stringstream in(text);
  std::string item;
  while (std::getline(in, item, ',')) out.push_back(ParseCount(item, 0));
  return out;
}

double MiB(size_t b) { return double(b) / (1024.0 * 1024.0); }

}  // namespace

int main(int argc, char** argv) {
  {
    // The unwinder's first call allocates; make it before any capture.
    void* frames[4];
    (void)backtrace(frames, 4);
  }
  std::vector<size_t> capacities = {size_t{1} << 16, size_t{1} << 20};
  std::vector<std::pair<size_t, size_t>> shapes = {{8, 48}};
  std::vector<api::Scheme> schemes = {api::Scheme::kHierarchicalIncremental,
                                      api::Scheme::kHierarchicalSynchronous,
                                      api::Scheme::kTree};
  unsigned cores = bs::HostPhysicalCores();
  double access_factor = 2.0;
  const auto usage = [&] {
    std::fprintf(stderr,
                 "usage: %s [--capacities LIST] [--shapes k:v,...] "
                 "[--schemes incremental,synchronous,tree] [--cores N] "
                 "[--accesses FACTOR] [--sites]\n",
                 argv[0]);
  };
  // A malformed argument is a usage error (exit 2), never std::terminate.
  try {
  for (int i = 1; i < argc; ++i) {
    const std::string arg = argv[i];
    auto next = [&]() -> std::string {
      if (i + 1 >= argc) throw std::invalid_argument(arg + " needs a value");
      return argv[++i];
    };
    if (arg == "--capacities") {
      capacities = ParseList(next());
    } else if (arg == "--shapes") {
      shapes.clear();
      std::stringstream in(next());
      std::string item;
      while (std::getline(in, item, ',')) {
        const size_t colon = item.find(':');
        if (colon == std::string::npos)
          throw std::invalid_argument("--shapes entries are key:value, not '" + item + "'");
        shapes.push_back({ParseCount(item.substr(0, colon), 10),
                          ParseCount(item.substr(colon + 1), 10)});
      }
    } else if (arg == "--schemes") {
      schemes.clear();
      std::stringstream in(next());
      std::string item;
      while (std::getline(in, item, ',')) {
        if (item == "incremental") schemes.push_back(api::Scheme::kHierarchicalIncremental);
        else if (item == "synchronous") schemes.push_back(api::Scheme::kHierarchicalSynchronous);
        else if (item == "tree") schemes.push_back(api::Scheme::kTree);
        else throw std::invalid_argument("unknown scheme " + item);
      }
    } else if (arg == "--cores") {
      const uint64_t n = ParseCount(next(), 10);
      if (n > UINT_MAX) throw std::invalid_argument("--cores is out of range");
      cores = static_cast<unsigned>(n);
    } else if (arg == "--accesses") {
      const std::string text = next();
      size_t used = 0;
      access_factor = std::stod(text, &used);
      if (used != text.size() || !std::isfinite(access_factor) || access_factor < 0)
        throw std::invalid_argument("--accesses needs a nonnegative factor, not '" + text + "'");
    } else if (arg == "--sites") {
      g_sites_mode = true;
    } else if (arg == "--steady-sites") {
      g_steady_sites = true;
    } else {
      usage();
      return 2;
    }
  }
  } catch (const std::exception& e) {
    std::fprintf(stderr, "%s: %s\n", argv[0], e.what());
    usage();
    return 2;
  }
  // cover = the plan's reserved bytes over the live heap after the fill.
  std::fprintf(stderr,
               "%-24s %7s %9s %9s %9s %9s %9s %9s %9s %8s %6s %s\n", "scheme",
               "k:v", "capacity", "modeled", "reserved", "built", "filled",
               "fillpeak", "steady", "cover", "allocs", "leak");
  // Rows that failed (an exception, a lost key) or left bytes live after
  // destruction: the audit still runs every row, then exits 1.
  size_t bad_rows = 0;
  for (const auto& shape : shapes) {
    for (size_t capacity : capacities) {
      for (api::Scheme scheme : schemes) {
        const Row r =
            RunRow(scheme, capacity, shape.first, shape.second, cores, access_factor);
        std::printf("AUDIT_ROW %s\n", Json(r).c_str());
        std::fflush(stdout);
        if (!r.ok) {
          ++bad_rows;
          std::fprintf(stderr, "%-24s %2zu:%-4zu %9zu  failed: %s\n",
                       SchemeName(scheme), shape.first, shape.second, capacity,
                       r.error.c_str());
          continue;
        }
        if (r.destroyed.live_requested != r.baseline_requested) ++bad_rows;
        const size_t filled = r.filled.heap.live_requested - r.baseline_requested;
        std::fprintf(
            stderr,
            "%-24s %2zu:%-4zu %9zu %8.1fM %8.1fM %8.1fM %8.1fM %8.1fM %8.1fM "
            "%7.2f%% %6" PRIu64 " %zu\n",
            SchemeName(scheme), shape.first, shape.second, capacity,
            MiB(r.modeled), MiB(r.reserved),
            MiB(r.constructed.heap.live_requested - r.baseline_requested),
            MiB(filled),
            MiB(r.filled.heap.peak_requested - r.baseline_requested),
            MiB(r.steady.heap.live_requested - r.baseline_requested),
            filled == 0 ? 0.0 : 100.0 * double(r.reserved) / double(filled),
            r.steady.heap.allocations,
            r.destroyed.live_requested - r.baseline_requested);
        if (!r.hwm_reset) {
          std::fprintf(stderr, "    peak RSS not reset (/proc/self/clear_refs refused): hwm is null\n");
        }
        for (size_t i = 0; i < r.sites.size() && i < 14; ++i) {
          std::fprintf(stderr, "    %10.3f MiB  %s\n", MiB(r.sites[i].first),
                       r.sites[i].second.c_str());
        }
      }
    }
  }
  if (bad_rows != 0) {
    std::fprintf(stderr, "%zu row(s) failed or left bytes live after destruction\n", bad_rows);
    return 1;
  }
  return 0;
}
