// Runs the reference-module test suites and compares roots and proofs with the
// committed py-trie golden fixtures.

#include "fixture.hpp"

#include <algorithm>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>

void run_codec_tests();
void run_trie_tests();
void run_packing_tests();
void run_mock_chain_tests();
void test_trie_updates();
void test_canonical_updates();

namespace {
using namespace ethereum_mpt;

void require(bool ok, const std::string& message) {
  if (!ok) throw std::runtime_error(message);
}

Hash read_hash(const std::string& text) {
  const auto bytes = from_hex(text);
  require(bytes.size() == 32, "fixture hash width");
  Hash hash{};
  std::copy(bytes.begin(), bytes.end(), hash.begin());
  return hash;
}

void golden_fixtures() {
  std::ifstream input(ETHEREUM_MPT_FIXTURES);
  require(bool(input), "cannot read oracle fixtures");
  std::string line, name;
  TrieKind role = TrieKind::storage;
  std::vector<Entry> entries;
  Trie trie{TrieKind::storage, nullptr};
  Trie updated{TrieKind::storage, nullptr};
  Hash root{}, key{};
  std::optional<Bytes> expected;
  Proof proof;
  size_t cases = 0, queries = 0;
  bool in_case = false, have_root = false, in_query = false;
  while (std::getline(input, line)) {
    if (line.empty() || line[0] == '#') continue;
    std::istringstream row(line);
    std::string command, a, b;
    row >> command >> a >> b;
    if (command == "case") {
      require(!in_case && !in_query, "unclosed fixture case");
      in_case = true;
      have_root = false;
      name = a;
      require(b == "account" || b == "storage", "fixture role");
      role = b == "account" ? TrieKind::account : TrieKind::storage;
      entries.clear();
      ++cases;
    } else if (command == "entry") {
      require(in_case && !have_root, "fixture entry outside build phase");
      entries.push_back({read_hash(a), from_hex(b)});
    } else if (command == "root") {
      require(in_case && !have_root, "unexpected fixture root");
      have_root = true;
      root = read_hash(a);
      trie = build_trie(role, entries);
      require(trie.root_hash() == root, name + ": root differs from py-trie");
      updated = {role, nullptr};
      for (const auto& entry : entries)
        updated = update_trie(updated, {{entry.key, entry.value}});
      require(updated.root_hash() == root, name + ": incremental root differs from py-trie");
    } else if (command == "query") {
      require(in_case && have_root && !in_query, "unexpected fixture query");
      in_query = true;
      key = read_hash(a);
      expected = b == "-" ? std::nullopt : std::optional<Bytes>(from_hex(b));
      proof.clear();
    } else if (command == "node") {
      require(in_query, "fixture proof node outside query");
      proof.push_back(from_hex(a));
    } else if (command == "endquery") {
      require(in_query, "unexpected end of fixture query");
      in_query = false;
      require(verify_proof(role, root, key, proof) == expected,
              name + ": verification of external proof/value failed");
      require(prove(trie, key) == proof, name + ": proof bytes differ from py-trie");
      require(prove(updated, key) == proof, name + ": incremental proof differs from py-trie");
      ++queries;
    } else {
      require(command == "end", "unknown fixture command: " + command);
      require(in_case && have_root && !in_query, "unclosed fixture query");
      in_case = false;
    }
  }
  require(!input.bad() && !in_case && !in_query && cases == 11 && queries == 35,
          "truncated oracle fixture suite");
  std::cout << "Independent py-trie fixtures: " << cases << " roots, " << queries
            << " proofs matched byte-for-byte\n";
}

void fixture_integration() {
  const auto fixture = make_fixture();
  for (const auto profile : {TierProfile{}, TierProfile{0, 0}, TierProfile{3, 2},
                             TierProfile{65, 65}}) {
    const auto packed = pack_snapshot(fixture, profile);
    validate_packed_snapshot(packed);
    require(packed.state_root == fixture.accounts.root_hash(), "packing changed root");
    const auto stats = packed.total_stats();
    require(stats.record_bytes == stats.canonical_bytes + 8 * stats.records +
            12 * (stats.ordinary_links + stats.account_leaves), "packing byte bill");
    require(stats.real_pages * page_bytes < 2 * stats.record_bytes +
            stats.packing_runs * page_bytes, "next-fit bound");
  }
}
}  // namespace

int main() {
  try {
    run_codec_tests();
    run_trie_tests();
    run_packing_tests();
    run_mock_chain_tests();
    test_trie_updates();
    test_canonical_updates();
    golden_fixtures();
    fixture_integration();
    std::cout << "ethereum_mpt_reference_test passed\n";
  } catch (const std::exception& error) {
    std::cerr << "ethereum_mpt_reference_test: " << error.what() << '\n';
    return 1;
  }
}
