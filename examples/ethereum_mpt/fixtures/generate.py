#!/usr/bin/env python3
"""Regenerate public golden fixtures with Ethereum py-trie, never the C++ codec.

Install requirements.txt in a separate environment. No network is used here.
Writes to stdout; review the diff before replacing oracle_vectors.txt.
"""
from importlib.metadata import version

import rlp
from eth_hash.auto import keccak
from trie import HexaryTrie


for package, expected in (("trie", "3.1.0"), ("rlp", "5.0.0"),
                          ("eth-hash", "0.7.1"), ("pycryptodome", "3.24.1")):
    if version(package) != expected:
        raise RuntimeError(f"expected {package}=={expected}")


def word(value):
    return value.to_bytes(32, "big")


def scalar(value):
    return rlp.encode(value.to_bytes((value.bit_length() + 7) // 8, "big"))


def emit(name, role, entries, queries):
    trie = HexaryTrie({})
    print("case", name, role)
    for key, value in entries:
        trie[key] = value
        print("entry", key.hex(), value.hex())
    print("root", trie.root_hash.hex())
    for key in queries:
        expected = trie[key]
        proof = trie.get_proof(key)
        # py-trie can include inline nodes. The wire fixture uses the minimal
        # root + hashed-descendants convention of Geth's proof construction.
        encoded = [rlp.encode(node) for node in proof]
        encoded = [node for i, node in enumerate(encoded) if i == 0 or len(node) >= 32]
        if entries:
            recovered = HexaryTrie.get_from_proof(
                trie.root_hash, key, tuple(rlp.decode(node) for node in encoded))
            if recovered != expected:
                raise RuntimeError("reference proof disagrees with reference value")
        print("query", key.hex(), expected.hex() or "-")
        for node in encoded:
            print("node", node.hex())
        print("endquery")
    print("end")


print("# Ethereum py-trie 3.1.0; rlp 5.0.0; eth-hash 0.7.1; pycryptodome 3.24.1")
emit("empty_storage", "storage", [], [word(0)])
emit("empty_account", "account", [], [keccak(bytes(20))])
storage = [(keccak(word(i)), scalar(v)) for i, v in enumerate(
    (1, 127, 128, 255, 256, (1 << 256) - 1))]
emit("secure_storage", "storage", storage,
     [key for key, _ in storage] + [keccak(word(99))])
storage_trie = HexaryTrie({})
for key, value in storage:
    storage_trie[key] = value
accounts = []
for i in range(1, 5):
    account = [i, (1 << 256) - 1 if i == 4 else i * 1000,
               storage_trie.root_hash if i % 2 else HexaryTrie({}).root_hash,
               keccak(b"fixture bytecode") if i == 3 else keccak(b"")]
    # RLP's integer serializer uses the canonical shortest representation.
    accounts.append((keccak(i.to_bytes(20, "big")), rlp.encode(account)))
emit("secure_accounts", "account", accounts,
     [key for key, _ in accounts] + [keccak((99).to_bytes(20, "big"))])
emit("single_account", "account", accounts[:1],
     [accounts[0][0], keccak(bytes(20))])

# Structural vectors deliberately use raw paths: no infeasible Keccak preimage
# search. Divergence near depth 64 exercises embedded leaves and path mismatch.
inline_entries = [(word(i), scalar(i + 1)) for i in (0, 1, 15, 16)]
emit("inline_storage", "storage", inline_entries, [word(i) for i in (0, 1, 2, 16, 256)])

# A zero path with one sibling at each nibble depth forces 64 branches followed
# by an empty-suffix leaf: 65 logical nodes, including inline final descendants.
deep = [(word(0), scalar(1))]
for depth in range(64):
    deep.append((word(1 << (4 * (63 - depth))), scalar(depth + 2)))
emit("depth_64_leaf", "storage", deep, [word(0), word(2)])

# Leaves immediately under depth-63 branches cross the 31/32-byte embedding
# boundary as the scalar width increases. All are canonical storage scalars.
for width in (27, 28, 29, 32):
    entries = [(word(0), scalar(1 << (8 * (width - 1)))), (word(1), scalar(1))]
    emit(f"child_width_{width}", "storage", entries, [word(0), word(1), word(2)])
