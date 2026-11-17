#!/usr/bin/env python3
"""Generate public mock block deltas and independent py-trie state-root goldens.

Use the versions in requirements.txt. No C++ implementation or network is used.
Write stdout to mock_blocks.txt and review the diff. These are final-state
mutations and artificial block IDs, not executed Ethereum transactions/headers.
"""
from copy import deepcopy
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


def address(value):
    return value.to_bytes(20, "big")


def block_id(name):
    return keccak(("ethereum-mpt-mock-block-v1:" + name).encode("ascii"))


def upsert(account, nonce, balance, changes=(), *, reset=False, code=b""):
    return (account, nonce, balance, keccak(code), reset, list(changes))


def state_root(state):
    accounts = HexaryTrie({})
    for account, (nonce, balance, code_hash, slots) in sorted(state.items()):
        storage = HexaryTrie({})
        for slot, value in sorted(slots.items()):
            if not value:
                raise RuntimeError("zero storage must be absent")
            storage[keccak(word(slot))] = rlp.encode(value)
        accounts[keccak(address(account))] = rlp.encode(
            [nonce, balance, storage.root_hash, code_hash])
    return accounts.root_hash


states = {}
numbers = {}


def emit(name, parent, upserts=(), deletions=()):
    state = deepcopy(states[parent]) if parent is not None else {}
    number = numbers[parent] + 1 if parent is not None else 0
    addresses = [item[0] for item in upserts] + list(deletions)
    if len(addresses) != len(set(addresses)):
        raise RuntimeError("duplicate/overlapping account mutations")
    for account in deletions:
        state.pop(account, None)
    for account, nonce, balance, code_hash, reset, changes in upserts:
        if len(changes) != len({slot for slot, _ in changes}):
            raise RuntimeError("duplicate storage changes")
        slots = {} if reset or account not in state else state[account][3]
        for slot, value in changes:
            if value:
                slots[slot] = value
            else:
                slots.pop(slot, None)
        state[account] = (nonce, balance, code_hash, slots)
    root = state_root(state)
    states[name] = state
    numbers[name] = number
    print("\n#", name)
    print("block", block_id(name).hex(),
          block_id(parent).hex() if parent is not None else bytes(32).hex(),
          number, root.hex())
    for account, nonce, balance, code_hash, reset, changes in upserts:
        print("upsert", address(account).hex(), nonce, word(balance).hex(),
              code_hash.hex(), int(reset))
        for slot, value in changes:
            print("storage", word(slot).hex(), word(value).hex())
        print("endupsert")
    for account in deletions:
        print("delete", address(account).hex())
    print("endblock")


print("# Ethereum py-trie 3.1.0; rlp 5.0.0; eth-hash 0.7.1; pycryptodome 3.24.1")
print("# Deterministic public post-state deltas; block IDs are fixture identifiers.")
print("mock_blocks_v1")
emit("genesis", None, [
    upsert(1, 1, 1000, [(1, 128), (2, 256)], reset=True),
    upsert(2, 2, 2000, [(1, 128), (2, 256)], reset=True),
    upsert(3, 3, 3000, reset=True, code=b"initial fixture bytecode"),
])
emit("replace", "genesis", [
    upsert(1, 2, 9999, [(1, 512), (2, 0), (3, 1)], code=b"replacement bytecode"),
    upsert(3, (1 << 64) - 1, (1 << 256) - 1, code=b"maximum fields bytecode"),
])
emit("delete", "replace", deletions=[1, 3])
emit("recreate", "delete", [
    upsert(1, 0, 5, [(9, 7)], reset=True),
    upsert(2, 4, 2001, [(1, 0)]),
])
emit("reset", "recreate", [upsert(2, 5, 2002, [(7, 65535)], reset=True)])
emit("fork_replace", "replace", [
    upsert(1, 3, 42, [(3, 0), (4, 900)], code=b"fork bytecode"),
], deletions=[3])
emit("fork_recreate", "fork_replace", [
    upsert(3, 1, 2, [(1, 512), (4, 900)], reset=True),
], deletions=[2])
emit("empty", "reset", deletions=[1, 2])
