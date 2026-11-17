#!/usr/bin/env python3
"""Check retained-window and legacy restart through both real ORAM update demos."""

from pathlib import Path
import subprocess
import sys
import tempfile


def require(condition, message):
    if not condition:
        raise AssertionError(message)


# A guard against a hung demo, not a speed bound: with assertions enabled (a
# build without NDEBUG) one demo run takes about ten times as long as in Release.
INVOCATION_TIMEOUT_SECONDS = 300


def invoke(executable, *arguments):
    return subprocess.run([str(executable), *map(str, arguments)],
                          text=True, capture_output=True, timeout=INVOCATION_TIMEOUT_SECONDS)


def fields(line):
    return dict(item.split("=", 1) for item in line.split())


def fixture_headers():
    fixture = Path(__file__).with_name("fixtures") / "mock_blocks.txt"
    headers = []
    for line in fixture.read_text(encoding="utf-8").splitlines():
        if line.startswith("block "):
            _, block_id, parent_id, number, root = line.split()
            headers.append(dict(id="0x" + block_id, parent="0x" + parent_id,
                                block=number, root="0x" + root))
    require(len(headers) == 8, "expected eight trusted fixture block headers")
    return headers


def successful(executable, headers, first, last, restored, *arguments, retained=None,
               existing=None):
    if retained is None:
        retained = first + 1
    if existing is None:
        existing = set(range(first - retained + 1, first + 1))
    else:
        existing = set(existing)
    result = invoke(executable, *arguments)
    require(result.returncode == 0,
            f"checkpoint demo failed: {arguments!r}\n{result.stderr}")
    require(not result.stderr, "successful checkpoint demo wrote to stderr")
    lines = result.stdout.splitlines()
    initial = [fields(line) for line in lines if line.startswith("initial_fixture_index=")]
    require(initial == [dict(initial_fixture_index=str(first), restored=str(int(restored)),
                             retained=str(retained))],
            "restart must preserve every saved retained root")
    updates = [fields(line) for line in lines if line.startswith("block=")]
    require(len(updates) == last - first, "restart must apply only subsequent fixture deltas")
    for index, update in enumerate(updates, first + 1):
        existing.add(index)
        expected = headers[index]
        for key in ("id", "block", "root"):
            require(update[key] == expected[key], f"fixture {index} {key} mismatch")
        require(update["retained"] == str(len(existing)),
                "restart must retain saved history and newly published roots")
        require(update["reorg"] == str(int(expected["parent"] != headers[index - 1]["id"])),
                "continuation must preserve the fixture's fork transitions")
    require(f"Verified fixture indices {first} through {last} and retained client proof frames"
            in lines, "checkpoint head and every continuation must finish proof verification")
    return updates


def rejected(executable, *arguments, message=None):
    result = invoke(executable, *arguments)
    require(result.returncode != 0 and "ethereum_mpt_updates:" in result.stderr,
            f"invalid checkpoint invocation succeeded or lacked an error: {arguments!r}")
    require(not result.stdout, "invalid restart must fail before loading maps or publishing")
    if message is not None:
        require(message in result.stderr, f"missing diagnostic: {message}\n{result.stderr}")


def main(replacement, incremental, fixture_writer):
    headers = fixture_headers()
    with tempfile.TemporaryDirectory(prefix="mpt checkpoint cli ") as directory:
        root = Path(directory)
        first = root / "replacement head one.checkpoint"
        successful(replacement, headers, 0, 1, False,
                   "--through-index", 1, "--checkpoint-out", first)
        first_bytes = first.read_bytes()
        require(first_bytes, "fresh run must write a checkpoint")

        resumed = root / "incremental resumed final.checkpoint"
        updates = successful(incremental, headers, 1, 7, True,
                             "--checkpoint-in", first, "--checkpoint-out", resumed)
        require(sum(update["reorg"] == "1" for update in updates) == 2,
                "restart from index one must retain both fixture fork transitions")
        require(first.read_bytes() == first_bytes, "separate output must preserve the input checkpoint")

        # Exercise the opposite backend transition and atomic same-path replacement.
        in_place = root / "incremental head one then replacement.checkpoint"
        successful(incremental, headers, 0, 1, False,
                   "--through-index", 1, "--checkpoint-out", in_place)
        require(in_place.read_bytes() == first_bytes,
                "checkpoint encoding must not depend on the ORAM publication policy")
        successful(replacement, headers, 1, 7, True,
                   "--checkpoint-in", in_place, "--checkpoint-out", in_place)
        final_bytes = resumed.read_bytes()
        require(in_place.read_bytes() == final_bytes and final_bytes != first_bytes,
                "same input/output path must advance to the identical final checkpoint")

        uninterrupted = root / "uninterrupted final.checkpoint"
        successful(replacement, headers, 0, 7, False, "--checkpoint-out", uninterrupted)
        require(uninterrupted.read_bytes() == final_bytes,
                "resumed and uninterrupted runs must produce byte-identical checkpoints")

        # A terminal checkpoint still verifies its head, without replaying deltas.
        successful(incremental, headers, 7, 7, True,
                   "--checkpoint-in", in_place, "--checkpoint-out", in_place)
        require(in_place.read_bytes() == final_bytes,
                "terminal restart must preserve the canonical checkpoint bytes")

        # Restarting at index two must keep index one's retained state so the next fork remains possible.
        second = root / "head two with retained ancestors.checkpoint"
        successful(replacement, headers, 1, 2, True,
                   "--checkpoint-in", first, "--through-index", 2, "--checkpoint-out", second)
        second_bytes = second.read_bytes()
        from_second = root / "resumed head two.checkpoint"
        successful(incremental, headers, 2, 7, True,
                   "--checkpoint-in", second, "--checkpoint-out", from_second)
        require(from_second.read_bytes() == final_bytes and second.read_bytes() == second_bytes,
                "retained ancestors must allow continuation through both forks")

        # Resume from the abandoned branch immediately before the first fork.
        fourth = root / "head four with both future fork ancestors.checkpoint"
        successful(incremental, headers, 2, 4, True, "--checkpoint-in", second,
                   "--through-index", 4, "--checkpoint-out", fourth)
        successful(replacement, headers, 4, 7, True,
                   "--checkpoint-in", fourth, "--checkpoint-out", fourth)
        require(fourth.read_bytes() == final_bytes,
                "restart must preserve abandoned-branch state for the later reorg")

        # Frozen output from the original v1 encoder at fixture index four.
        # No external hash package is needed to test backward compatibility.
        legacy = root / "legacy single head four.checkpoint"
        fixture = Path(__file__).with_name("fixtures") / "checkpoint_v1.hex"
        legacy_bytes = bytes.fromhex(fixture.read_text(encoding="ascii"))
        legacy.write_bytes(legacy_bytes)
        promoted = root / "promoted single head.checkpoint"
        successful(incremental, headers, 4, 4, True, "--checkpoint-in", legacy,
                   "--through-index", 4, "--checkpoint-out", promoted, retained=1)
        successful(replacement, headers, 4, 4, True, "--checkpoint-in", promoted,
                   "--through-index", 4, retained=1)
        require(legacy.read_bytes() == legacy_bytes and promoted.read_bytes() != legacy_bytes,
                "v1 input must remain intact while new saves use the history format")

        preserved = root / "preserved output.checkpoint"
        preserved.write_bytes(b"existing output must survive rejected continuation\n")
        preserved_bytes = preserved.read_bytes()
        generated = invoke(fixture_writer, "--write-cli-fixtures", root)
        require(generated.returncode == 0,
                f"could not generate checkpoint edge cases: {generated.stderr}")
        for executable in (replacement, incremental):
            rejected(executable, "--checkpoint-in", legacy, "--checkpoint-out", preserved,
                     message="unavailable ancestor")
            rejected(executable, "--checkpoint-in", legacy, "--checkpoint-out", legacy,
                     message="unavailable ancestor")
            require(preserved.read_bytes() == preserved_bytes and legacy.read_bytes() == legacy_bytes,
                    "missing legacy ancestors must be rejected before replacing either file")

            disconnected = root / "disconnected.checkpoint"
            disconnected_bytes = disconnected.read_bytes()
            rejected(executable, "--checkpoint-in", disconnected, "--checkpoint-out", preserved,
                     message="unavailable ancestor")
            rejected(executable, "--checkpoint-in", disconnected, "--checkpoint-out", disconnected,
                     message="unavailable ancestor")
            require(preserved.read_bytes() == preserved_bytes and
                    disconnected.read_bytes() == disconnected_bytes,
                    "missing intermediate ancestry must fail before any checkpoint replacement")

            # Validate every saved header, even one that is not the selected head.
            rejected(executable, "--checkpoint-in", root / "untrusted.checkpoint",
                     "--checkpoint-out", preserved, message="metadata does not match")
            require(preserved.read_bytes() == preserved_bytes,
                    "untrusted historical metadata must preserve the existing output")

            replayed = root / "replayed.checkpoint"
            successful(executable, headers, 0, 7, True,
                       "--checkpoint-in", root / "nonlast.checkpoint",
                       "--checkpoint-out", replayed, retained=8, existing=range(8))
            require(replayed.read_bytes() == final_bytes,
                    "replaying retained blocks must preserve publication order and final state")

        corrupt = root / "corrupt checkpoint"
        damaged = bytearray(first_bytes)
        damaged[len(damaged) // 2] ^= 1
        corrupt.write_bytes(damaged)
        for executable in (replacement, incremental):
            for source in (root / "missing checkpoint", corrupt):
                rejected(executable, "--checkpoint-in", source, "--checkpoint-out", preserved)
                require(preserved.read_bytes() == preserved_bytes,
                        "unreadable or corrupt input must preserve existing output")
            rejected(executable, "--checkpoint-in", first, "--through-index", 0,
                     "--checkpoint-out", preserved, message="precedes the checkpoint head")
            require(preserved.read_bytes() == preserved_bytes,
                    "backward fixture range must preserve existing output")

        invalid = (("--unknown", "1"), ("--checkpoint-in",), ("--checkpoint-out",),
                   ("--through-index",), ("--through-index", "-1"),
                   ("--through-index", "8"), ("--through-index", "1x"),
                   ("--through-index", "01"), ("--through-index", ""),
                   ("--checkpoint-in", ""), ("--checkpoint-out", ""),
                   ("--through-index", "1", "--through-index", "2"),
                   ("--checkpoint-in", first, "--checkpoint-in", first),
                   ("--checkpoint-out", preserved, "--checkpoint-out", preserved))
        for arguments in invalid:
            for executable in (replacement, incremental):
                rejected(executable, *arguments)
        require(preserved.read_bytes() == preserved_bytes,
                "argument rejection must not modify an existing checkpoint")
        for executable in (replacement, incremental):
            result = invoke(executable, "--help")
            require(result.returncode == 0 and "--checkpoint-in" in result.stdout and
                    "--checkpoint-out" in result.stdout and "--through-index" in result.stdout
                    and not result.stderr, "CLI help must describe checkpoint controls")

    print("Checkpoint CLI checks passed: cross-backend restart, forks, atomic same-path saves, "
          "retained proofs, v1 compatibility and rejected inputs")


if __name__ == "__main__":
    require(len(sys.argv) == 4,
            "usage: checkpoint_cli_test.py /path/to/replacement /path/to/incremental /path/to/checkpoint_test")
    main(sys.argv[1], sys.argv[2], sys.argv[3])
