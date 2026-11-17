"""Per-boot attestation of a protected (tdx/snp) campaign: capture, launch gate, verdict.

`attest` runs as root once per boot, before `run`. It fetches one report
through configfs-tsm whose report data is the SHA-512 of the binding (runtime,
host, boot and environment class) and keeps the report and its record under
campaign/attestations/. `run` launches a tdx or snp campaign only when the live
detection shows that runtime and this boot's capture exists; the environment
record then references the capture by hash. `verdict` attaches an offline
verifier's result, and `reduce` marks a row protected_verified only through a
verified verdict with no failed one beside it.
"""
import hashlib
import os
from pathlib import Path
import time

from .codec import decode, identity, load_json, plain, require
from .doctor import file_hash, inspect
from .schema import Environment
from .store import atomic_bytes, atomic_json
from .tee import (KERNEL_NAMES, PROVIDERS, TEE_RUNTIMES, AttestationBinding, AttestationCapture,
                  AttestationFile, AttestationVerdict, fetch_report, report_data, report_facts,
                  runtime_contract)


def binding(environment):
    require(environment["runtime"] in TEE_RUNTIMES, "only a tdx or snp environment is attested")
    require(environment["boot_identity"] is not None, "attestation needs the boot identity")
    return AttestationBinding(1, environment["runtime"], environment["host_identity"],
                              environment["boot_identity"], environment["environment_class"])


def capture_path(bound):
    """The capture's campaign-relative path, named by its binding."""
    return "attestations/" + identity("attestation-binding-v1", bound) + ".json"


def _file(campaign, relative):
    path = Path(campaign) / relative
    return AttestationFile(relative, file_hash(path), path.stat().st_size)


def _check_file(campaign, item):
    path = Path(campaign) / item.path
    require(not path.is_symlink() and path.stat().st_size == item.bytes and file_hash(path) == item.sha256,
            f"attestation file changed: {item.path}")


def load_capture(campaign, relative, sha256=None):
    """A capture record with its report files re-hashed; `sha256` pins the record."""
    path = Path(campaign) / relative
    require(sha256 is None or file_hash(path) == sha256, f"attestation capture changed: {relative}")
    capture = decode(AttestationCapture, load_json(path))
    require(capture_path(capture.binding) == relative, "capture stored under another binding's name")
    for item in (capture.report, capture.auxiliary):
        if item is not None:
            _check_file(campaign, item)
    return capture


def _give_to_owner(campaign, paths):
    """Run as root, hand what attest wrote to the campaign's owner, so the
    unprivileged service reads it and the operator can add verdicts."""
    if not hasattr(os, "geteuid") or os.geteuid() != 0:
        return
    owner = Path(campaign).stat()
    for path in paths:
        os.chown(path, owner.st_uid, owner.st_gid)


def attest_campaign(campaign, entry=None):
    """Fetch this boot's report for the campaign's class, or return the existing one."""
    from .campaign import read_plan
    from .resolution import read_resolution
    campaign = Path(campaign).resolve()
    plan = read_plan(campaign)
    resolution = read_resolution(campaign, plan)
    runtime = plan["campaign"]["execution"]["runtime"]
    require(runtime in TEE_RUNTIMES, "attest needs a campaign whose execution.runtime is tdx or snp")
    require(not resolution["build"]["synthetic"], "a synthetic build is never attested")
    worker = (campaign / "build" / "worker").resolve(strict=True)
    require("sha256-" + file_hash(worker) == resolution["build"]["worker_sha256"], "frozen worker binary changed")
    environment = inspect(worker, runtime, library_header=resolution["build"]["library_header_sha256"])
    detection = decode(Environment, environment).tee
    reasons = runtime_contract(runtime, detection)
    require(not reasons, "this host does not show the campaign's runtime: " + ", ".join(reasons))
    require(detection.kernel_names(runtime), f"a capture needs the boot log to name {KERNEL_NAMES[runtime]}; "
            "run attest as root, where the kernel log is readable")
    bound = binding(environment)
    relative = capture_path(bound)
    if not (campaign / relative).exists():
        data = report_data(bound)
        provider, blob, auxiliary, generation = fetch_report(data, entry)
        require(provider == PROVIDERS[runtime], f"configfs-tsm provider {provider!r} is not {PROVIDERS[runtime]!r}")
        facts = report_facts(runtime, blob, data)
        require(facts.report_data_matches is not False, "the report does not carry the bound report data")
        stem = relative.removesuffix(".json")
        files = []
        for suffix, content in ((".report.bin", blob), (".aux.bin", auxiliary)):
            if content is not None:
                atomic_bytes(campaign / (stem + suffix), content)
            files.append(None if content is None else _file(campaign, stem + suffix))
        capture = AttestationCapture(1, bound, data.hex(), provider, generation, files[0], files[1], facts,
                                     detection, time.time_ns())
        capture.validate()
        atomic_json(campaign / relative, capture, immutable=True)
        _give_to_owner(campaign, [campaign / "attestations", campaign / relative,
                                  *(campaign / item.path for item in files if item is not None)])
        status = "captured"
    else:
        status = "existing"
    capture = load_capture(campaign, relative)
    return {"status": status, "capture": relative, "capture_sha256": file_hash(campaign / relative),
            "binding": plain(bound), "facts": plain(capture.facts),
            "note": "Unverified until an offline verifier's result is recorded with `verdict`."}


def launch_gate(campaign, execution, environment):
    """The runtime gate before a native, tdx or snp launch.

    The label must match what the guest kernel shows (doctor's `runtime:`
    evidence), and a tdx or snp run also needs this boot's capture for its
    class. A debuggable guest cannot serve a campaign that requires protection.
    """
    runtime = execution["runtime"]
    reasons = [reason for reason in environment["missing_evidence"] if reason.startswith("runtime:")]
    reference = None
    if runtime in TEE_RUNTIMES and not reasons:
        if environment["boot_identity"] is None:
            reasons.append("attestation:boot_identity_unknown")
        else:
            relative = capture_path(binding(environment))
            if not (Path(campaign) / relative).exists():
                reasons.append("attestation:no_capture_this_boot")
            else:
                try:
                    capture = load_capture(campaign, relative)
                    reference = _file(campaign, relative)
                    if capture.facts.debug and execution["require_protected"]:
                        reasons.append("attestation:debug_guest")
                except (OSError, ValueError):
                    reasons.append("attestation:capture_invalid")
    return {"status": "blocked" if reasons else "compatible", "runtime": runtime,
            "rejection_reasons": sorted(reasons),
            "attestation": None if reasons or reference is None else plain(reference)}


def record_verdict(campaign, capture, verifier, result, reference, output=None):
    """Attach an offline verifier's result to one capture, keeping its output."""
    campaign = Path(campaign).resolve()
    require(capture.startswith("attestations/") and capture.endswith(".json") and ".verdict-" not in capture,
            "name a capture record under attestations/")
    load_capture(campaign, capture)
    stem = capture.removesuffix(".json")
    kept = None
    if output is not None:
        data = Path(output).read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        relative = f"{stem}.verifier-{digest[:16]}.log"
        atomic_bytes(campaign / relative, data)
        kept = AttestationFile(relative, digest, len(data))
    verdict = AttestationVerdict(1, file_hash(campaign / capture), verifier, result, reference, kept)
    decode(AttestationVerdict, plain(verdict))
    relative = f"{stem}.verdict-{identity('attestation-verdict-v1', verdict)[-16:]}.json"
    atomic_json(campaign / relative, verdict, immutable=True)
    return {"verdict": relative, **plain(verdict)}


def protection(campaign, environment):
    """(protected_verified, verification_reference) for one environment's rows.

    Verified needs a tdx or snp environment whose capture still hashes as
    recorded, at least one verified verdict for it and no failed one.
    """
    reference = environment.get("attestation")
    if environment["runtime"] not in TEE_RUNTIMES or reference is None:
        return False, None
    campaign = Path(campaign)
    try:
        load_capture(campaign, reference["path"], reference["sha256"])
    except (OSError, ValueError):
        return False, None
    verdicts = []
    stem = Path(reference["path"]).name.removesuffix(".json")
    for path in sorted((campaign / "attestations").glob(stem + ".verdict-*.json")):
        try:
            verdict = decode(AttestationVerdict, load_json(path))
            if verdict.output is not None:
                _check_file(campaign, verdict.output)
        except (OSError, ValueError):
            return False, None  # a verdict that no longer checks out may have been a failure
        if verdict.capture_sha256 == reference["sha256"]:
            verdicts.append((path, verdict))
    if not verdicts or any(verdict.result == "failed" for _, verdict in verdicts):
        return False, None
    path, verdict = next((p, v) for p, v in verdicts if v.result == "verified")
    return True, f"{path.relative_to(campaign).as_posix()} ({verdict.verifier}: {verdict.reference})"
