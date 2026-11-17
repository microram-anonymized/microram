"""Local evidence capture. Exposed VM topology is not physical-host attestation, and
TEE detection is not attestation either (tee.py)."""
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import time

from .codec import decode, identity, plain, ValidationError
from .schema import ClockCheck, Environment, SharedObject
from .guest_memory import capture_guest_memory
from .preflight import memory_evidence
from .tee import detect_tee, runtime_contract
from .topology import capture_topology, topology_contract


def file_hash(path):
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _text(path):
    try:
        return Path(path).read_text().strip()
    except (OSError, UnicodeError):
        return None


# Invariant-TSC and user-mode wait flags, recorded beside the compiled ISA.
CLOCK_FLAGS = ("constant_tsc", "nonstop_tsc", "tsc_known_freq")
WAIT_FLAGS = ("monitorx", "waitpkg")


def compiled_isa(worker):
    """The worker's compiled-in extensions (`--compiled-isa`), or None if it cannot say."""
    try:
        result = subprocess.run([str(worker), "--compiled-isa"], capture_output=True, text=True, timeout=30)
        value = json.loads(result.stdout) if result.returncode == 0 else None
    except (OSError, subprocess.SubprocessError, ValueError):
        return None
    return sorted(set(value)) if isinstance(value, list) and all(type(v) is str for v in value) else None


def host_flags(read=_text):
    for line in (read("/proc/cpuinfo") or "").splitlines():
        if line.startswith("flags"):
            return set(line.split(":", 1)[1].split())
    return None


def isa_and_clock(compiled, flags, clock_source):
    """Missing evidence for a host that cannot run the binary, or whose clock is not an invariant TSC.

    An extension compiled in but not exposed (a guest may filter CPUID) makes
    the binary fault, so native runs refuse it. The clock entries are evidence
    only: the TSC is what steady_clock should read on the target.
    """
    missing = []
    if compiled is None:
        missing.append("isa:compiled_set_unknown")
    elif flags is None:
        missing.append("isa:host_flags_unknown")
    else:
        missing.extend("isa:not_exposed:" + flag for flag in compiled if flag not in flags)
    if flags is not None and not all(flag in flags for flag in CLOCK_FLAGS[:2]):
        missing.append("clock:no_invariant_tsc")
    if clock_source != "tsc":
        missing.append("clock:clocksource_not_tsc")
    return missing


# What the clock check (`worker --clock-check`) may show before the TSC counts
# as validated. The rate and slew bounds are far above what a healthy host
# shows (hundredths of a ppm of spread, about 10 ppm of NTP slew) and far below
# what a TSC rescale or a clocksource switch produces; NTP's own slew is at
# most 500 ppm. A vDSO read is tens of nanoseconds and a trapped or
# system-call read is hundreds.
CLOCK_RATE_SPREAD_PPM = 10.0
CLOCK_SLEW_PPM = 500.0
CLOCK_READ_NS = 100.0


def clock_check(worker):
    """The worker's TSC cross-validation (`--clock-check`), or None if it cannot run one."""
    try:
        result = subprocess.run([str(worker), "--clock-check"], capture_output=True, text=True, timeout=60)
        if result.returncode != 0:
            return None
        return decode(ClockCheck, json.loads(result.stdout))
    except (OSError, subprocess.SubprocessError, ValueError, ValidationError):
        return None


def clock_check_missing(check):
    """Missing evidence from a clock check: each entry one way latencies could be wrong."""
    if check is None:
        return ["clock:cross_validation_unavailable"]
    missing = []
    if check.rate_spread_ppm > CLOCK_RATE_SPREAD_PPM:
        missing.append("clock:tsc_rate_unstable")
    if abs(check.monotonic_slew_ppm) > CLOCK_SLEW_PPM:
        missing.append("clock:monotonic_slewed")
    if check.read_ns > CLOCK_READ_NS:
        missing.append("clock:slow_clock_read")
    if check.proven_skews:
        missing.append("clock:tsc_skew_across_cpus")
    if check.backwards_on_migration:
        missing.append("clock:tsc_backwards_on_migration")
    if check.unplaced_cpus:
        missing.append("clock:skew_unmeasured_on_some_cpus")
    return missing


def parse_ldd(text):
    """(soname, path or None) for each object `ldd` lists; the vDSO has no file."""
    objects = []
    for line in (text or "").splitlines():
        line = line.strip()
        if not line or line.startswith("statically linked"):
            continue
        if "=>" in line:
            name, target = (part.strip() for part in line.split("=>", 1))
            path = None if target.startswith("not found") else target.split(" (", 1)[0].strip() or None
        else:  # the loader, or the vDSO: "path (0x...)"
            name = line.split(" (", 1)[0].strip()
            path = name if name.startswith("/") else None
        objects.append((Path(name).name if name.startswith("/") else name, path))
    return objects


def dependency_closure(worker):
    """The shared objects the loader resolves for the worker, each hashed; None if unknown.

    `ldd` runs the dynamic loader in trace mode, so it names what THIS host
    resolves, which is what the class must follow: a library update is a new
    environment. The vDSO is the kernel's and has no file; an object the
    loader cannot find is kept with no hash.
    """
    try:
        result = subprocess.run(["ldd", str(worker)], capture_output=True, text=True, timeout=30)
    except (OSError, subprocess.SubprocessError):
        return None
    if result.returncode != 0:
        # A static binary is "not a dynamic executable": a closure of nothing.
        return [] if "not a dynamic executable" in (result.stdout + result.stderr) else None
    closure = []
    for name, path in parse_ldd(result.stdout):
        if name.startswith("linux-vdso") or name.startswith("linux-gate"):
            continue
        digest = None
        if path is not None:
            try:
                digest = file_hash(path)
            except OSError:
                digest = None
        closure.append(SharedObject(name, path, digest))
    return sorted(closure, key=lambda o: o.name)


def cpu_identity(read=_text):
    """(family, model number, stepping, microcode) of the first CPU in /proc/cpuinfo."""
    values = {}
    for line in (read("/proc/cpuinfo") or "").splitlines():
        if not line.strip():
            break
        key, _, value = line.partition(":")
        values.setdefault(key.strip(), value.strip())
    def number(key):
        return int(values[key]) if values.get(key, "").isdecimal() else None
    return number("cpu family"), number("model"), number("stepping"), values.get("microcode") or None


def thp_modes(read=_text):
    """The selected `[mode]` of THP enabled and defrag. The library's default,
    madvise(MADV_HUGEPAGE), does nothing under `never`."""
    def selected(name):
        words = (read("/sys/kernel/mm/transparent_hugepage/" + name) or "").split()
        chosen = [word[1:-1] for word in words if word.startswith("[") and word.endswith("]")]
        return chosen[0] if len(chosen) == 1 else None
    return selected("enabled"), selected("defrag")


# Boot parameters that name the boot disk or kernel file, not behaviour (the
# kernel release is in the class already). Everything else, such as idle=poll,
# accept_memory= and mitigations=, moves results and so stays in the class.
CMDLINE_IDENTITY_KEYS = ("BOOT_IMAGE", "initrd", "root")


def class_cmdline(cmdline):
    if cmdline is None:
        return None
    return " ".join(word for word in cmdline.split() if word.split("=", 1)[0] not in CMDLINE_IDENTITY_KEYS)


def steal_ticks(read=_text):
    """Steal time since boot, in clock ticks, from /proc/stat's aggregate line."""
    for line in (read("/proc/stat") or "").splitlines():
        fields = line.split()
        if fields and fields[0] == "cpu" and len(fields) > 8 and fields[8].isdecimal():
            return int(fields[8])
    return None


def memory_limit(evidence=None):
    if evidence is None:
        evidence = memory_evidence(_text)
    limits = [limit for limit in [evidence["guest_total_bytes"],
        *(a["limit_bytes"] for a in evidence["ancestors"])] if limit is not None]
    return min(limits) if limits else None


def source_identity():
    root = Path(__file__).resolve().parents[2]
    try:
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root).decode().strip()
        patch = subprocess.check_output(["git", "diff", "HEAD", "--binary", "--no-ext-diff"], cwd=root)
        untracked = subprocess.check_output(["git", "ls-files", "--others", "--exclude-standard", "-z"], cwd=root)
        files = {}
        for name in untracked.decode().split("\0"):
            path = root / name
            source = name.startswith(("include/", "src/", "cmake/", "tests/", "benchmarks/oram/",
                                      "benchmarks/support/", "benchmarks/campaigns/", "analysis/oram_bench"))
            source |= name == "analysis/CMakeLists.txt"
            if source and path.is_file() and (path.suffix in (".hpp", ".cpp", ".py", ".json", ".cmake") or path.name == "CMakeLists.txt"):
                files[name] = file_hash(path)
        return identity("source-v1", [revision, hashlib.sha256(patch).hexdigest(), files])
    except (OSError, subprocess.CalledProcessError):
        return "unverified-source"


def inspect(worker, execution="native", *, physical_cores=None, cache_domains=None, library_header=None):
    """Environment evidence. The class is what a result may be pooled within.

    The class = worker binary + library headers + CPU/topology +
    runtime + dependency + kernel (release, command line, THP modes). Git
    revision, dirty diff and Python tooling are recorded (source_identity) but
    excluded, so a coordinator or reducer fix neither strands nor silently
    restarts a campaign. The runtime label is checked against what the guest
    kernel shows (`runtime:` evidence); `run` refuses a mismatch.
    """
    worker = Path(worker).resolve(strict=True)
    allowed = sorted(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else []
    topology = capture_topology(allowed, _text)
    core_count = len(topology.physical_core_slots) if topology.physical_core_slots is not None else None
    domains = topology.cache_domains
    model = None
    for line in (_text("/proc/cpuinfo") or "").splitlines():
        if line.startswith("model name"):
            model = line.split(":", 1)[1].strip()
            break
    build = "sha256-" + file_hash(worker)
    source = source_identity()
    closure = dependency_closure(worker)
    missing = ["verified_thread_placement"]
    if closure is None:
        missing.append("dependency_closure_unavailable")
        dependency = identity("dependency-observation-v1", [platform.libc_ver(), platform.machine()])
    else:
        missing.extend("dependency:not_found:" + o.name for o in closure if o.sha256 is None)
        dependency = identity("dependency-closure-v1", [platform.machine(),
                                                         [[o.name, o.sha256] for o in closure]])
    if execution in ("tdx", "snp"):
        missing.append("protected_attestation")  # verified offline; reduce reads the verdict
    memory = memory_evidence(_text)
    missing.extend("memory:" + field for field in memory["missing_evidence"])
    missing.extend("topology:" + reason for reason in topology.missing_evidence)
    missing.extend("topology_contract:" + reason for reason in topology_contract(
        topology, physical_cores=physical_cores, cache_domains=cache_domains))
    compiled, flags = compiled_isa(worker), host_flags()
    clock_source = _text("/sys/devices/system/clocksource/clocksource0/current_clocksource")
    clock_missing = isa_and_clock(compiled, flags, clock_source)
    missing.extend(clock_missing)
    check = clock_check(worker)
    check_missing = clock_check_missing(check)
    missing.extend(check_missing)
    # Validated: an invariant TSC is the clocksource, and it passed every
    # cross-check. Otherwise the record claims only the OS's monotonic clock.
    tsc_validated = (check is not None and not check_missing and flags is not None and
                     all(flag in flags for flag in CLOCK_FLAGS[:2]) and
                     not any(reason.startswith("clock:") for reason in clock_missing))
    recorded = None if flags is None else sorted(
        f for f in flags if f in set(compiled or ()) | set(CLOCK_FLAGS) | set(WAIT_FLAGS))
    tee = detect_tee(flags)
    missing.extend(tee.missing_evidence)
    missing.extend(runtime_contract(execution, tee))
    family, model_number, stepping, microcode = cpu_identity(_text)
    thp_enabled, thp_defrag = thp_modes(_text)
    cmdline = _text("/proc/cmdline") or None
    if library_header is None:
        from .resolution import library_header_identity
        library_header = library_header_identity()
    environment_class = identity("environment-class-v5", [execution, model, family, model_number, stepping,
        plain(topology), allowed, build, library_header, dependency, platform.release(),
        class_cmdline(cmdline), thp_enabled, thp_defrag])
    environment = Environment(1,
        identity("host-v1", _text("/etc/machine-id") or platform.node()),
        _text("/proc/sys/kernel/random/boot_id"), environment_class, execution,
        False, None, model, core_count, allowed,
        domains, memory_limit(memory), build, source, dependency,
        "tsc_validated" if tsc_validated else "monotonic", repr(time.get_clock_info("monotonic")),
        missing, topology, library_header,
        compiled, recorded, clock_source, tee, None, cmdline, thp_enabled, thp_defrag,
        family, model_number, stepping, microcode, steal_ticks(_text),
        os.sysconf("SC_CLK_TCK") if hasattr(os, "sysconf") else None,
        dependency_closure=closure, clock_check=check, guest_memory=capture_guest_memory(execution, tee))
    environment.validate()
    return plain(environment)
