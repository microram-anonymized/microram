"""Confidential-VM evidence inside the guest: detection, report fetch and parsing.

In a cloud confidential VM the harness runs inside the guest, so the runtime
adapter is detection and evidence, not a launcher. Detection reads what the
guest kernel shows: a CPU flag, a guest driver's device and the boot log's
memory-encryption line. It never verifies anything. A report fetched through
configfs-tsm is verified offline, and no row is `protected_verified` until a
verdict is attached (attestation.py). Readers are injectable, so fixtures stand
in for sysfs, devices and configfs.
"""
from dataclasses import dataclass
import hashlib
import os
from pathlib import Path
import secrets
import subprocess
from typing import Literal, Optional

from .codec import ValidationError, canonical, require

TeeRuntime = Literal["tdx", "snp"]
TEE_RUNTIMES = ("tdx", "snp")
# configfs-tsm's report interface (Linux 6.7 or later). Plain VMs have it too
# (a WSL2 VM does, for example), so it is recorded, never a TEE signal.
TSM_REPORT = Path("/sys/kernel/config/tsm/report")
# The `provider` configfs-tsm names for each runtime's guest driver.
PROVIDERS = {"tdx": "tdx_guest", "snp": "sev_guest"}
DEVICES = {"tdx": "/dev/tdx_guest", "snp": "/dev/sev-guest"}
# mem_encrypt_init() prints this once at boot, and only when memory encryption
# is active: "... Intel TDX" in a TD, "... AMD SEV SEV-ES SEV-SNP" in an SNP guest.
KERNEL_LINE = "Memory Encryption Features active:"
KERNEL_NAMES = {"tdx": "Intel TDX", "snp": "SEV-SNP"}
# The kernel sets `tdx_guest` only after CPUID leaf 0x21 identifies a TD. The
# sev* flags are recorded only: a host CPU's SNP support does not make a guest
# confidential, so they would mislabel a plain control on the same hardware.
TEE_CPU_FLAGS = ("sev", "sev_es", "sev_snp", "tdx_guest")


@dataclass(frozen=True)
class TeeDetection:
    """What the guest kernel shows, and the runtime derived from it.

    `indicated` lists every TEE with any positive signal; `shown` is the one
    whose required signals all hold. TDX needs the `tdx_guest` flag and
    /dev/tdx_guest, SNP needs /dev/sev-guest, and a boot line that names a TEE
    must name the same one. An absent line says nothing (the ring buffer may
    have wrapped), so a report capture, which runs as root, requires it.
    """
    schema_version: Literal[1]
    cpu_flags: Optional[list[str]]
    tdx_device: bool
    sev_guest_device: bool
    kernel_log_readable: bool
    kernel_memory_encryption: Optional[str]
    tsm_report_interface: bool
    indicated: list[TeeRuntime]
    shown: Optional[TeeRuntime]
    missing_evidence: list[str]

    def validate(self):
        require(self == assess_tee(self.cpu_flags, self.tdx_device, self.sev_guest_device,
                                   self.kernel_log_readable, self.kernel_memory_encryption,
                                   self.tsm_report_interface), "inconsistent derived TEE evidence")

    def kernel_names(self, runtime):
        """True when the boot line names `runtime`: the capture's stronger rule."""
        return self.kernel_memory_encryption is not None and KERNEL_NAMES[runtime] in self.kernel_memory_encryption


def assess_tee(cpu_flags, tdx_device, sev_guest_device, kernel_log_readable, kernel_line, tsm_report_interface):
    require(cpu_flags is None or cpu_flags == sorted(set(cpu_flags) & set(TEE_CPU_FLAGS)),
            "TEE CPU flags must be a sorted subset of the recorded flags")
    require(kernel_log_readable or kernel_line is None, "an unreadable kernel log cannot hold a line")
    require(kernel_line is None or kernel_line.startswith(KERNEL_LINE), "not the memory-encryption line")
    says = None if kernel_line is None else {runtime: KERNEL_NAMES[runtime] in kernel_line
                                            for runtime in TEE_RUNTIMES}
    tdx_flag = None if cpu_flags is None else "tdx_guest" in cpu_flags
    signals = {"tdx": [tdx_flag, tdx_device, says and says["tdx"]],
               "snp": [sev_guest_device, says and says["snp"]]}
    required = {"tdx": [tdx_flag, tdx_device], "snp": [sev_guest_device]}
    indicated = [runtime for runtime in TEE_RUNTIMES if any(v is True for v in signals[runtime])]
    missing = []
    if cpu_flags is None:
        missing.append("tee:cpu_flags_unreadable")
    if not kernel_log_readable:
        missing.append("tee:kernel_log_unreadable")
    elif kernel_line is None and indicated:
        missing.append("tee:kernel_line_absent")  # on a plain host, absence is the expected state
    shown = None
    if len(indicated) > 1:
        missing.append("tee:conflicting_indications")
    elif indicated:
        runtime = indicated[0]
        if all(v is True for v in required[runtime]) and (says is None or says[runtime]):
            shown = runtime
        else:
            missing.append(f"tee:incomplete_{runtime}_evidence")
    return TeeDetection(1, cpu_flags, tdx_device, sev_guest_device, kernel_log_readable, kernel_line,
                        tsm_report_interface, indicated, shown, sorted(missing))


def _kernel_line(text):
    lines = [line[line.index(KERNEL_LINE):].strip() for line in text.splitlines() if KERNEL_LINE in line]
    return lines[-1] if lines else None


def kernel_log(run=subprocess.run):
    """(readable, memory-encryption line). dmesg first, then this boot's journal.

    Unprivileged reads fail under dmesg_restrict or without journal access; an
    empty output is never a real kernel log, so it counts as unreadable.
    """
    readable = False
    for command in (["dmesg"], ["journalctl", "-k", "-b", "--no-pager", "-q", "-o", "cat"]):
        try:
            result = run(command, capture_output=True, text=True, timeout=30)
        except (OSError, subprocess.SubprocessError):
            continue
        if result.returncode == 0 and result.stdout.strip():
            readable = True
            line = _kernel_line(result.stdout)
            if line is not None:
                return True, line
    return readable, None


def detect_tee(flags, exists=os.path.exists, log=kernel_log):
    """Live detection. `flags` is /proc/cpuinfo's flag set, or None when unreadable."""
    readable, line = log()
    return assess_tee(None if flags is None else sorted(set(flags) & set(TEE_CPU_FLAGS)),
                      exists(DEVICES["tdx"]), exists(DEVICES["snp"]), readable, line, exists(str(TSM_REPORT)))


def runtime_contract(runtime, detection):
    """Why `runtime` may not label this host ([] when it may).

    A tdx or snp label needs the host to show that TEE; a native label needs a
    host that indicates none, so the plain control can never carry the TEE label
    or the reverse. Fake (synthetic) evidence is never checked.
    """
    if runtime in ("fake", "unspecified"):
        return []
    if detection is None:
        return ["runtime:tee_detection_missing"]
    if runtime == "native":
        return [f"runtime:native_on_tee_host:{tee}" for tee in detection.indicated]
    return [] if detection.shown == runtime else [f"runtime:{runtime}_not_shown"]


# Reports. Offsets are the published layouts: AMD SEV-SNP ABI (56860)
# ATTESTATION_REPORT, and Intel's DCAP quote v4/v5 with the TD report body.
SNP_REPORT_BYTES = 0x4A0
SNP_POLICY_DEBUG_BIT = 19
# PLATFORM_INFO bit 4 is CIPHERTEXT_HIDING_EN (CIPHERTEXT_HIDING_DRAM_EN in later
# ABI revisions). The raw word is kept, so a corrected reading loses nothing.
SNP_CIPHERTEXT_HIDING_BIT = 4
TDX_TEE_TYPE = 0x81
TDX_BODY_BYTES = 584
TDX_ATTRIBUTES_OFFSET = 120  # TDATTRIBUTES in the TD report body; bit 0 is DEBUG
TDX_REPORT_DATA_OFFSET = 520


@dataclass(frozen=True)
class ReportFacts:
    """Fields read from the report locally. The offline verifier is authoritative."""
    layout: Literal["snp_report", "tdx_quote_v4", "tdx_quote_v5", "unrecognized"]
    report_version: Optional[int]
    report_data_matches: Optional[bool]
    # A debuggable guest (TD attribute DEBUG, SNP policy DEBUG) is not protected.
    debug: Optional[bool]
    snp_platform_info: Optional[int] = None
    snp_ciphertext_hiding: Optional[bool] = None


def report_facts(runtime, blob, expected):
    def word(offset, size):
        return int.from_bytes(blob[offset:offset + size], "little")
    unrecognized = ReportFacts("unrecognized", None, None, None)
    if runtime == "snp":
        if len(blob) < SNP_REPORT_BYTES:
            return unrecognized
        info = word(0x40, 8)
        return ReportFacts("snp_report", word(0, 4), blob[0x50:0x90] == expected,
                           bool(word(0x08, 8) >> SNP_POLICY_DEBUG_BIT & 1), info,
                           bool(info >> SNP_CIPHERTEXT_HIDING_BIT & 1))
    if len(blob) < 48:
        return unrecognized
    version = word(0, 2)
    if word(4, 4) != TDX_TEE_TYPE or version not in (4, 5):
        return unrecognized
    # v5 puts a (type, size) descriptor before the body: 2 = TD 1.0, 3 = TD 1.5.
    body = 48 if version == 4 else 54
    if (version == 5 and word(48, 2) not in (2, 3)) or len(blob) < body + TDX_BODY_BYTES:
        return unrecognized
    data = blob[body + TDX_REPORT_DATA_OFFSET:body + TDX_REPORT_DATA_OFFSET + 64]
    return ReportFacts(f"tdx_quote_v{version}", version, data == expected,
                       bool(word(body + TDX_ATTRIBUTES_OFFSET, 8) & 1))


class ConfigfsReport:
    """One private configfs-tsm report entry. Creating it needs root."""

    def __init__(self, root=TSM_REPORT):
        self.path = Path(root) / f"oram-bench-{os.getpid()}-{secrets.token_hex(4)}"

    def __enter__(self):
        try:
            os.mkdir(self.path)
        except PermissionError as error:
            raise ValidationError("creating a configfs-tsm report entry needs root") from error
        except FileNotFoundError as error:
            raise ValidationError(f"no configfs-tsm report interface at {self.path.parent} "
                                  "(Linux 6.7 or later, configfs mounted)") from error
        return self

    def __exit__(self, *exc):
        os.rmdir(self.path)

    def read(self, name):
        return (self.path / name).read_bytes()

    def write(self, name, data):
        with open(self.path / name, "wb", buffering=0) as stream:
            stream.write(data)


def fetch_report(data, entry=None):
    """(provider, report, auxiliary or None, generation) through configfs-tsm.

    Each write to inblob increments `generation`, so exactly one increment
    between the two reads proves no other writer changed the request.
    """
    require(type(data) is bytes and len(data) == 64, "report data must be 64 bytes")
    with (entry if entry is not None else ConfigfsReport()) as report:
        before = int(report.read("generation"))
        report.write("inblob", data)
        blob = report.read("outblob")
        try:
            auxiliary = report.read("auxblob") or None
        except OSError:
            auxiliary = None
        provider = report.read("provider").decode().strip()
        after = int(report.read("generation"))
    require(after == before + 1, "configfs-tsm generation moved: another writer changed the request")
    require(bool(blob), "configfs-tsm returned an empty report")
    return provider, blob, auxiliary, after


@dataclass(frozen=True)
class AttestationBinding:
    """What a report's report data commits to: the pooling class on one host and boot.

    Not the whole environment record: that also holds the calling process's
    cgroup memory and the tooling's git state, which differ between the root
    capture and the service user's run. The record references the capture.
    """
    schema_version: Literal[1]
    runtime: TeeRuntime
    host_identity: str
    boot_identity: str
    environment_class: str


def report_data(binding):
    """The 64 bytes written to inblob: SHA-512 of the canonical binding."""
    return hashlib.sha512(canonical(binding)).digest()


@dataclass(frozen=True)
class AttestationFile:
    path: str  # relative to the campaign directory
    sha256: str
    bytes: int

    def validate(self):
        require(self.path.startswith("attestations/") and "\\" not in self.path and
                all(part not in ("", ".", "..") for part in self.path.split("/")), "unsafe attestation path")
        require(len(self.sha256) == 64 and all(c in "0123456789abcdef" for c in self.sha256), "invalid sha256")


@dataclass(frozen=True)
class AttestationCapture:
    schema_version: Literal[1]
    binding: AttestationBinding
    report_data: str
    provider: str
    generation: int
    report: AttestationFile
    auxiliary: Optional[AttestationFile]
    facts: ReportFacts
    # Taken as root when the report was fetched, so the boot log was readable.
    detection: TeeDetection
    captured_unix_ns: int

    def validate(self):
        runtime = self.binding.runtime
        require(self.report_data == report_data(self.binding).hex(), "report data differs from its binding")
        require(self.provider == PROVIDERS[runtime], "configfs-tsm provider differs from the runtime")
        require(self.detection.shown == runtime and self.detection.kernel_names(runtime),
                "capture-time detection does not show the runtime")
        require(self.facts.report_data_matches is not False, "report does not carry the bound report data")


@dataclass(frozen=True)
class AttestationVerdict:
    """An offline verifier's result for one capture (go-tdx-guest, Intel Trust
    Authority, or snpguest against AMD's VCEK); `output` keeps its log."""
    schema_version: Literal[1]
    capture_sha256: str
    verifier: str
    result: Literal["verified", "failed"]
    reference: str
    output: Optional[AttestationFile]

    def validate(self):
        require(len(self.capture_sha256) == 64 and all(c in "0123456789abcdef" for c in self.capture_sha256),
                "invalid capture sha256")
