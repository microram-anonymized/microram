"""Guest runtime-private memory evidence, kept apart from process/library memory (memory.py).

In a confidential guest, RAM is private (encrypted, accepted by the guest) except
the shared swiotlb bounce pool used for device I/O; lazily accepted memory
(`Unaccepted:`) is not yet usable. Everything here is read from the guest kernel
and is evidence, not attestation. Absence is never read as a value: a field
the kernel did not report is null and named in `unavailable`. A host showing no
TEE signal records `not_applicable`, never a protection claim.
"""
from dataclasses import dataclass
import re
import subprocess
from typing import Literal, Optional

from .codec import require

SWIOTLB_SLAB = 2048  # IO_TLB_SHIFT = 11
UNITS = {"KB": 1024, "MB": 1024**2, "GB": 1024**3}
DMESG_BOUNCE = re.compile(r"software IO TLB: mapped \[mem [^\]]*\] \((\d+)(KB|MB|GB)\)")
DEBUGFS_SWIOTLB = "/sys/kernel/debug/swiotlb/io_tlb_nslabs"
ESTIMATE_BASIS = "guest_ram - shared_bounce - unaccepted; an estimate, MemTotal may already exclude the swiotlb pool"


@dataclass(frozen=True)
class GuestMemory:
    schema_version: Literal[1]
    runtime: str                       # the label; what the kernel shows is environment.tee
    private_memory: Literal["applicable", "not_applicable"]
    guest_ram_bytes: Optional[int]
    guest_ram_source: Optional[str]
    unaccepted_bytes: Optional[int]
    unaccepted_source: Optional[str]
    shared_bounce_bytes: Optional[int]
    shared_bounce_source: Optional[str]  # debugfs, dmesg or cmdline_request (the request, not the pool)
    private_bytes_estimate: Optional[int]
    private_estimate_basis: Optional[str]
    hugetlb_pages: Optional[int]       # reserved huge pages; THP modes are environment.thp_*
    hugetlb_page_bytes: Optional[int]
    unavailable: list[str]             # "<field>:<reason>"

    def validate(self):
        known = None not in (self.guest_ram_bytes, self.unaccepted_bytes, self.shared_bounce_bytes)
        require((self.private_bytes_estimate is not None) == (known and self.private_memory == "applicable"),
                "private estimate needs all inputs")
        require((self.private_bytes_estimate is None) == (self.private_estimate_basis is None),
                "private estimate carries its basis")
        require(self.private_memory == "applicable" or (self.unaccepted_bytes is self.shared_bounce_bytes is None),
                "not_applicable guests record no private-memory values")
        if self.private_bytes_estimate is not None:
            require(self.private_bytes_estimate == max(0, self.guest_ram_bytes - self.shared_bounce_bytes
                                                      - self.unaccepted_bytes), "inconsistent private estimate")


def _meminfo(text):
    values = {}
    for line in (text or "").splitlines():
        key, _, rest = line.partition(":")
        parts = rest.split()
        if parts and parts[0].isdecimal() and len(parts[0]) <= 19:
            values[key] = int(parts[0]) * (1024 if parts[1:] == ["kB"] else 1)
    return values


def _cmdline_slabs(cmdline):
    for word in (cmdline or "").split():
        if word.startswith("swiotlb="):
            first = word[8:].split(",")[0]
            if first.isdecimal():
                return int(first)
    return None


def assess_guest_memory(runtime, tee, meminfo, cmdline, dmesg, debugfs_slabs, reasons=None):
    """Pure. `meminfo`, `cmdline` and `dmesg` are raw text and `debugfs_slabs` is
    io_tlb_nslabs, each None when unreadable, with the cause in `reasons[name]`
    (default "unreadable"). `tee` is the TeeDetection."""
    reasons = reasons or {}
    unavailable = []

    def why(name):
        return reasons.get(name, "unreadable")
    applicable = bool(tee is not None and tee.indicated) or runtime in ("tdx", "snp")
    info = _meminfo(meminfo)
    ram = info.get("MemTotal")
    if ram is None:
        unavailable.append("guest_ram_bytes:" + why("meminfo"))
    unaccepted = bounce = source = None
    if applicable:
        unaccepted = info.get("Unaccepted")
        if unaccepted is None:
            unavailable.append("unaccepted_bytes:" + (why("meminfo") if meminfo is None else "no_meminfo_line"))
        if debugfs_slabs is not None:
            bounce, source = debugfs_slabs * SWIOTLB_SLAB, "debugfs"
        else:
            unavailable.append("swiotlb_debugfs:" + why("debugfs"))
            match = DMESG_BOUNCE.search(dmesg or "")
            if match:
                bounce, source = int(match[1]) * UNITS[match[2]], "dmesg"
            else:
                unavailable.append("swiotlb_dmesg:" + (why("dmesg") if dmesg is None else "not_in_log"))
                slabs = _cmdline_slabs(cmdline)
                if slabs is not None:
                    bounce, source = slabs * SWIOTLB_SLAB, "cmdline_request"
                else:
                    unavailable.append("swiotlb_cmdline:" + (why("cmdline") if cmdline is None else "no_swiotlb_parameter"))
        if bounce is None:
            unavailable.append("shared_bounce_bytes:not_reported")
        elif source != "debugfs":
            unavailable = [u for u in unavailable if not u.startswith("shared_bounce_bytes")]
    else:
        unavailable += [f"{f}:not_applicable" for f in ("unaccepted_bytes", "shared_bounce_bytes",
                                                       "private_bytes_estimate")]
    estimate = None
    if applicable and None not in (ram, unaccepted, bounce):
        estimate = max(0, ram - bounce - unaccepted)
    elif applicable:
        unavailable.append("private_bytes_estimate:inputs_missing")
    pages, size = info.get("HugePages_Total"), info.get("Hugepagesize")
    if pages is None or size is None:
        unavailable.append("hugetlb:" + why("meminfo"))
    record = GuestMemory(1, runtime, "applicable" if applicable else "not_applicable",
                         ram, None if ram is None else "meminfo:MemTotal",
                         unaccepted, None if unaccepted is None else "meminfo:Unaccepted",
                         bounce, source, estimate, None if estimate is None else ESTIMATE_BASIS,
                         pages, size, unavailable)
    record.validate()
    return record


def read_dmesg(run=subprocess.run):
    """(text, reason): unprivileged `dmesg` only. A failure is `permission` (dmesg_restrict
    gives a nonzero exit), `missing` without the binary, `empty` for a blank log."""
    try:
        result = run(["dmesg"], capture_output=True, text=True, timeout=30)
    except FileNotFoundError:
        return None, "missing"
    except (OSError, subprocess.SubprocessError):
        return None, "permission"
    if result.returncode != 0:
        return None, "permission"
    return (result.stdout, None) if result.stdout.strip() else (None, "empty")


def read_file(path):
    try:
        with open(path) as stream:
            return stream.read().strip(), None
    except PermissionError:
        return None, "permission"
    except FileNotFoundError:
        return None, "missing"
    except (OSError, UnicodeError):
        return None, "unreadable"


def capture_guest_memory(runtime, tee, read=read_file, dmesg=read_dmesg):
    meminfo, r_mem = read("/proc/meminfo")
    cmdline, r_cmd = read("/proc/cmdline")
    log, r_log = dmesg()
    slabs_text, r_dbg = read(DEBUGFS_SWIOTLB)
    slabs = int(slabs_text) if slabs_text is not None and slabs_text.isdecimal() else None
    if slabs_text is not None and slabs is None:
        r_dbg = "unparsable"
    reasons = {"meminfo": r_mem, "cmdline": r_cmd, "dmesg": r_log, "debugfs": r_dbg}
    return assess_guest_memory(runtime, tee, meminfo, cmdline, log, slabs, {k: v for k, v in reasons.items() if v})
