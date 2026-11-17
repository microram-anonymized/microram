"""Memory admission evidence and pure budget checks, independent of benchmarks.

Available bytes are a snapshot, not a reservation. Unknown allocation peaks or
hidden cgroup ancestors never become evidence that a native trial fits memory.
"""
from pathlib import Path, PurePosixPath
import re

from .codec import require


def _read(path):
    try:
        return Path(path).read_text().strip()
    except (OSError, UnicodeError):
        return None


def _uint(text):
    if text is None or not 0 < len(text) <= 20 or not text.isascii() or not text.isdecimal():
        return None
    value = int(text)
    return value if value < 2**64 else None


def _path(text):
    # mountinfo escapes whitespace and backslashes as octal sequences.
    text = re.sub(r"\\(040|011|012|134)", lambda m: chr(int(m[1], 8)), text)
    path = PurePosixPath(text)
    return path if path.is_absolute() and ".." not in path.parts else None


def memory_evidence(read=_read):
    """Read exposed Linux guest/cgroup-v2 constraints; injectable for fixtures."""
    result = {"memory_evidence_schema_version": 1, "guest_total_bytes": None,
              "guest_available_bytes": None, "cgroup_mount": None,
              "cgroup_membership": None, "ancestors": [], "missing_evidence": []}
    missing = result["missing_evidence"]
    for line in (read("/proc/meminfo") or "").splitlines():
        parts = line.split()
        if len(parts) == 3 and parts[0] in ("MemTotal:", "MemAvailable:") and parts[2] == "kB":
            value = _uint(parts[1])
            if value is not None and value <= (2**64 - 1) // 1024:
                result["guest_total_bytes" if parts[0] == "MemTotal:" else "guest_available_bytes"] = value * 1024
    for field in ("guest_total_bytes", "guest_available_bytes"):
        if result[field] is None:
            missing.append(field)
    membership = None
    for line in (read("/proc/self/cgroup") or "").splitlines():
        if line.startswith("0::"):
            membership = _path(line[3:])
            break
    if membership is None:
        missing.append("cgroup_v2_membership")
        return result
    result["cgroup_membership"] = str(membership)
    mounts = []
    for line in (read("/proc/self/mountinfo") or "").splitlines():
        parts = line.split()
        try:
            separator = parts.index("-")
        except ValueError:
            continue
        if separator < 6 or len(parts) <= separator + 1 or parts[separator + 1] != "cgroup2":
            continue
        root, mount = _path(parts[3]), _path(parts[4])
        if root is None or mount is None:
            continue
        if membership == root or root in membership.parents:
            mounts.append((root, mount, membership.relative_to(root), False))
        elif membership == PurePosixPath("/"):
            # Namespace root at a mounted subtree: ancestors remain unavailable.
            mounts.append((root, mount, PurePosixPath("."), True))
    if not mounts:
        missing.append("cgroup_v2_mount_mapping")
        return result
    # Prefer the broadest visible hierarchy, including all exposed ancestors.
    root, mount, relative, namespaced = min(mounts, key=lambda m: (m[3], len(m[0].parts), str(m[1])))
    result["cgroup_mount"] = {"root": str(root), "mount_point": str(mount), "namespace_root_mapping": namespaced}
    if root != PurePosixPath("/") or namespaced:
        missing.append("cgroup_ancestors_above_mount")
    group = mount / relative
    while True:
        maximum, current = read(str(group / "memory.max")), read(str(group / "memory.current"))
        limit = _uint(maximum)
        usage = _uint(current)
        # The hierarchy root has no memory.max or memory.current; it is
        # unlimited and bounded by guest MemAvailable. Only non-root groups
        # have cgroup.type, so a cgroup-namespace root is not mistaken for it.
        top = group == mount and root == PurePosixPath("/") and not namespaced
        non_root = read(str(group / "cgroup.type")) is not None
        hierarchy_root = (top and maximum is None and not non_root and
                          read(str(group / "cgroup.controllers")) is not None)
        if top and non_root:
            missing.append("cgroup_ancestors_above_mount")
        known_limit = maximum == "max" or limit is not None or hierarchy_root
        result["ancestors"].append({"path": str(group), "limit_bytes": limit,
                                    "limit_known": known_limit, "current_bytes": usage,
                                    "hierarchy_root": hierarchy_root})
        if not known_limit:
            missing.append("cgroup_limit:" + str(group))
        if usage is None and maximum != "max" and not hierarchy_root:
            missing.append("cgroup_current:" + str(group))
        if group == mount:
            break
        group = group.parent
    return result


def assess_memory(evidence, *, lower_bound_bytes, estimated_peak_bytes=None,
                  headroom_ppm=200_000, host_limit_bytes=None):
    """Assess *additional* worker bytes against remaining budgets at each scope.

    A supplied peak must cover all simultaneous library, harness, initialization,
    allocator and runtime allocations. Partial estimates belong in lower_bound.
    Headroom reserves a fraction of each total limit, not of its unused space.
    """
    for name, value in (("lower_bound_bytes", lower_bound_bytes), ("estimated_peak_bytes", estimated_peak_bytes),
                        ("host_limit_bytes", host_limit_bytes)):
        require((value is None and name != "lower_bound_bytes") or
                (type(value) is int and 0 <= value < 2**64), name + " must be uint64 or optional null")
    require(type(headroom_ppm) is int and 0 <= headroom_ppm < 1_000_000, "invalid memory headroom")
    require(estimated_peak_bytes is None or estimated_peak_bytes >= lower_bound_bytes,
            "complete peak cannot be below the allocation lower bound")
    require(evidence.get("memory_evidence_schema_version") == 1, "unsupported memory evidence")
    missing = list(evidence["missing_evidence"])
    budgets = []

    def usable(limit):
        return limit * (1_000_000 - headroom_ppm) // 1_000_000

    total, available = evidence["guest_total_bytes"], evidence["guest_available_bytes"]
    for field in ("guest_total_bytes", "guest_available_bytes"):
        value = evidence[field]
        require(value is None or type(value) is int and 0 <= value < 2**64, "invalid guest memory evidence")
        if value is None:
            missing.append(field)
    if total is not None and available is not None and available > total:
        missing.append("guest_available_exceeds_total")
    if not evidence["ancestors"] or evidence["cgroup_mount"] is None:
        missing.append("cgroup_hierarchy")
    if total is not None:
        budgets.append({"scope": "guest_total", "additional_bytes_upper_bound": usable(total)})
        if available is not None:
            budgets.append({"scope": "guest_available", "additional_bytes_upper_bound": max(0, available - (total - usable(total)))})
    if host_limit_bytes is not None:
        budgets.append({"scope": "configured_host_limit", "additional_bytes_upper_bound": usable(host_limit_bytes)})
    for ancestor in evidence["ancestors"]:
        limit, current = ancestor["limit_bytes"], ancestor["current_bytes"]
        require(all(v is None or type(v) is int and 0 <= v < 2**64 for v in (limit, current)),
                "invalid cgroup memory evidence")
        if not ancestor["limit_known"]:
            missing.append("cgroup_limit:" + ancestor["path"])
        if limit is not None and current is None:
            missing.append("cgroup_current:" + ancestor["path"])
        if limit is not None:
            # Even missing usage can prove the lower bound exceeds a hard cap.
            budgets.append({"scope": "cgroup:" + ancestor["path"],
                            "additional_bytes_upper_bound": max(0, usable(limit) - (current or 0))})
    required = estimated_peak_bytes if estimated_peak_bytes is not None else lower_bound_bytes
    exceeded = [budget["scope"] for budget in budgets if required > budget["additional_bytes_upper_bound"]]
    if estimated_peak_bytes is None:
        missing.append("complete_additional_allocation_peak")
    if not budgets:
        missing.append("available_memory_budget")
    return {"memory_preflight_schema_version": 1, "headroom_ppm": headroom_ppm,
            "lower_bound_bytes": lower_bound_bytes, "estimated_peak_bytes": estimated_peak_bytes,
            "available_bytes_upper_bound": min((b["additional_bytes_upper_bound"] for b in budgets), default=None),
            "budgets": budgets, "exceeded_scopes": exceeded, "missing_evidence": sorted(set(missing)),
            "status": "exceeds_budget" if exceeded else "insufficient_evidence" if missing else "within_estimated_budget"}


def attempt_preflight(row, entry, evidence, rate=None):
    """Admit one attempt: its resolution estimate against live memory evidence.

    The components are the resolver's modelled library bytes plus the worker's
    own known buffers (resolution.estimated_memory); the event buffer is priced
    with the attempt's actual rate. Modelled bytes are still requested bytes,
    so the estimate is a lower bound, never certified fit.
    """
    from .resolution import event_buffer_bytes
    spec = row["spec"]
    components = dict(entry["estimated_memory"])
    components["event_buffer"] = event_buffer_bytes(row, rate)
    lower = sum(components.values())
    require(lower < 2**64, "estimated allocation lower bound exceeds uint64")
    return {"scope": "worker_additional_allocations", "components": components,
            "evidence": evidence, "assessment": assess_memory(evidence, lower_bound_bytes=lower,
                headroom_ppm=spec["resources"]["headroom_ppm"],
                host_limit_bytes=spec["resources"]["host_memory_limit_bytes"])}
