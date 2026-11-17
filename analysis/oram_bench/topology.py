"""Exposed Linux topology evidence and strict, measurement-free contracts.

Physical-core IDs here are guest-exposed identities, never host attestation.
Readers and cache enumeration can be injected for offline correctness tests.
"""
from dataclasses import dataclass
from pathlib import Path
import re
from typing import Literal, Optional

from .codec import require


@dataclass(frozen=True)
class CpuTopology:
    cpu: int
    package: Optional[int]
    core: Optional[int]
    siblings: Optional[list[int]]
    l3_cpus: Optional[list[int]]
    l3_bytes: Optional[int]
    # The NUMA node, from /sys/devices/system/node; None where the kernel
    # exposes none (and in evidence recorded without the field).
    node: Optional[int] = None

    def validate(self):
        require(0 <= self.cpu < 2**20, "CPU ID outside supported bounds")
        require(self.node is None or type(self.node) is int and 0 <= self.node < 2**16, "invalid NUMA node")
        require(all(value is None or type(value) is int and 0 <= value < 2**64
                    for value in (self.package, self.core)), "invalid exposed core identity")
        for group in (self.siblings, self.l3_cpus):
            require(group is None or (group == sorted(set(group)) and self.cpu in group and
                    all(0 <= cpu < 2**20 for cpu in group)), "invalid CPU topology group")
        require((self.l3_cpus is None) == (self.l3_bytes is None) and
                (self.l3_bytes is None or self.l3_bytes > 0), "inconsistent L3 size evidence")


@dataclass(frozen=True)
class TopologyEvidence:
    schema_version: Literal[1]
    cpus: list[CpuTopology]
    physical_core_slots: Optional[list[int]]
    cache_domains: Optional[list[list[int]]]
    missing_evidence: list[str]
    physical_host_verified: Literal[False] = False
    # The NUMA nodes the allowed CPUs span, when every CPU's node is known.
    # Neither placement policy considers memory locality, so more than one is
    # refused by the contract: a sub-NUMA-clustered Xeon, a two-socket host or
    # a Zen part in NPS2/NPS4 needs the run bound to one node (numactl).
    numa_nodes: Optional[list[int]] = None

    def validate(self):
        require(self == _assess(self.cpus), "inconsistent derived topology evidence")


def cpu_list(value):
    require(isinstance(value, str) and bool(value), "missing CPU list")
    result = set()
    for part in value.split(','):
        require(re.fullmatch(r'[0-9]+(?:-[0-9]+)?', part) is not None, "malformed CPU list")
        bounds = [int(x) for x in part.split('-')]
        first, last = bounds[0], bounds[-1]
        require(0 <= first <= last < 2**20 and last-first < 65536, "CPU range outside supported bounds")
        values = set(range(first, last+1))
        require(not result.intersection(values), "overlapping CPU ranges")
        result.update(values)
        require(len(result) <= 65536, "CPU list too large")
    return sorted(result)


def _nonnegative(value):
    if value is None or re.fullmatch(r'[0-9]+', value) is None:
        return None
    number = int(value)
    return number if number < 2**64 else None


def _cache_bytes(value):
    match = re.fullmatch(r'([0-9]+)([KM]?)', value or '')
    if not match:
        return None
    size = int(match[1]) * {'': 1, 'K': 1024, 'M': 1024**2}[match[2]]
    return size if 0 < size < 2**64 else None


def numa_nodes_by_cpu(read_text):
    """{cpu: node} from /sys/devices/system/node, or {} when it is absent or malformed."""
    try:
        nodes = cpu_list(read_text('/sys/devices/system/node/online'))
        result = {}
        for node in nodes:
            for cpu in cpu_list(read_text(f'/sys/devices/system/node/node{node}/cpulist')):
                require(cpu not in result, "CPU in two NUMA nodes")
                result[cpu] = node
        return result
    except ValueError:
        return {}


def capture_topology(allowed, read_text, cache_indexes=None):
    require(len(set(allowed)) == len(allowed) and all(type(cpu) is int and 0 <= cpu < 2**20 for cpu in allowed),
            "invalid allowed CPU mask")
    if cache_indexes is None:
        cache_indexes = lambda root: sorted((root / 'cache').glob('index*'))
    nodes = numa_nodes_by_cpu(read_text)
    cpus = []
    for cpu in sorted(allowed):
        root = Path(f'/sys/devices/system/cpu/cpu{cpu}')
        package = _nonnegative(read_text(root / 'topology/physical_package_id'))
        core = _nonnegative(read_text(root / 'topology/core_id'))
        try:
            siblings = cpu_list(read_text(root / 'topology/thread_siblings_list'))
            require(cpu in siblings, "CPU absent from its sibling list")
        except ValueError:
            siblings = None
        l3, size = None, None
        try:
            caches = [index for index in cache_indexes(root) if read_text(index / 'level') == '3'
                      and read_text(index / 'type') == 'Unified']
            require(len(caches) == 1, "missing/ambiguous unified L3")
            l3 = cpu_list(read_text(caches[0] / 'shared_cpu_list'))
            require(cpu in l3, "CPU absent from its L3 domain")
            size = _cache_bytes(read_text(caches[0] / 'size'))
            require(size is not None, "invalid L3 size")
        except (ValueError, OSError):
            l3, size = None, None
        cpus.append(CpuTopology(cpu, package, core, siblings, l3, size, nodes.get(cpu)))
    return _assess(cpus)


def _assess(cpus):
    require([entry.cpu for entry in cpus] == sorted({entry.cpu for entry in cpus}),
            "CPU evidence must be unique and ordered")
    missing = []
    for entry in cpus:
        entry.validate()
        if entry.package is None or entry.core is None or entry.siblings is None:
            missing.append(f'cpu:{entry.cpu}:core_identity')
        if entry.l3_cpus is None or entry.l3_bytes is None:
            missing.append(f'cpu:{entry.cpu}:l3_identity')
    by_cpu = {entry.cpu: entry for entry in cpus}
    core_ok = bool(cpus) and not any('core_identity' in reason for reason in missing)
    cache_ok = bool(cpus) and not any('l3_identity' in reason for reason in missing)
    cores = {}
    for entry in cpus:
        if entry.package is not None and entry.core is not None:
            cores.setdefault((entry.package, entry.core), set()).add(entry.cpu)
    for entry in cpus:
        if entry.siblings is not None and entry.package is not None and entry.core is not None:
            group = cores[(entry.package, entry.core)]
            if (set(entry.siblings).intersection(by_cpu) != group or
                any(entry.siblings != by_cpu[cpu].siblings for cpu in group)):
                core_ok = False
                missing.append(f'cpu:{entry.cpu}:inconsistent_siblings')
        if entry.l3_cpus is not None:
            group = cores.get((entry.package, entry.core), set())
            if any(entry.l3_cpus != by_cpu[cpu].l3_cpus for cpu in group):
                cache_ok = False
                missing.append(f'cpu:{entry.cpu}:core_spans_l3_domains')
            for cpu in entry.l3_cpus:
                other = by_cpu.get(cpu)
                if other is not None and (entry.l3_cpus != other.l3_cpus or entry.l3_bytes != other.l3_bytes):
                    cache_ok = False
                    missing.append(f'cpu:{entry.cpu}:inconsistent_l3')
                    break
    slots = None
    if core_ok:
        cores = {}
        for entry in cpus:
            cores.setdefault((entry.package, entry.core), entry.cpu)
        slots = sorted(cores.values())
    domains = None
    if cache_ok:
        domains = [list(domain) for domain in sorted({tuple(cpu for cpu in entry.l3_cpus if cpu in by_cpu) for entry in cpus})]
    if not cpus:
        missing.append('allowed_cpu_mask')
    numa = sorted({entry.node for entry in cpus}) if cpus and all(e.node is not None for e in cpus) else None
    return TopologyEvidence(1, cpus, slots, domains, sorted(set(missing)), numa_nodes=numa)


def topology_contract(evidence, *, physical_cores=None, cache_domains=None):
    """Require exact exposed counts and one NUMA node, while allowing SMT siblings in the mask.

    physical_core_slots names one allowed logical CPU per exposed physical core;
    selecting these slots excludes SMT sharing without changing host affinity.
    """
    evidence.validate()
    reasons = []
    for name, value in (('physical_cores', physical_cores), ('cache_domains', cache_domains)):
        require(value is None or type(value) is int and value > 0, f'{name} must be positive')
    if physical_cores is not None:
        if evidence.physical_core_slots is None:
            reasons.append('unverified_exposed_physical_cores')
        elif len(evidence.physical_core_slots) != physical_cores:
            reasons.append('exposed_physical_core_count_mismatch')
    if cache_domains is not None:
        if evidence.cache_domains is None:
            reasons.append('unverified_exposed_cache_domains')
        elif len(evidence.cache_domains) != cache_domains:
            reasons.append('exposed_cache_domain_count_mismatch')
    # Always: placement ignores memory locality, so the mask must stay on one node.
    if evidence.numa_nodes is not None and len(evidence.numa_nodes) > 1:
        reasons.append('multiple_numa_nodes')
    return reasons

