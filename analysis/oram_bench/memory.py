"""Streaming reduction of worker memory CSV v1; no host inspection or timing.

Memory observations are independent of the C++ timing/histogram reducer. Peaks
are sampled process/cgroup quantities, never a library allocation total.
"""
import csv
from pathlib import Path

from .codec import require


COLUMNS = ("rss_bytes", "pss_bytes", "high_water_rss_bytes", "swap_bytes",
           "minor_faults", "major_faults", "cgroup_current_bytes",
           "cgroup_peak_bytes", "cgroup_limit_bytes")
HEADER = ("phase", "monotonic_ns", *COLUMNS)
# Output names. memory.peak is the lifetime peak of the coordinator's cgroup,
# so it includes earlier trials; VmHWM is this worker's per-trial peak.
FIELDS = tuple("cgroup_lifetime_peak_bytes" if c == "cgroup_peak_bytes" else c for c in COLUMNS)
PEAK_FIELDS = ("rss_bytes", "pss_bytes", "high_water_rss_bytes", "swap_bytes",
               "cgroup_current_bytes", "cgroup_lifetime_peak_bytes")
# cgroup_limit_bytes is the tightest memory.max up to the hierarchy root,
# "unlimited" when no level sets one, and blank when unknown.
UNLIMITED = "unlimited"
PHASES = {name: index for index, name in enumerate((
    "before_construction", "after_construction", "after_fill", "after_warmup",
    "after_settle", "before_measure", "measure", "final_drain", "log_flush",
    "after_drain", "after_verify"))}
PERIODIC = {"measure", "final_drain", "log_flush", "phase_transition"}


def _number(text, *, optional=False, unlimited=False):
    if text == "" and optional:
        return None
    if text == UNLIMITED and unlimited:
        return UNLIMITED
    require(0 < len(text) <= 20 and text.isascii() and text.isdecimal(),
            "memory CSV requires unsigned decimal integers or blank optional fields")
    value = int(text)
    require(value < 2**64, "memory CSV integer exceeds uint64")
    return value


def reduce_memory_stream(stream, *, interval_ns=None):
    """Summarize one (possibly interrupted) trial using bounded accumulator space.

    Paging evidence is conservative: before_measure through after_drain includes
    logger setup/flushing. A major fault need not be swap-backed, so its reason
    is explicit. Minor faults are diagnostic, not an in-RAM invalidation.
    """
    require(interval_ns is None or (type(interval_ns) is int and 0 < interval_ns < 2**64),
            "memory sampling interval must be a positive uint64 or null")
    reader = csv.reader(stream, strict=True)
    try:
        require(tuple(next(reader, ())) == HEADER, "unsupported memory CSV header")
        phases, seen = {}, set()
        previous_time, rank = None, -1
        last_fault = {"minor_faults": None, "major_faults": None}
        baseline = end = None
        active = False
        active_samples = 0
        envelope_peaks = dict.fromkeys(PEAK_FIELDS)
        complete_fields = True
        previous_active_time = None
        max_gap = None
        reasons = set()
        interval_major = None
        minimum_limit = None
        limit_status = "unknown"
        trial_peak = None
        count = 0
        for row in reader:
            require(len(row) == len(HEADER), "memory CSV row has wrong field count")
            phase = row[0]
            require(phase in PHASES or phase == "phase_transition", "unknown memory CSV phase")
            timestamp = _number(row[1])
            require(previous_time is None or timestamp >= previous_time, "memory timestamps decrease")
            previous_time = timestamp
            if phase != "phase_transition":
                require(PHASES[phase] >= rank, "memory lifecycle phases decrease")
                rank = PHASES[phase]
            if phase not in PERIODIC and phase != "before_measure":
                require(phase not in seen, "duplicate memory lifecycle boundary")
            if phase in PERIODIC:
                require(baseline is not None and end is None, "periodic memory sample outside measurement envelope")
            seen.add(phase)
            values = {field: _number(text, optional=True, unlimited=field == "cgroup_limit_bytes")
                      for field, text in zip(FIELDS, row[2:])}
            for field in last_fault:
                value = values[field]
                require(value is None or last_fault[field] is None or value >= last_fault[field],
                        "cumulative memory fault counter decreased")
                if value is not None:
                    last_fault[field] = value
            count += 1
            observation = phases.setdefault(phase, {"samples": 0, "first_ns": timestamp,
                "last_ns": timestamp, "sampled_max_bytes": dict.fromkeys(PEAK_FIELDS),
                "known_samples": dict.fromkeys(FIELDS, 0)})
            observation["samples"] += 1
            observation["last_ns"] = timestamp
            for field, value in values.items():
                if value is not None:
                    observation["known_samples"][field] += 1
                    if field in PEAK_FIELDS:
                        old = observation["sampled_max_bytes"][field]
                        observation["sampled_max_bytes"][field] = value if old is None else max(old, value)
            limit, high_water = values["cgroup_limit_bytes"], values["high_water_rss_bytes"]
            if limit == UNLIMITED:
                limit_status = "limited" if minimum_limit is not None else UNLIMITED
            elif limit is not None:
                minimum_limit = limit if minimum_limit is None else min(minimum_limit, limit)
                limit_status = "limited"
            if high_water is not None:
                trial_peak = high_water if trial_peak is None else max(trial_peak, high_water)
            if phase == "before_measure" and baseline is None:
                baseline = {"monotonic_ns": timestamp, **values}
                active = True
            # Missing before_measure still permits reporting swap evidence from
            # the final boundary, but never produces a clean classification.
            if (active and phase != "after_verify") or phase == "after_drain":
                active_samples += 1
                for field in PEAK_FIELDS:
                    value, old = values[field], envelope_peaks[field]
                    if value is not None:
                        envelope_peaks[field] = value if old is None else max(old, value)
                if previous_active_time is not None:
                    gap = timestamp - previous_active_time
                    max_gap = gap if max_gap is None else max(max_gap, gap)
                previous_active_time = timestamp
                swap, major = values["swap_bytes"], values["major_faults"]
                complete_fields &= swap is not None and major is not None
                if swap:
                    reasons.add("nonzero_process_swap")
                if major is not None:
                    if interval_major is not None and major > interval_major:
                        reasons.add("major_faults_in_measurement_envelope")
                    interval_major = major
            if phase == "after_drain":
                end = {"monotonic_ns": timestamp, **values}
                active = False
        complete = baseline is not None and end is not None
        deltas = {}
        for field in ("minor_faults", "major_faults"):
            deltas[field] = (end[field] - baseline[field] if complete and
                            baseline[field] is not None and end[field] is not None else None)
        paging = ("paging_observed" if reasons else "no_paging_observed" if
                  complete and complete_fields else "unknown")
        return {"memory_summary_schema_version": 2, "memory_csv_schema_version": 1,
            "scope": "process_and_cgroup_observations", "samples": count,
            "sampling_interval_ns": interval_ns, "phases": phases,
            # The worker process's VmHWM: its resident peak over the whole trial.
            "trial_peak_rss_bytes": trial_peak,
            "cgroup_lifetime_peak_scope": "coordinator_cgroup_lifetime_including_earlier_trials",
            # limited (the minimum below), unlimited (no level sets memory.max) or unknown.
            "cgroup_limit_status": limit_status,
            "minimum_observed_cgroup_limit_bytes": minimum_limit,
            "measurement_envelope": {"scope": "before_measure_through_after_drain",
                "complete": complete, "begin_ns": baseline["monotonic_ns"] if baseline else None,
                "end_ns": end["monotonic_ns"] if end else None,
                "samples": active_samples, "maximum_observation_gap_ns": max_gap,
                "sampled_max_bytes": envelope_peaks,
                "fault_deltas": deltas},
            "paging_status": paging, "paging_reasons": sorted(reasons),
            # No absence-of-paging observation establishes all publication gates.
            "in_ram_valid": False if reasons else None,
            "library_allocation_bytes": None, "initialization_peak_complete": False}
    except csv.Error as error:
        raise ValueError("malformed memory CSV: " + str(error)) from error


def reduce_memory(path, *, interval_ns=None):
    with Path(path).open(newline="") as stream:
        return reduce_memory_stream(stream, interval_ns=interval_ns)
