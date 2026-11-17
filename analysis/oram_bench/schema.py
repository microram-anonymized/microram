"""Version 1 campaign contracts. Times are ns, sizes bytes, ratios integer ppm.

None on an override means automatic; explicit 0/False are never discarded.
None on an observation means unavailable, never an observed zero.
Construction/security eligibility remains the C++ resolver's responsibility.
"""

from dataclasses import dataclass, field
import math
from typing import Literal, Optional, Union, get_args

from .codec import require
from .guest_memory import GuestMemory
from .tee import AttestationCapture, AttestationFile, AttestationVerdict, TeeDetection
from .topology import TopologyEvidence

# The baselines (benchmarks/baselines/README.md): never chosen by `auto`, and
# each runs only where its worker is frozen. std_unordered_map lives in the main
# worker; the others have their own workers under benchmarks/baselines/.
BaselineScheme = Literal["std_unordered_map", "h2o2ram", "h2o2ram_shipped", "sonic_zingoram",
                         "sonic_zingoram_recursive"]
Scheme = Literal["auto", "hierarchical_incremental", "hierarchical_synchronous", "tree", "std_unordered_map",
                 "h2o2ram", "h2o2ram_shipped", "sonic_zingoram", "sonic_zingoram_recursive"]
PinnedScheme = Literal["hierarchical_incremental", "hierarchical_synchronous", "tree", "std_unordered_map",
                       "h2o2ram", "h2o2ram_shipped", "sonic_zingoram", "sonic_zingoram_recursive"]
BASELINE_SCHEMES = get_args(BaselineScheme)
# Index ORAMs address blocks by a number: they cannot report a miss.
INDEX_ORAM_SCHEMES = ("h2o2ram", "h2o2ram_shipped", "sonic_zingoram", "sonic_zingoram_recursive")
Security = Literal["oblivious", "oblivious_position_map_outside", "not_oblivious"]
# Every row carries a security label. Only `oblivious` rows are drawn as
# like-for-like competitors; h2o2ram_shipped (published H2O2RAM, whose lookups
# branch on the secret) and std_unordered_map are not oblivious, and
# sonic_zingoram keeps its position map outside the ORAM.
SECURITY_LABELS = {"sonic_zingoram": "oblivious_position_map_outside", "std_unordered_map": "not_oblivious",
                   "h2o2ram_shipped": "not_oblivious", "fake": "not_oblivious", "noop": "not_oblivious"}


def security_label(scheme):
    """The security label of a scheme; library schemes, auto included, are oblivious."""
    return SECURITY_LABELS.get(scheme, "oblivious")


# Both SONIC rows time the position lookup inside each access (the
# recursive map, or position_[block] outside the array); a data-tree-only row
# would be "excluded" and never complete-access throughput. Other schemes have
# no separate position lookup to label.
POSITION_LOOKUP_LABELS = {"sonic_zingoram": "included", "sonic_zingoram_recursive": "included"}


def position_lookup_label(scheme):
    return POSITION_LOOKUP_LABELS.get(scheme)


ApiMode = Literal["scalar", "batch"]

Arrival = Literal["saturated", "fixed"]


@dataclass(frozen=True)
class SynchronousOverrides:
    """The arena fields, which both hierarchy modes take; the synchronous mode
    has no rebuild threads, so it takes only these."""
    branching_factor: Optional[Literal[2, 4, 8]] = None
    online_stash_entries: Optional[int] = None
    prefix_flushes: Optional[Literal[2, 4, 8]] = None
    top_digit: Optional[int] = None
    dense_prefixes: Optional[int] = None
    half_fanout_prefix: Optional[bool] = None
    tier_buckets: Optional[int] = None
    bank_first: Optional[Literal["off", "no_clone"]] = None
    batch_lanes: Optional[int] = None
    batch_execution: Optional[Literal["chunked_cascade", "parallel_tiles"]] = None
    batch_participants: Optional[int] = None
    batch_bucket_scan: Optional[bool] = None
    batch_profile: Optional[bool] = None
    batch_result_layout: Optional[Literal["rows", "sliced_place_at_lane"]] = None
    batch_spin_ns: Optional[int] = None
    wait_limit_ms: Optional[int] = None

@dataclass(frozen=True)
class HierarchyOverrides(SynchronousOverrides):
    """The incremental mode: the arena fields plus its rebuild threads."""
    # The rebuild's threads: a budget the library heuristic divides, or an
    # explicit owner count with its division ("first-last,..." highest group
    # first), top-group helpers and lanes. The resolver refuses mixing the two.
    rebuild_threads: Optional[int] = None
    owner_threads: Optional[int] = None
    level_groups: Optional[str] = None
    top_helpers: Optional[int] = None
    bottom_helpers: Optional[int] = None
    rebuild_lanes: Optional[int] = None
    lane_min_buckets: Optional[int] = None
    slice_target_rate: Optional[int] = None
    slice_touches: Optional[int] = None
    inline_work_factor_ppm: Optional[int] = None
    time_rebuild_stages: Optional[bool] = None
    near_max_level: Optional[int] = None
    owner_spin_ns: Optional[int] = None
    park_retry_us: Optional[int] = None
    # The rebuild cost model the heuristic divides by (LevelArenaRebuildCost):
    # a target's tuner fit (`fit-rebuild`), never a per-row knob. They are
    # heuristic inputs, so they stay out of the configuration key.
    rebuild_cost_line_picos: Optional[int] = None
    rebuild_cost_residual_line_picos: Optional[int] = None
    rebuild_cost_offer_line_picos: Optional[int] = None
    rebuild_cost_job_nanos: Optional[int] = None
    rebuild_cost_middle_burst_ppm: Optional[int] = None
    rebuild_cost_helper_speedup_ppm: Optional[int] = None
    rebuild_cost_max_top_threads: Optional[int] = None
    rebuild_cost_thread_gain_floor_ppm: Optional[int] = None
    rebuild_cost_probe_bucket_picos: Optional[int] = None
    rebuild_cost_probe_line_picos: Optional[int] = None
    # The worst line cost a rebuild piece is budgeted at; unlike the rest it
    # sizes the engine's pieces directly, so it is part of the configuration.
    rebuild_cost_slice_line_picos: Optional[int] = None

@dataclass(frozen=True)
class PositionMapOverrides:
    mode: Optional[Literal["hierarchical_incremental", "hierarchical_synchronous"]] = None
    incremental: Optional[HierarchyOverrides] = None
    synchronous: Optional[SynchronousOverrides] = None

@dataclass(frozen=True)
class TreeOverrides:
    fold: Optional[int] = None
    leaf_scale: Optional[int] = None
    max_load_ppm: Optional[int] = None
    max_folded_slots: Optional[int] = None
    # 0: the default rule (3 up to fold 4, 4 at fold 5).
    stash_registers: Optional[Literal[0, 3, 4]] = None
    prefetch_ahead: Optional[int] = None
    uid_from_key: Optional[bool] = None
    payload_max_threads: Optional[int] = None
    payload_threshold: Optional[int] = None
    payload_spin_us: Optional[int] = None
    payload_monitor_wait: Optional[bool] = None
    # Placement only: payload workers go in the caller's cache domain.
    payload_near: Optional[bool] = None
    position_map: PositionMapOverrides = field(default_factory=PositionMapOverrides)

@dataclass(frozen=True)
class H2O2RAMOverrides:
    """H2O2RAM's own knobs; its planner picks the rest."""
    # 128 is its default; 256 is its commented large-block setting.
    linear_scan_threshold: Optional[Literal[128, 256]] = None
    # OpenMP's idle policy; unset keeps libgomp's default (spin, then sleep).
    omp_wait_policy: Optional[Literal["active", "passive"]] = None


@dataclass(frozen=True)
class UnorderedMapOverrides:
    """std::unordered_map, reserved for N entries at the library's default
    maximum load factor (1.0). hash_noexcept: a noexcept hash, so libstdc++
    keeps no hash per node (unset: not noexcept, the hash cached)."""
    hash_noexcept: Optional[bool] = None


@dataclass(frozen=True)
class SonicOverrides:
    """SONIC's ZingORAM trees. The stash follows from (Z, A):
    there is deliberately no stash_bound, which could give up SONIC's 2^-80."""
    # The data tree: Z real and S dummy slots, eviction rate A (0: the largest
    # SONIC's analysis allows), routing depth R, eviction batch E.
    bucket_real_size: Optional[int] = None
    bucket_dummy_size: Optional[int] = None
    eviction_rate: Optional[int] = None
    routing_depth: Optional[int] = None
    evict_batch: Optional[int] = None
    # Access threads T (batch rows spread over them) and eviction threads (a
    # divisor of 2^R; 0 is 2^R).
    access_threads: Optional[int] = None
    eviction_threads: Optional[int] = None
    # sonic_zingoram_recursive only: branching factor b, top-map entries C, and
    # the map trees' Z, S, A, E (shared by every map level).
    map_branching_factor: Optional[Literal[16, 32, 64, 128, 256]] = None
    map_top_entries: Optional[int] = None
    map_bucket_real_size: Optional[int] = None
    map_bucket_dummy_size: Optional[int] = None
    map_eviction_rate: Optional[int] = None
    map_evict_batch: Optional[int] = None


@dataclass(frozen=True)
class Overrides:
    schema_version: Literal[1] = 1
    scheme: Scheme = "auto"
    # On auto these are per-scheme candidate constraints, never ignored globals.
    incremental: Optional[HierarchyOverrides] = None
    synchronous: Optional[SynchronousOverrides] = None
    tree: Optional[TreeOverrides] = None
    # One block per baseline with knobs.
    h2o2ram: Optional[H2O2RAMOverrides] = None
    sonic: Optional[SonicOverrides] = None
    unordered_map: Optional[UnorderedMapOverrides] = None

    def validate(self):
        library = self.incremental is not None or self.synchronous is not None or self.tree is not None
        require(not (self.scheme in BASELINE_SCHEMES and library),
                "a baseline scheme takes no library override block")
        require(self.h2o2ram is None or self.scheme in ("h2o2ram", "h2o2ram_shipped"),
                "the h2o2ram block belongs to the h2o2ram schemes")
        require(self.sonic is None or self.scheme in ("sonic_zingoram", "sonic_zingoram_recursive"),
                "the sonic block belongs to the sonic schemes")
        require(self.unordered_map is None or self.scheme == "std_unordered_map",
                "the unordered_map block belongs to std_unordered_map")

@dataclass(frozen=True)
class Shape:
    name: str
    key_bytes: int
    value_bytes: int
    # `dense` makes key i the little-endian integer i, so an index ORAM can use
    # it as its index; `permuted` spreads the keys over the key space.
    key_layout: Literal["permuted", "dense"] = "permuted"

    def validate(self):
        require(self.key_bytes > 0 and self.value_bytes > 0, "record widths must be positive")


@dataclass(frozen=True)
class Workload:
    # `counter`: request k touches live key k*S mod N, S about 0.618 N and
    # coprime with N (the worker's --key-pattern counter), with the uniform
    # read/update sequence. It removes the key generator's random draws from the
    # request thread while every scheme, the key-order-filled baselines
    # included, still sees scattered keys. All hits.
    distribution: Literal["uniform", "counter"] = "uniform"
    occupancy_ppm: int = 1_000_000
    read_ppm: int = 950_000
    hit_ppm: int = 1_000_000
    miss_key_count: int = 0
    buffer_requests: int = 4096

    def validate(self):
        require(0 < self.occupancy_ppm <= 1_000_000, "occupancy_ppm must be in (0,1000000]")
        require(self.read_ppm <= 1_000_000 and self.hit_ppm <= 1_000_000,
                "read/hit ratios exceed one million ppm")
        require((self.hit_ppm == 1_000_000) == (self.miss_key_count == 0),
                "miss workload must declare a disjoint nonempty miss key set")
        require(self.hit_ppm == 1_000_000 or self.read_ppm == 1_000_000,
                "v1 miss workloads are read-only; writes must update existing keys")
        require(self.buffer_requests > 0, "generator buffer must be positive")
        require(self.distribution == "uniform" or self.hit_ppm == 1_000_000,
                "the counter key pattern cannot issue misses")


@dataclass(frozen=True)
class BatchPolicy:
    # arrive_together: offered-load rows deliver each batch's requests at one instant (one batch every
    # batch / rate seconds), so a batch never waits to form; its response time runs from that arrival.
    formation: Literal["fixed_count", "max_count_or_timeout", "arrive_together"] = "fixed_count"
    timeout_ns: Optional[int] = None

    def validate(self):
        require((self.formation in ("fixed_count", "arrive_together") and self.timeout_ns is None) or
                (self.formation == "max_count_or_timeout" and self.timeout_ns is not None and
                 self.timeout_ns > 0), "timeout is required only for timeout batching")


@dataclass(frozen=True)
class Timing:
    warmup_ns: int = 5_000_000_000
    measurement_ns: int = 30_000_000_000
    # Unmeasured requests after warmup (the worker's --settle-requests), issued at the row's own rate.
    settle_requests: int = 0
    # Optional per-row settle for capacity sweeps: each row settles
    # max(settle_requests, ceil(capacity * settle_per_entry_ppm / 10^6)) requests (10^6: at least N).
    # The planner writes the row's count into its spec's settle_requests. Unset, the field is left out of
    # the plan, so plans and trial ids of campaigns without it are unchanged.
    settle_per_entry_ppm: Optional[int] = None
    drain_deadline_ns: int = 30_000_000_000
    # Construction, fill, settle and final verification, which no phase deadline
    # bounds; a default allowance, which pilots can replace per row with trial_time models.
    setup_allowance_ns: int = 120_000_000_000
    max_trial_ns: int = 600_000_000_000
    max_accesses: int = 2**32
    # Waiting requests a full-event (raw request log) trial may hold; histogram rows ignore it. 2^23 leaves room
    # for the backlog a top-level rebuild stall can build at a high offered rate.
    queue_limit: int = 2**23
    # Carries into the top hierarchy level the measurement window must contain
    # (a carry is one batch of entries moved into a level); two put one whole top
    # rebuild period inside it. Fewer label
    # the row `insufficient_cycle_coverage`; they are kept, never promoted.
    minimum_top_level_carries: int = 2

    def validate(self):
        require(self.measurement_ns > 0 and self.drain_deadline_ns > 0 and
                self.max_accesses > 0 and self.queue_limit > 0, "timing/queue limits must be positive")
        require(self.settle_per_entry_ppm is None or self.settle_per_entry_ppm > 0,
                "settle_per_entry_ppm must be positive; leave it unset for one settle_requests per campaign")
        # A warmup keeps its outstanding requests until its own drain deadline.
        warmup = self.warmup_ns + (self.drain_deadline_ns if self.warmup_ns else 0)
        require(self.max_trial_ns >= self.setup_allowance_ns + warmup + self.measurement_ns +
                self.drain_deadline_ns,
                "max_trial_ns cannot cover setup allowance, warmup and its drain, measurement and drain")


@dataclass(frozen=True)
class Instrumentation:
    # full_events is the diagnostic mode (one in-memory buffer per trial, sized
    # from the row's rate); histogram_checkpoints is the publication mode.
    logging: Literal["full_events", "histogram_checkpoints"] = "full_events"
    chunk_bytes: int = 4 * 1024 * 1024
    # Event buffer for saturated trials (coarse windows, plus per-call service
    # records when service_timing is on). Offered-load buffers are sized per row.
    buffer_bytes: int = 64 * 1024 * 1024
    # One histogram checkpoint per block of completion time (0: one block).
    checkpoint_interval_ns: int = 1_000_000_000
    memory_interval_ns: int = 100_000_000
    # Saturation count windows, in requests (the worker's --window-requests).
    window_requests: int = 1024
    service_timing: bool = False
    minimum_tail_count: int = 100
    # `full` checks every returned value against an 8-byte/live-key
    # version table; `off` (final large rows only, never smoke) allocates no
    # table and labels the row unverified. Hit/miss checks stay in both.
    verification: Literal["full", "off"] = "full"
    # Close histogram checkpoint blocks on a second thread on the harness core
    # (the worker's --checkpoint-thread 1), off the request thread. Plans carry
    # the field only when it is on, so existing trial ids are unchanged.
    checkpoint_thread: bool = False

    def validate(self):
        require(0 < self.chunk_bytes <= self.buffer_bytes, "event buffer must hold a chunk")
        require(not self.checkpoint_thread or self.logging == "histogram_checkpoints",
                "a checkpoint thread needs histogram checkpoints")
        require(self.memory_interval_ns > 0 and self.window_requests > 0 and self.minimum_tail_count > 0,
                "telemetry windows and tail count must be positive")
        # The worker's bound (benchmarks/support/memory.hpp): one day.
        require(self.memory_interval_ns <= 86_400_000_000_000,
                "memory_interval_ns must be at most one day (86400000000000 ns)")


@dataclass(frozen=True)
class Resources:
    physical_cores: int = 16
    harness_cores: Literal[1] = 1  # the worker reserves exactly one harness core
    smt: bool = False
    required_cache_domains: Optional[int] = 2
    allowed_cpus: Optional[list[int]] = None
    library_memory_limit_bytes: Optional[int] = None
    host_memory_limit_bytes: Optional[int] = None
    headroom_ppm: int = 200_000
    placement: Literal["near_far", "unplaced"] = "near_far"
    # The idle-wait instruction declared to the resolver. A row asking
    # for monitor-wait needs one, and `run` refuses a host whose doctor flags
    # (waitpkg for umwait, monitorx for mwaitx) do not expose it.
    monitor_wait: Literal["none", "umwait", "mwaitx"] = "none"
    # One spin-before-park for every waiting library thread (the paper presets, benchmarks/campaigns/paper/,
    # use 1 s, so nothing parks between requests). The resolver applies it to each spin the overrides leave unset
    # (ResourceBudget::spin_before_park_ns); None keeps the library defaults and earlier trial ids.
    spin_before_park_ns: Optional[int] = None

    def validate(self):
        require(self.physical_cores > self.harness_cores, "core budget must leave a library caller")
        require(self.spin_before_park_ns is None or self.spin_before_park_ns > 0,
                "spin_before_park_ns must be positive; leave it unset for the library defaults")
        require(self.headroom_ppm < 1_000_000, "headroom consumes the entire memory budget")
        require(self.required_cache_domains is None or self.required_cache_domains > 0,
                "required_cache_domains must be positive")
        require(self.required_cache_domains is None or self.physical_cores % self.required_cache_domains == 0,
                "required_cache_domains must split physical_cores evenly (the worker declares them to the resolver)")
        if self.allowed_cpus is not None:
            require(len(self.allowed_cpus) == len(set(self.allowed_cpus)) and bool(self.allowed_cpus),
                    "allowed_cpus must be nonempty and unique")
            require(len(self.allowed_cpus) >= self.physical_cores,
                    "allowed_cpus cannot supply the requested core count")
            require(all(cpu < 2**20 for cpu in self.allowed_cpus), "CPU ID outside supported bounds")
        for name in ("library_memory_limit_bytes", "host_memory_limit_bytes"):
            require(getattr(self, name) is None or getattr(self, name) > 0,
                    f"{name} must be positive when known")


@dataclass(frozen=True)
class Execution:
    # tdx and snp run in a confidential VM's guest; `unspecified` never launches.
    runtime: Literal["native", "snp", "tdx", "unspecified"] = "unspecified"
    require_protected: bool = True
    source_identity: Optional[str] = None
    build_identity: Optional[str] = None
    dependency_identity: Optional[str] = None
    policy_identity: str = "uncalibrated_fallback_v2"

    def validate(self):
        require(not (self.runtime == "native" and self.require_protected),
                "native execution cannot satisfy require_protected")


@dataclass(frozen=True)
class TrialTimeModel:
    """An arm's trial time, fitted from its pilot campaign (pilots.py): the per-arm time cap.

    A row measures for max(measurement_ns, coverage window), where the window
    holds coverage_accesses_per_entry_ppm / 10^6 accesses per requested entry
    at access_ns each (H2O2RAM's two top rebuilds: about 2 x capacity). A row
    whose setup, warmup, window and drain exceed max_trial_ns is skipped as
    trial_time_cap before running.

    access_ns and setup_ns_per_entry are measured at reference_capacity and
    scale as (capacity / reference_capacity)^(capacity_exponent_ppm / 10^6);
    without a reference they are constant. key_bytes, value_bytes and
    api_mode, when set, restrict the model to rows of those widths or that
    API: a baseline's cost need not be smooth in the width (H2O2RAM's planner
    picks other tables at 1 KiB), and a batch fills and serves faster.
    """
    setup_ns: int = 0
    setup_ns_per_entry: int = 0
    access_ns: int = 0
    coverage_accesses_per_entry_ppm: int = 0
    reference_capacity: Optional[int] = None
    capacity_exponent_ppm: int = 0
    key_bytes: Optional[int] = None
    value_bytes: Optional[int] = None
    api_mode: Optional[ApiMode] = None

    def validate(self):
        require(not self.coverage_accesses_per_entry_ppm or self.access_ns,
                "a coverage window needs the arm's access time")
        require(self.reference_capacity is None or self.reference_capacity > 0,
                "reference_capacity must be positive")
        require(not self.capacity_exponent_ppm or self.reference_capacity is not None,
                "a capacity exponent needs its reference_capacity")

    def selector(self):
        return (self.key_bytes, self.value_bytes, self.api_mode)

    def matches(self, shape, api_mode):
        return all(want is None or want == have for want, have in
                   zip(self.selector(), (shape["key_bytes"], shape["value_bytes"], api_mode)))

    def scaled(self, nanoseconds, capacity):
        """A time measured at reference_capacity, at this capacity (rounded up)."""
        if self.reference_capacity is None or not self.capacity_exponent_ppm:
            return nanoseconds
        ratio = (capacity / self.reference_capacity) ** (self.capacity_exponent_ppm / 1_000_000)
        return math.ceil(nanoseconds * ratio)


@dataclass(frozen=True)
class Candidate:
    name: str
    overrides: Overrides
    # Empty: no model, so no estimate and no pruning. Otherwise every row's
    # widths and API must match one model; the one with more selectors wins.
    trial_time: list[TrialTimeModel] = field(default_factory=list)

    def validate(self):
        selectors = [model.selector() for model in self.trial_time]
        require(len(selectors) == len(set(selectors)), f"{self.name}: two trial_time models for one width")

    def trial_time_model(self, shape, api_mode):
        matching = [m for m in self.trial_time if m.matches(shape, api_mode)]
        if not self.trial_time:
            return None
        require(bool(matching), f"candidate {self.name!r}: no trial_time model covers key_bytes "
                f"{shape['key_bytes']}, value_bytes {shape['value_bytes']}, api_mode {api_mode}")
        rank = {id(m): sum(part is not None for part in m.selector()) for m in matching}
        best = max(rank.values())
        chosen = [m for m in matching if rank[id(m)] == best]
        require(len(chosen) == 1, f"candidate {self.name!r}: trial_time models {[m.selector() for m in chosen]} "
                "tie for this width")
        return chosen[0]


@dataclass(frozen=True)
class RateGrid:
    absolute_ops_per_second: list[int] = field(default_factory=list)
    saturation_fractions_ppm: list[int] = field(default_factory=list)
    # No offered rate below this. Baseline curves and the rows matched to
    # them may set it lower. Absolute rates are
    # checked here; a frozen saturation fraction below it never launches.
    minimum_ops_per_second: int = 100_000

    def validate(self):
        require(bool(self.absolute_ops_per_second or self.saturation_fractions_ppm), "empty rate grid")
        require(self.minimum_ops_per_second > 0, "rate floor must be positive")
        require(all(v >= self.minimum_ops_per_second for v in self.absolute_ops_per_second),
                "absolute rate below the stage's minimum_ops_per_second")
        for values in (self.absolute_ops_per_second, self.saturation_fractions_ppm):
            require(len(values) == len(set(values)), "duplicate rate")
        require(all(v > 0 for v in self.absolute_ops_per_second + self.saturation_fractions_ppm),
                "rates must be positive")


@dataclass(frozen=True)
class Stage:
    name: str
    kind: Literal["smoke", "capacity", "latency", "value_width", "tuning"]
    shapes: list[Shape]
    capacities: list[int]
    candidates: list[Candidate]
    api_modes: list[ApiMode] = field(default_factory=lambda: ["scalar", "batch"])
    batch_sizes: list[int] = field(default_factory=lambda: [64])
    batch_policy: BatchPolicy = field(default_factory=BatchPolicy)
    rates: Optional[RateGrid] = None
    # A named stream gives the stage its own workload/arrival seeds; None
    # keeps the campaign's shared per-repetition seeds. The planner rejects a
    # held_out stage whose seeds a screening stage also uses.
    seed_stream: Optional[str] = None
    seed_role: Optional[Literal["screening", "finalist", "held_out"]] = None
    # A diagnostic stage (e.g. a low-rate screen) may go below
    # the 100k floor through its own minimum_ops_per_second; its rows carry
    # the `diagnostic_stage` publication blocker and `plot` leaves them out.
    diagnostic: bool = False

    def validate(self):
        for name in ("shapes", "capacities", "candidates", "api_modes"):
            require(bool(getattr(self, name)), f"{name} must be nonempty")
        for name in ("capacities", "api_modes", "batch_sizes"):
            values = getattr(self, name)
            require(len(values) == len(set(values)), f"duplicate {name}")
        for name in ("shapes", "candidates"):
            values = [v.name for v in getattr(self, name)]
            require(len(values) == len(set(values)), f"duplicate {name} names")
        require(all(v > 0 for v in self.capacities + self.batch_sizes), "capacity/batch size must be positive")
        require("batch" not in self.api_modes or bool(self.batch_sizes), "batch mode needs sizes")
        require((self.kind == "latency") == (self.rates is not None), "only latency stages need rates")
        require(self.kind == "latency" or self.batch_policy.formation == "fixed_count",
                "timeout batching and batches arriving together require offered arrivals")


@dataclass(frozen=True)
class CostLimits:
    max_trials: int = 4096
    # Bounds trials * max_trial_ns * (1 + planned_retries).
    max_campaign_trial_ns: int = 14 * 86400 * 1_000_000_000
    # Worker-failure retries budgeted per trial: the launch policy's default
    # --retries. Preemption retries are not budgeted.
    planned_retries: int = 1
    max_raw_bytes: Optional[int] = None

    def validate(self):
        require(self.max_trials > 0 and self.max_campaign_trial_ns > 0, "cost limits must be positive")
        require(self.max_raw_bytes is None or self.max_raw_bytes > 0, "max_raw_bytes must be positive")


@dataclass(frozen=True)
class Campaign:
    schema_version: Literal[1]
    name: str
    stages: list[Stage]
    repetitions: int = 3
    base_seed: int = 1
    order_seed: int = 1
    workload: Workload = field(default_factory=Workload)
    timing: Timing = field(default_factory=Timing)
    instrumentation: Instrumentation = field(default_factory=Instrumentation)
    resources: Resources = field(default_factory=Resources)
    execution: Execution = field(default_factory=Execution)
    limits: CostLimits = field(default_factory=CostLimits)

    def validate(self):
        require(0 < self.repetitions <= self.limits.max_trials, "repetitions exceed trial budget")
        require(bool(self.stages), "campaign needs stages")
        require(len({s.name for s in self.stages}) == len(self.stages), "duplicate stage name")
        # The worker enforces the same bounds at parse time; replay keeps every
        # waiting request plus one batch in memory.
        interval = self.instrumentation.checkpoint_interval_ns
        require(interval == 0 or (self.timing.measurement_ns + self.timing.drain_deadline_ns) // interval <= 4096,
                "checkpoint_interval_ns allows more than 4096 blocks over measurement plus drain")
        for stage in self.stages:
            largest = max(stage.batch_sizes) if "batch" in stage.api_modes else 1
            require(self.timing.queue_limit >= largest, "queue_limit is smaller than a caller batch")
            require(self.timing.queue_limit + largest <= 2**24,
                    "queue_limit plus caller batch exceeds the 2^24-request replay bound")


@dataclass(frozen=True)
class Choice:
    field: str
    value: Union[int, bool, str]
    source: Literal["explicit", "fallback", "derived"]
    reason: str


@dataclass(frozen=True)
class WorkerOverrideArgument:
    field: str
    value: str


@dataclass(frozen=True)
class ResolverRequest:
    resolver_request_schema_version: Literal[1]
    scheme: Scheme
    requested_capacity: int
    key_bytes: int
    value_bytes: int
    max_accesses: int
    api_mode: ApiMode
    caller_batch_size: int
    cores: int
    harness_cores: Literal[1]
    overrides: list[WorkerOverrideArgument]
    # Declared L3 domains splitting `cores` evenly; they cap an explicit
    # near/far boundary's rebuild budget per side. Older workers omit it.
    cache_domains: int = 1
    # Older workers omit it; they only generated permuted keys.
    key_layout: Literal["permuted", "dense"] = "permuted"
    # The declared idle-wait capability; a resolution without it means none.
    monitor_wait: Literal["none", "umwait", "mwaitx"] = "none"
    # The budget's one spin-before-park (0: library defaults). Workers print it only when set.
    spin_before_park_ns: int = 0

    def validate(self):
        require(self.requested_capacity > 0 and self.key_bytes > 0 and self.value_bytes > 0 and
                self.max_accesses > 0 and self.caller_batch_size > 0 and self.cores > self.harness_cores,
                "invalid resolver request sizes or budget")
        require(self.cache_domains > 0 and self.cores % self.cache_domains == 0,
                "cache domains must split the core budget evenly")
        require(self.api_mode != "scalar" or self.caller_batch_size == 1, "scalar resolver batch size must be one")
        names = [argument.field for argument in self.overrides]
        require(len(names) == len(set(names)), "duplicate resolver override argument")


# A baseline's own pool threads (H2O2RAM's TBB and OpenMP, SONIC's pthread
# pools): one entry per library slot they may use, not per thread.
BASELINE_POOL_ROLE = 10


@dataclass(frozen=True)
class WorkerThread:
    # Matches the native resolver's ThreadRole enum; the writer is not a library
    # role. 10 is a baseline pool slot.
    role: Literal[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    index: int
    cpu: Optional[int]
    # A rebuild thread's side of an explicit near/far boundary (true: the caller's L3).
    near: Optional[bool] = None


@dataclass(frozen=True)
class MemoryComponent:
    """One entry of a plan's modelled library memory.

    ``tallied``: the engine records every buffer of it and construction checks
    the record against the plan; ``modeled``: computed from the geometry the
    constructor sizes from; ``lower_bound``: below what is allocated.
    """
    component: str
    requested_bytes: int
    coverage: Literal["tallied", "modeled", "lower_bound"]


@dataclass(frozen=True)
class WorkerResolution:
    """Native resolved.json envelope, not the persisted exact-replay format.

    This validates placement structure; geometry/security eligibility remains
    the library resolver's responsibility. Older envelopes lacking slot policy
    fields cannot supply campaign placement evidence.
    """
    worker_schema_version: Literal[1, 2]
    scheme: PinnedScheme
    requested_capacity: int
    actual_capacity: int
    policy_identity: str
    configuration_key: str
    supports_direct_initialization: bool
    modeled_buffer_bytes: int
    choices: list[Choice]
    library_threads: int
    reserved_harness_cores: Literal[1]
    placement_verified: Literal[False]
    threads: list[WorkerThread]
    # baseline_self_placed: a baseline's pools place themselves inside the
    # library slots; placement.json then comes from a /proc scan (4.4).
    placement_policy: Literal["unplaced", "explicit", "near_far_v2", "baseline_self_placed"]
    cpu_slots: list[int]
    # Accesses between rebuilds reaching each level, lowest first: the
    # hierarchy's, or a tree's position map's (counted in position-map
    # accesses). The last entry is the top's rebuild period.
    carry_period_accesses: list[int] = field(default_factory=list)
    resolver_request: Optional[ResolverRequest] = None
    # The modelled buffers as the allocator is asked for them (each rounded to
    # its alignment, 2 MiB for a huge-page buffer), and their breakdown. Absent
    # from envelopes that do not report it and from baselines, which model none.
    modeled_reserved_bytes: Optional[int] = None
    memory_components: list[MemoryComponent] = field(default_factory=list)

    def validate(self):
        require((self.worker_schema_version == 2) == (self.resolver_request is not None),
                "worker schema 2 requires resolver request; schema 1 has no request binding")
        require(self.modeled_reserved_bytes is None or self.modeled_reserved_bytes >= self.modeled_buffer_bytes,
                "reserved bytes cannot be below the requested bytes they round")
        require(not self.memory_components or
                sum(c.requested_bytes for c in self.memory_components) == self.modeled_buffer_bytes,
                "memory components must sum to the modelled buffer bytes")
        if self.resolver_request is not None:
            request = self.resolver_request
            require(request.requested_capacity == self.requested_capacity and
                    request.scheme in ("auto", self.scheme), "resolver request conflicts with resolved capacity/scheme")
            # Auto never resolves to a baseline.
            require(self.scheme not in BASELINE_SCHEMES or request.scheme == self.scheme,
                    "a baseline scheme must be requested explicitly")
            require(request.harness_cores == self.reserved_harness_cores and
                    self.library_threads <= request.cores - request.harness_cores,
                    "resolver request conflicts with resolved thread budget")
            require(not self.cpu_slots or len(self.cpu_slots) == request.cores,
                    "resolver request conflicts with resolved CPU slot budget")
        require(0 < self.requested_capacity <= self.actual_capacity, "invalid worker capacities")
        require(self.library_threads == len(self.threads) and bool(self.threads),
                "worker library role count mismatch")
        require(self.threads[0].role == 0 and self.threads[0].index == 0 and
                all(thread.role != 0 for thread in self.threads[1:]), "worker needs one caller first")
        baseline_pools = {0, BASELINE_POOL_ROLE}
        allowed = {"hierarchical_incremental": {0, 1, 2, 8, 11},
                   "hierarchical_synchronous": {0, 2}, "tree": {0, 4, 5, 6, 9, 12},
                   "std_unordered_map": {0}, "h2o2ram": baseline_pools, "h2o2ram_shipped": baseline_pools,
                   "sonic_zingoram": baseline_pools, "sonic_zingoram_recursive": baseline_pools}[self.scheme]
        require((self.placement_policy == "baseline_self_placed") <= (self.scheme in BASELINE_SCHEMES),
                "only a baseline places itself")
        require(all(thread.role in allowed for thread in self.threads), "role incompatible with worker scheme")
        for role in allowed:
            indices = [thread.index for thread in self.threads if thread.role == role]
            require(indices == list(range(len(indices))), "worker role indices must be contiguous")
        require(len(self.cpu_slots) == len(set(self.cpu_slots)) and
                all(cpu < 2**20 for cpu in self.cpu_slots), "invalid worker CPU slots")
        if self.placement_policy == "unplaced":
            require(not self.cpu_slots and all(t.cpu is None for t in self.threads),
                    "unplaced worker cannot declare CPU assignments")
        else:
            require(len(self.cpu_slots) >= self.library_threads + self.reserved_harness_cores,
                    "worker CPU slots omit library or reserved harness cores")
            require([t.cpu for t in self.threads] == self.cpu_slots[:self.library_threads],
                    "worker thread CPUs differ from slot order")
        require(bool(self.choices) and len({c.field for c in self.choices}) == len(self.choices),
                "worker choices must be nonempty and unique")


@dataclass(frozen=True)
class SharedObject:
    """One object of the worker's dependency closure (doctor)."""
    name: str
    path: Optional[str]      # None when the loader cannot find it
    sha256: Optional[str]    # None when there is no file to hash


@dataclass(frozen=True)
class TscOffsetBound:
    """A CPU's TSC offset from the reference CPU's, bounded by ping-pong causality."""
    cpu: int
    low_ns: float
    high_ns: float


@dataclass(frozen=True)
class NtpState:
    state: Literal["ok", "insert", "delete", "in_progress", "wait", "error"]
    synchronized: bool
    frequency_ppm: float
    max_error_us: int
    estimated_error_us: int


@dataclass(frozen=True)
class ClockCheck:
    """`worker --clock-check`: the TSC against the OS clocks, in the runtime."""
    schema: Literal["clock-check-v1"]
    tsc_hz: float
    window_ms: int
    window_hz: list[float]
    rate_spread_ppm: float
    monotonic_slew_ppm: float
    read_ns: float
    cpu_offsets_ns: list[TscOffsetBound]
    reference_cpu: int
    max_cpu_offset_ns: float
    proven_skews: int
    backwards_on_migration: int
    unplaced_cpus: int
    ntp: NtpState


@dataclass(frozen=True)
class Environment:
    schema_version: Literal[1]
    host_identity: str
    boot_identity: Optional[str]
    environment_class: str
    runtime: Literal["native", "snp", "tdx", "fake"]
    protected_verified: bool
    verification_reference: Optional[str]
    cpu_model: Optional[str]
    physical_cores: Optional[int]
    allowed_cpus: list[int]
    cache_domains: Optional[list[list[int]]]
    memory_limit_bytes: Optional[int]
    build_identity: str
    source_identity: str
    dependency_identity: str
    clock: Literal["monotonic", "tsc_validated", "fake"]
    clock_evidence: Optional[str]
    missing_evidence: list[str]
    topology: Optional[TopologyEvidence] = None
    # Hash of the library headers the frozen worker was built from.
    library_header_identity: Optional[str] = None
    # The worker's compiled-in ISA extensions, the host's flags among them and
    # the clock/wait flags, and the kernel's clocksource (doctor evidence).
    compiled_isa: Optional[list[str]] = None
    cpu_flags: Optional[list[str]] = None
    clock_source: Optional[str] = None
    # What the guest kernel shows, and for a tdx or snp run the boot's
    # attestation capture. A verdict arrives later, beside the capture; this
    # immutable record never claims one (reduce reads it).
    tee: Optional[TeeDetection] = None
    attestation: Optional[AttestationFile] = None
    # The class takes the command line without its boot-disk parameters,
    # the THP modes and the CPU's family/model/stepping (one cloud machine type
    # can run on Granite and Emerald Rapids, and a TD may hide the brand
    # string's detail). Steal ticks
    # since boot and microcode are evidence only.
    kernel_cmdline: Optional[str] = None
    thp_enabled: Optional[str] = None
    thp_defrag: Optional[str] = None
    cpu_family: Optional[int] = None
    cpu_model_number: Optional[int] = None
    cpu_stepping: Optional[int] = None
    microcode: Optional[str] = None
    steal_ticks: Optional[int] = None
    clock_ticks_per_second: Optional[int] = None
    # The shared objects the loader resolves for the worker, hashed; the
    # class's dependency identity is computed from them. And the TSC cross-
    # validation that decides whether `clock` may say tsc_validated.
    dependency_closure: Optional[list[SharedObject]] = None
    clock_check: Optional[ClockCheck] = None
    # Runtime-private memory evidence, separate from process/library memory.
    guest_memory: Optional[GuestMemory] = None

    def validate(self):
        require(self.guest_memory is None or self.guest_memory.validate() is None, "invalid guest memory")
        require(len(self.allowed_cpus) == len(set(self.allowed_cpus)) and
                all(cpu < 2**20 for cpu in self.allowed_cpus), "invalid environment CPU mask")
        require(not self.protected_verified or (self.runtime in ("tdx", "snp") and
                self.verification_reference is not None), "protected verification needs runtime evidence")
        require(self.attestation is None or self.runtime in ("tdx", "snp"),
                "only a tdx or snp environment references an attestation")


@dataclass(frozen=True)
class Artifact:
    path: str
    sha256: str
    bytes: int

    def validate(self):
        require(not self.path.startswith("/") and "\\" not in self.path and
                all(p not in ("", ".", "..") for p in self.path.split("/")), "unsafe artifact path")
        require(len(self.sha256) == 64 and all(c in "0123456789abcdef" for c in self.sha256),
                "invalid sha256")


@dataclass(frozen=True)
class Manifest:
    schema_version: Literal[1]
    trial_id: str
    attempt_id: str
    environment_id: str
    resolved_plan_id: str
    status: Literal["complete", "interrupted", "failed", "invalid", "skipped"]
    # preemption: a coordinator-initiated stop or an attempt orphaned by a dead
    # coordinator; bounded separately from worker-side infrastructure failures.
    # configuration: a native worker resolved or placed differently from
    # resolution.json; deterministic, so terminal.
    # time_cap: the worker outlived max_trial_ns and was killed; terminal, since
    # a rerun would only spend another cap.
    failure_kind: Optional[Literal["infrastructure", "preemption", "correctness", "stash", "logging", "resource",
                                   "configuration", "time_cap"]]
    reason: Optional[str]
    artifacts: list[Artifact]
    events: int
    lost_events: int
    correctness_verified: bool
    measurement_begin_ns: Optional[int]
    measurement_end_ns: Optional[int]
    drain_end_ns: Optional[int]
    # A complete `off` trial is valid and visibly unverified.
    verification: Literal["full", "off"] = "full"

    def validate(self):
        require(len({a.path for a in self.artifacts}) == len(self.artifacts), "duplicate artifact path")
        if self.status == "complete":
            require(self.correctness_verified == (self.verification == "full") and
                    self.lost_events == 0 and self.failure_kind is None,
                    "complete trial must pass correctness (unless verification is off, "
                    "when it cannot claim it) and logging")
            require(bool(self.artifacts), "complete trial must reference raw artifacts")
            require(self.measurement_begin_ns is not None and self.measurement_end_ns is not None and
                    self.drain_end_ns is not None and
                    self.measurement_begin_ns < self.measurement_end_ns <= self.drain_end_ns,
                    "complete trial needs valid measurement/drain boundaries")



SCHEMAS = {"campaign": Campaign, "overrides": Overrides, "worker-resolution": WorkerResolution,
           "environment": Environment, "manifest": Manifest, "attestation": AttestationCapture,
           "attestation-verdict": AttestationVerdict}
