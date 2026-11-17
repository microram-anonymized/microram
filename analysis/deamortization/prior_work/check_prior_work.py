"""Check the fixed configurations used in the prior-work comparison.

Run from the repository root:
python analysis/deamortization/prior_work/check_prior_work.py
This checks scheduling and reserved record slots, not hash overflow or sort cost.
"""
from collections import defaultdict
from fractions import Fraction as F
import heapq

from simulate import Simulator


def os_cycle(levels):
    """Integrate distinct carry lifetimes over an exact steady-state period."""
    period = 2**levels
    changes = defaultdict(int)
    changes[F(0)] = changes[F(period)] = 0
    for level in range(levels):
        unit = 2**level
        phase = F(4, 3) * (unit - 1)
        for generation in range(-3, period // (2 * unit) + 2):
            first = phase + 2 * unit * generation
            publication = first + F(4, 3) * unit
            for arrival in (first, first + unit):
                start, stop = max(arrival, F(0)), min(publication, F(period))
                if start < stop:
                    changes[start] += 1
                    changes[stop] -= 1
    live = peak = 0
    area = last = F(0)
    for time, delta in sorted(changes.items()):
        area += live * (time - last)
        live += delta
        peak = max(peak, live)
        last = time
    return area / period, peak


def os_event_check(levels=8):
    """Count actual live Source objects in the existing hierarchy simulator."""
    period = 2**levels
    start, end = 4 * period, 8 * period
    sim = Simulator(6, 0, "two", levels=levels, accesses=end + 2 * period)
    previous, area, peak = 0.0, 0.0, 0

    def live_sources():
        sources = []
        for level in sim.levels:
            sources.extend(level.incoming)
            if level.generation:
                sources.append(level.generation.first_src)
                if level.generation.second_src is not None:
                    sources.append(level.generation.second_src)
        return len({id(source) for source in sources})

    live = 0
    while sim.events and sim.now < end:
        time = sim.events[0][0]
        duration = max(0, min(time, end) - max(previous, start))
        area += live * duration
        if duration:
            peak = max(peak, live)
        sim.now = time
        # Drain all events at this instant before observing the lookup state.
        while sim.events and abs(sim.events[0][0] - time) < 1e-10:
            _, _, _, kind, level, token = heapq.heappop(sim.events)
            if kind == "external":
                from simulate import Source
                source = Source(None, None)
                sim.offer(0, source)
                assert source not in sim.levels[0].incoming
            elif kind == "early_done":
                generation = sim.levels[level].generation
                if generation is not None and token == generation.token:
                    sim.update_work(level)
                    sim.schedule_next_work_event(level)
            else:
                sim.finish_generation(level, token)
        live = live_sources()
        previous = time
    assert abs(area / (end - start) - 5 * levels / 6) < 1e-8
    assert peak == levels + 1
    return area / (end - start), peak


def pd_cycle(levels):
    """Published generation recurrence, one resident largest table of size H.

    Each lower height has q=1 or 2 read-only sources and an output of q*P.
    Outputs are charged to their generating job exactly once, including the
    largest replacement. No largest-level outgoing merge is charged.
    """
    largest = 2**levels
    baseline = 2 * largest - 1
    probes, memory = [], []
    for query in range(4 * largest, 6 * largest):
        generation = query
        count = 0
        slots = largest
        for level in range(levels):
            active = 1 + (generation % 2 == 0)
            count += active
            slots += 2 * active * 2**level
            generation = (generation - 1) // 2
        probes.append(count)
        memory.append(slots)
    assert F(sum(probes), len(probes)) == F(3 * levels, 2)
    assert max(probes) == 2 * levels
    assert max(memory) == 5 * largest - 4
    return F(max(memory), baseline), F(sum(probes), len(probes)), max(probes)


def main():
    for levels in range(2, 15):
        average, peak = os_cycle(levels)
        assert average == F(5 * levels, 6)
        assert peak == levels + 1
        pd_cycle(levels)
    print("Exact cyclic sweeps: L=2..14 passed")
    average, peak = os_event_check()
    print(f"Ostrovsky-Shoup, event simulation L=8: average={average:.12g}, peak={peak}")
    for speed, expected in ((5.99, False), (6, True), (6.01, True)):
        actual = Simulator(speed, 0, "two", levels=12, accesses=100_000).run()
        assert actual == expected
    print("Ostrovsky-Shoup, alpha=0: 5.99 stalls; 6 and 6.01 pass")
    # The output is the P-word prefix of the work array, so it is credited
    # once, rather than charging two banks plus another whole array. At load
    # one half the padding step needs P + 2D = 2P words (the earlier 3P/2
    # array fits only at load at most 1/4).
    load = F(1, 2)
    work_array = max(F(3, 2), 1 + 2 * load)
    os_slots = 2 + (work_array - 1)
    assert os_slots == 3
    assert 4 * os_slots == 12
    # Goodrich et al. leave the cuckoo epsilon unspecified, so the paper's table
    # reports the load-one-half limit, expansion c -> 2.
    expansion = F(2)
    goodrich_slots = F(5, 2) + 1 / (2 * expansion)
    assert goodrich_slots == F(11, 4)
    assert 5 * expansion + 1 == 11
    print(f"Fixed per-level hash-rebuild arenas: {os_slots} times baseline")
    print(f"Goodrich tables plus history, expansion->2: {goodrich_slots} times baseline, "
          f"{5 * expansion + 1}N record slots")
    ratio, average, peak = pd_cycle(14)
    print(f"PD-ORAM L=14: storage witness={float(ratio):.9f}, average={average}, peak={peak}")
    print("PD-ORAM deadline compression: (C(2m)/m)/(C(2m)/(2m)) = 2")


if __name__ == "__main__":
    main()
