#!/usr/bin/env python3
"""Hierarchy replay battery: native engine runs against the trusted model.

    python3 oracle/hierarchy_replay_tests.py [--no-generate] [--no-selected] [-j N]
        [--report FILE] [--summary FILE]

1. Regenerates the fixture battery with oracle/gen_hierarchy_fixtures.sh
   (which builds the dumper, oracle/build_hierarchy_dump.sh) into
   .lake/oracle/hierarchy/ (HIERARCHY_FIXTURES overrides), unless
   --no-generate.
2. Builds the oracle (`lake build oracle`) and runs
   `oracle --hierarchy` on every fixture in parallel (one process per file):
   every published table lane-exact against the model, the failure checks of
   HIERARCHY_REPLAY_SCHEMA.md, the theorems' premises on the observed trace
   (`trace_premises`: TracePremises; `unsh_promise`: UnshPromise, exact at
   the run's words and in its word-independent sufficient form), the
   evidence's completeness (`evidence`), and for the forced-failure fixtures
   the job the engine named against the expected one.
   The trace premises are recomputed here independently from the fixture; a
   fixture passes when the oracle's failure reasons are exactly the premise
   violations recomputed here (forced keys past N = 32 T, by construction of
   a forced top overflow) and every such key is a forced one.  The battery
   fails if no flagged tombstone reaches a carry's tier (a vacuous exact form).
   *Fail closed*, per fixture, besides the
   oracle's own `evidence.*` checks: the oracle's line exists (no MALFORMED);
   compared = tables - skipped_top, with skipped_top the number of top tables
   at a selected run and 0 elsewhere; the dumper's `checks.failures` is empty;
   `shapes.init` is present for initialization and `init_shape_differs`
   agrees with the emitted shapes; every
   fixture records the view of both engines (`config.view`,
   `config.sync_check`), and each engine's view records every completed
   operation (the arena: `outcome.accesses`; the synchronous engine: up to its
   own failure, `checks.sync.sync_failure.access`); `key_bound` is the
   engine's address space.
3. Mutation tests on copies of passing fixtures (.lake/oracle/hierarchy-mutations/),
   each with the failure reasons it must and may produce: a main lane's
   value changed, a tier record dropped, two main lanes swapped, a unit
   record changed and a word changed (tables); a key repeated in a unit
   (nodup), an ordinal over the load bound (load), N lowered below a unit
   key and a unit key moved past N (keys), a repeated initialization key
   (init_nodup), and the unshadowed bit set on a carry tombstone that shadows
   a live older copy (unsh_promise, in the tier: exact and sufficient; in the
   main: sufficient) must FAIL (exit 1); an unmodified copy must PASS; a
   truncated file and a fixture missing a word family must be MALFORMED
   (exit 2).
   *The adversary's view* (every fixture; OnlineDiff.lean): the line's
   `online` object must be present and pass for both engines (touched bucket
   and real flag of every access and plan entry against the model's
   `touched`/`isReal`, traceOf against the captured units, the schedule
   premises, the plan identities, OnlineFresh's one-real-probe-per-(family,
   key), the synchronous plans against `syncSchedule`, every completed
   operation recorded, the dummy counters one chain); the battery prints and
   totals the compared entries.  At the selected configurations the top's
   contents are not evaluated: every plan's top entry is its last, so no
   compared quantity reads them (`top_order` otherwise); the top entries'
   buckets and real flags are compared.
   View mutations on the mutation base must FAIL with their reason: a touched
   bucket changed (online.arena.view), a real flag flipped (online.arena.real),
   a dummy word changed at a dummy entry (online.arena.view), a plan entry
   dropped or two entries reordered (online.arena.schedule), a synchronous
   plan's consumption mark changed (online.sync.sync_schedule), a probing
   operation turned into an unprobed write (online.*.kinds), and a unit record
   moved to another lane (online.units).
   *The batch path* (k_batch_*, j_selected_*_batch, s2_share_batch_*,
   OnlineBatchDiff.lean): the `online` object is the batch model's
   (`"model":"OnlineBatch"`, per slot, chunk by chunk, plus the chunk checks);
   on every scalar view the line also carries `online_batch` (the same view
   through the batch model, BatchScalar), which must pass with the scalar
   replay's counts (its reasons `online_batch.*` are matched as `online.*`).
   Batch-view mutations on BATCH_BASE must FAIL with their reason: a lane's
   touched bucket (online.arena.view), a duplicate lane claimed real
   (online.arena.real), a duplicate lane's dummy word (online.arena.view), a
   lane recording another plan than its chunk (online.arena.chunks), a
   chunk's plan with its first hashed table dropped (online.arena.schedule), a
   synchronous chunk's consumption mark (online.sync.sync_schedule), a chunk
   record removed and a chunk lane turned into write_np (online.arena.chunks),
   and a superseded lane given a record in a captured frozen unit (online.units).
   *Vacuity probes* (`vacuity_mutations`; probes that gut a fixture's
   evidence, plus one per completeness check): fixtures with evidence removed -- no tables, three
   tables, contents nulled below or at the top outside a selected run, the
   view or one engine's view removed, accesses emptied or truncated, probing
   operations turned into unrecorded writes, `audit_violations`, `ops`,
   `checks` or `outcome.levels` removed, units cut, a lazy run's levels
   zeroed, `key_bound` raised, a batch fixture read as scalar or with its
   chunks removed, the initialization shape missing or invalid, a selected run's
   level-two contents nulled or its skip flag cleared, a selected plan with
   its top entry first -- each must be rejected (exit 1 with its reason, or
   MALFORMED with its message).
4. The shapes check (spec_tests/HierarchyReplayShapes.lean) on the selected
   fixtures (every job geometry, and the initialization's against the
   preparation's, T7), and on copies with one separated row changed and with
   the initialization's drain changed (each must fail).
5. Word independence of the schedule: every pair s2_*_a / s2_*_b runs one
   operation sequence under two engine secrets; both engines' plan schedules
   (every access's plan, counter and real/dummy pattern, every chunk), the
   units, the outcome and every table's descriptor and record set must be
   identical, while the words and some touched buckets differ (so the two
   secrets really differ).  The pairs cover kHandOver eager and lazy and the
   engine's default inline policy kAuto (kShare), scalar and batch.

--report FILE writes the run's machine-readable record (default
.lake/oracle/hierarchy-report.json); --summary FILE also writes the summary
(oracle/hierarchy_battery_summary.py) from it.  Exit status 0 when every
expectation holds, 1 otherwise. Standard library only; safe under
`python3 -I`.
"""

import argparse
import concurrent.futures
import copy
import datetime
import json
import os
import runpy
import shlex
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(HERE)
ORACLE = os.path.join(LEAN, ".lake", "build", "bin", "oracle")

# Shared with the generator; runpy also works under Python's isolated mode.
MANIFEST = runpy.run_path(os.path.join(HERE, "hierarchy_fixture_manifest.py"))
EXPECTED_FAILURES = MANIFEST["EXPECTED_FAILURES"]
SELECTED = MANIFEST["SELECTED"]
CASES = {case["name"]: case for case in MANIFEST["FIXTURES"]}

# The fixture the mutations start from: uninitialized, three levels, with main and
# tier records (forced collisions fill tiers; most unforced tables have none),
# keys below N, and flagged and unflagged tombstones in a top carry's tier.
MUTATION_BASE = "u_unsh_b8l3d8"
# An initialized fixture (the initialization input's mutations).
INIT_BASE = "g_init_b2l3d2"
# A lazily driven fixture (the levels' state at the stop).
LAZY_BASE = "l_lazy_b4l3d4"
# The fixture the batch-view mutations start from: AccessBatch calls of varying
# size split at unit and prefix ends, repeated keys inside aligned chunks,
# and scalar operations (WriteWithoutProbe included) between the calls.
BATCH_BASE = "k_batch_b2l3d2_mix"
# The selected fixture of the selected-run mutations.
SELECTED_BASE = "j_selected_uniform"

# What a changed trace may also move outside the view replay.
SIDE_ALL = {"tables", "failure_check", "unsh_promise.exact", "unsh_promise.sufficient",
            "trace_premises.nodup"}
# What a changed trace or word may also move in the view replay.
ONLINE_SIDE = {f"online.{e}.{c}" for e in ("arena", "sync") for c in ("view", "real", "fresh")} | \
    {"online.units"}
# A mutation whose reasons beyond its `must` are not constrained.
ANY = None


def unsh_bit(fx):
    """The unshadowed flag's bit in a stored value: meta bit 0x20."""
    return 8 * (fx["config"]["value_bytes"] - 1) + 5


def premise_violations(fx):
    """TracePremises recomputed from the fixture, independently of the oracle:
    the names of the violated conjuncts, and the unit keys >= N."""
    c = fx["config"]
    n = c.get("key_bound", c.get("address_space"))
    bound = c["load"] * c["carry1"]
    bad, past = set(), set()
    if n > 2 ** 27 or ("address_space" in c and n > c["address_space"]):
        bad.add("trace_premises.N")
    for o in fx["units"]:
        recs = 0
        for u in o["units"]:
            keys = [r["key"] for r in u if r is not None]
            if len(keys) != len(set(keys)):
                bad.add("trace_premises.nodup")
            recs += len(keys)
            past.update(k for k in keys if k >= n)
        if recs > bound:
            bad.add("trace_premises.load")
    if past:
        bad.add("trace_premises.keys")
    ik = [r["key"] for r in fx["init"]]
    if len(ik) != len(set(ik)):
        bad.add("trace_premises.init_nodup")
    if any(k >= n for k in ik):
        bad.add("trace_premises.init_keys")
    return bad, past


def levels_of(fx):
    return len(fx["config"]["fanouts"]) + 1


def fixture_facts(name, fx):
    """What the summary and the fail-closed checks read from a fixture itself."""
    c = fx["config"]
    L = levels_of(fx)
    out = fx["outcome"]
    loads = []
    for o in fx["units"]:
        loads.append(sum(1 for u in o["units"] for r in u if r is not None))
    tables_by_level = {}
    top_tables = 0
    for t in fx["tables"]:
        lvl = t["owner"] - 1 if t["slot_kind"] == "inbox" else t["owner"]
        tables_by_level[lvl] = tables_by_level.get(lvl, 0) + 1
        if lvl == L:
            top_tables += 1
    sync_fail = ((fx.get("checks") or {}).get("sync") or {}).get("sync_failure")
    acc = out["accesses"]
    expected = {"arena": acc,
                "sync": min(acc, sync_fail["access"]) if sync_fail else acc}
    view = fx.get("view") or {}
    recorded = {e: (len(view[e]["accesses"]) if view.get(e) else None) for e in ("arena", "sync")}
    return {
        "name": name,
        "selected": c.get("selected"),
        "batch": c.get("batch", 0) != 0,
        "drive": c.get("drive", "eager"),
        "policy": c.get("flush_policy"),
        "initialized": c["initialized"],
        "forced": any(op.get("forced") for op in fx["ops"]),
        "native_failure": out["failure"] is not None,
        "two_secret": name.startswith("s2_"),
        "secret": c.get("secret_seed"),
        "fanouts": c["fanouts"],
        "levels": L,
        "accesses": acc,
        "prefixes": out["prefixes"],
        "load_bound": c["load"] * c["carry1"],
        "load_max": max(loads) if loads else 0,
        "load_ordinals_at_bound": sum(1 for x in loads if x == c["load"] * c["carry1"]),
        "load_ordinals": len(loads),
        "tables_by_level": {str(k): v for k, v in sorted(tables_by_level.items())},
        "top_tables": top_tables,
        "checks_failures": (fx.get("checks") or {}).get("failures"),
        "init_equals_prep": fx["shapes"].get("init") == fx["shapes"].get("prep"),
        "view": c.get("view"), "sync_check": c.get("sync_check"),
        "key_bound": c.get("key_bound"), "address_space": c.get("address_space"),
        "expected_recorded": expected, "recorded": recorded,
    }


def kind_of(f):
    """The battery's partition of runs (the summary's kinds)."""
    if f["selected"]:
        return "selected (batch)" if f["batch"] else "selected (scalar)"
    if f["two_secret"]:
        return "two-secret (batch)" if f["batch"] else "two-secret (scalar)"
    return "small (batch)" if f["batch"] else "small (scalar)"


def norm(reasons):
    """The same view through the batch model (`online_batch`, on a scalar view)
    reports the scalar replay's reasons under `online_batch.*`; the mutation
    expectations name them once, as `online.*`."""
    return {"online." + r[len("online_batch."):] if r.startswith("online_batch.") else r
            for r in reasons}


def run_oracle(item):
    """One oracle run on (path, mode): (exit code, parsed JSON line or None,
    seconds, stderr)."""
    path, mode = item
    t0 = time.time()
    p = subprocess.run([ORACLE, mode, path], capture_output=True, text=True)
    dt = time.time() - t0
    line = p.stdout.strip().splitlines()[-1] if p.stdout.strip() else ""
    try:
        out = json.loads(line) if line else None
    except ValueError:
        out = None
    return p.returncode, out, dt, p.stderr.strip()


def run_parallel(items, jobs):
    """Run the oracle on (path, mode) items, the slowest-looking (largest) first."""
    order = sorted(items, key=lambda it: -os.path.getsize(it[0]))
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
        return dict(zip(order, ex.map(run_oracle, order)))


def named_of(out):
    n = (out or {}).get("failure_detail", {}).get("named")
    if not isinstance(n, dict):
        return None
    return (n.get("job"), n.get("level"), n.get("ordinal"))


def fail_closed(name, fx, facts, out):
    """The driver's own completeness checks of one fixture's line."""
    notes = []
    args = CASES[name]["args"]
    selected = args[args.index("--selected") + 1] if "--selected" in args else None
    if facts["selected"] != selected or facts["batch"] != ("--batch" in args):
        notes.append("selected/batch configuration does not match the manifest case")
    sel = facts["selected"] is not None
    skipped = out.get("skipped_top")
    want_skip = facts["top_tables"] if sel else 0
    if skipped != want_skip:
        notes.append(f"skipped_top {skipped} != {want_skip}")
    if out.get("compared") != out.get("tables", -1) - (skipped or 0) or out.get("unread", 0) != 0:
        notes.append(f"compared {out.get('compared')} != tables {out.get('tables')} - skipped {skipped}")
    if out.get("tables") != len(fx["tables"]):
        notes.append("tables counted != fixture tables")
    if facts["checks_failures"] != []:
        notes.append(f"dumper checks.failures {facts['checks_failures']}")
    if out.get("init_shape_differs") != (not facts["init_equals_prep"]):
        notes.append(f"init_shape_differs {out.get('init_shape_differs')}")
    if (out.get("evidence") or {}).get("result") != "pass":
        notes.append("evidence not pass")
    if facts["view"] is not True or facts["sync_check"] is not True:
        notes.append("config.view / config.sync_check not set")
    if facts["key_bound"] != facts["address_space"]:
        notes.append("key_bound is not the address space")
    on = out.get("online")
    if on is None:
        notes.append("no view replay")
        return notes
    for eng in ("arena", "sync"):
        x = on.get(eng)
        if x is None:
            notes.append(f"no {eng} view")
            continue
        exp = facts["expected_recorded"][eng]
        rec = (x.get("recorded") or {}).get("records")
        if rec != exp or facts["recorded"][eng] != exp:
            notes.append(f"{eng}: {rec} recorded, {exp} expected")
        if (x.get("counters") or {}).get("result") != "pass":
            notes.append(f"{eng}: counters")
        if sel and x.get("top_entries", 0) == 0:
            notes.append(f"{eng}: no top entry compared at a selected run")
    batch = on.get("model") == "OnlineBatch"
    if batch != facts["batch"]:
        notes.append("view model does not match config.batch")
    if batch and on.get("chunks", 0) == 0:
        notes.append("a batch view without chunks")
    if not batch:
        # BatchScalar on this run: the batch model's replay of the scalar
        # view must pass and agree with the scalar model's, entry for entry
        ob = out.get("online_batch")
        if ob is None or ob.get("result") != "pass":
            notes.append("online_batch missing or failing")
        else:
            for eng in ("arena", "sync"):
                x, y = on.get(eng), ob.get(eng)
                if x is None or y is None or any(
                        x[k] != y[k] for k in ("probing", "entries", "real", "engine_real")):
                    notes.append(f"online_batch ({eng}) differs from online")
    return notes


VKEYS = ("fixtures", "arena_accesses", "arena_entries", "arena_real", "sync_accesses", "sync_entries",
         "sync_real", "mismatches", "sync_compared", "units", "chunks", "chunk_lanes",
         "arena_duplicate_lanes", "sync_duplicate_lanes", "plans", "scalar_batch_checked",
         "arena_top_entries", "sync_top_entries")


def battery(fixture_dir, jobs, report, include_selected=True):
    names, ignored, notes = MANIFEST["inventory"](fixture_dir, include_selected)
    report["inventory"] = {"expected": names, "ignored_selected": ignored, "notes": notes,
                           "ok": not notes}
    if notes:
        for note in notes:
            print("inventory: " + note)
        return False
    if not names:
        print(f"no fixtures in {fixture_dir}")
        return False
    paths = [os.path.join(fixture_dir, n + ".json") for n in names]
    t0 = time.time()
    results = run_parallel([(p, "--hierarchy") for p in paths], jobs)
    wall = time.time() - t0
    ok = True
    totals = {"finishes": 0, "unsh_checked": 0, "flagged_tier": 0, "unflagged_tier": 0,
              "unflagged_shadowing": 0}
    vtot = {}  # kind -> counts
    vrows = []
    rows = []
    print(f"{'fixture':28} {'result':9} {'compared':>9} {'mism':>5} {'jobs':>5} "
          f"{'failure':8} {'named job':28} {'secs':>6} {'premises':18} "
          f"{'unsh: fin b/tier/neg':22}")
    for name, path in zip(names, paths):
        code, out, dt, err = results[(path, "--hierarchy")]
        with open(path) as f:
            fx = json.load(f)
        facts = fixture_facts(name, fx)
        kind = kind_of(facts)
        row = {"name": name, "kind": kind, "facts": facts, "exit": code, "seconds": round(dt, 2)}
        rows.append(row)
        if out is None or "result" not in out:
            print(f"{name:28} NO OUTPUT (exit {code}) {(out or {}).get('error', err)[:300]}")
            row["ok"] = False
            ok = False
            continue
        named = named_of(out)
        verdict = out.get("result")
        notes = []
        expect, past = premise_violations(fx)
        forced = {op["key"] for op in fx["ops"] if op.get("forced")}
        reasons = set(out.get("failures", []))
        good = True
        if reasons != expect:
            notes.append(f"failures {sorted(reasons)} != expected {sorted(expect)}")
            good = False
        if past - forced:
            notes.append(f"unforced keys >= N: {sorted(past - forced)[:5]}")
            good = False
        if code != (1 if expect else 0) or verdict != ("fail" if expect else "pass"):
            good = False
        tp = out.get("trace_premises", {})
        prem = "pass" if tp.get("result") == "pass" else \
            ",".join(r.split(".")[1] for r in sorted(reasons) if r.startswith("trace_premises")) + \
            (" (forced)" if past and not past - forced else "")
        up = out.get("unsh_promise", {})
        if up.get("result") == "n/a":
            unsh = "n/a"
        else:
            ex, sf = up.get("exact", {}), up.get("sufficient", {})
            unsh = (f"{up.get('finishes')} {sf.get('flagged_in_b')}/{ex.get('flagged_in_b_tier')}/"
                    f"{ex.get('unflagged_shadowing_in_b_tier')} {up.get('result')}")
            totals["finishes"] += up.get("finishes", 0)
            totals["unsh_checked"] += up.get("unsh_checked", 0)
            totals["flagged_tier"] += ex.get("flagged_in_b_tier", 0)
            totals["unflagged_tier"] += ex.get("unflagged_shadowing_in_b_tier", 0)
            totals["unflagged_shadowing"] += up.get("unflagged_shadowing", 0)
        if name in EXPECTED_FAILURES and named != EXPECTED_FAILURES[name]:
            notes.append(f"expected named job {EXPECTED_FAILURES[name]}")
            good = False
        if name not in EXPECTED_FAILURES and out.get("native_failure") is not None:
            notes.append("unexpected native failure")
            good = False
        fc = fail_closed(name, fx, facts, out)
        if fc:
            notes += fc
            good = False
        on = out.get("online") or {}
        batch = on.get("model") == "OnlineBatch"
        vt = vtot.setdefault(kind, {k: 0 for k in VKEYS})
        if on:
            vt["fixtures"] += 1
            vt["units"] += on["units"]["ordinals"]
            if not batch and (out.get("online_batch") or {}).get("result") == "pass":
                vt["scalar_batch_checked"] += 1
            vr = [name]
            for eng in ("arena", "sync"):
                x = on.get(eng)
                if x is None:
                    vr.append("-")
                    continue
                vt[eng + "_accesses"] += x["probing"]
                vt[eng + "_entries"] += x["entries"]
                vt[eng + "_real"] += x["real"]
                vt[eng + "_top_entries"] += x.get("top_entries", 0)
                vt["mismatches"] += x["bucket_mismatches"] + x["real_mismatches"]
                vt["plans"] += x["plans"]
                if "sync_schedule" in x:
                    vt["sync_compared"] += x["sync_schedule"]["compared"]
                if batch:
                    vt["chunks"] += x["chunks"]
                    vt["chunk_lanes"] += x["chunk_lanes"]
                    vt[eng + "_duplicate_lanes"] += x["duplicate_lanes"]
                vr.append(f"{x['drive']:5} {x['probing']:>6}/{x['entries']:<6} real {x['real']:>6} "
                          f"mism {x['bucket_mismatches']}/{x['real_mismatches']} "
                          f"prem {x['schedule_premises']['result']} fresh {x['fresh']['duplicates']}"
                          + (f" sync-sched {x['sync_schedule']['differ']}" if "sync_schedule" in x else "")
                          + (f" chunks {x['chunks']} lanes {x['chunk_lanes']} dup {x['duplicate_lanes']}"
                             if batch else "")
                          + (f" top {x.get('top_entries', 0)}" if facts["selected"] else ""))
            vrows.append(vr)
            for eng in ("arena", "sync"):
                for m in (on.get(eng) or {}).get("first_mismatches", [])[:3]:
                    print(f"    view mismatch ({eng}):", json.dumps(m)[:300])
        ok &= good
        row["ok"] = good
        row["notes"] = notes
        row["line"] = {k: out.get(k) for k in ("result", "failures", "tables", "compared", "skipped_top",
                                               "mismatches", "jobs_evaluated", "init_shape_differs",
                                               "failure_check")}
        row["trace_premises"] = {"result": tp.get("result"), "keys": tp.get("keys"),
                                 "load": {k: (tp.get("load") or {}).get(k)
                                          for k in ("max_records", "bound", "violations")},
                                 "N": tp.get("N")}
        row["unsh_promise"] = {"result": up.get("result"), "finishes": up.get("finishes"),
                               "unsh_checked": up.get("unsh_checked"),
                               "flagged_in_b_tier": (up.get("exact") or {}).get("flagged_in_b_tier"),
                               "unflagged_shadowing_in_b_tier":
                                   (up.get("exact") or {}).get("unflagged_shadowing_in_b_tier"),
                               "unflagged_shadowing": up.get("unflagged_shadowing")}
        row["view"] = {"model": on.get("model", "Online") if on else None,
                       **{eng: ({k: (on.get(eng) or {}).get(k)
                                 for k in ("probing", "entries", "real", "bucket_mismatches",
                                           "real_mismatches", "plans", "chunks", "chunk_lanes",
                                           "duplicate_lanes", "top_entries")}
                                if on.get(eng) else None) for eng in ("arena", "sync")}}
        compared = f"{out.get('compared')}/{out.get('tables')}"
        print(f"{name:28} {verdict:9} {compared:>9} {out.get('mismatches'):>5} "
              f"{out.get('jobs_evaluated'):>5} {out.get('failure_check'):8} "
              f"{str(named) if named else '-':28} {dt:6.2f} {prem:18} {unsh:22} {' '.join(notes)}")
        for form in ("exact", "sufficient"):
            for v in out.get("unsh_promise", {}).get(form, {}).get("first", [])[:3]:
                print(f"    unsh {form} violation:", json.dumps(v)[:400])
        if reasons - expect:
            for m in out.get("first_mismatches", [])[:3]:
                print("    mismatch:", json.dumps(m)[:300])
            print("    failure:", json.dumps(out.get("failure_detail"))[:400])
            print("    evidence:", json.dumps(out.get("evidence"))[:600])
    npass = sum(1 for p in paths if (results[(p, "--hierarchy")][1] or {}).get("result") == "pass")
    print(f"battery: {npass}/{len(paths)} pass outright, wall {wall:.1f} s with {jobs} processes")
    print(f"unshadowed promise: {totals['finishes']} top finishes, {totals['unsh_checked']} flagged "
          f"carry tombstones checked, {totals['flagged_tier']} of them in a carry's tier (exact form), "
          f"{totals['unflagged_tier']} unflagged tier tombstones shadowing a live C copy, "
          f"{totals['unflagged_shadowing']} unflagged carry tombstones shadowing a live older copy")
    if totals["flagged_tier"] == 0 or totals["unflagged_tier"] == 0:
        print("unshadowed promise: the exact form is vacuous on this battery")
        ok = False
    print(f"\nadversary's view ({sum(v['fixtures'] for v in vtot.values())} fixtures; accesses/entries, "
          f"real probes, bucket/real mismatches):")
    for vr in vrows:
        print(f"  {vr[0]:24} arena {vr[1]}\n  {'':24} sync  {vr[2]}")
    for kind, vt in sorted(vtot.items()):
        print(f"view [{kind}]: {vt['fixtures']} fixtures; arena {vt['arena_accesses']} probing slots, "
              f"{vt['arena_entries']} entries ({vt['arena_real']} real); sync {vt['sync_accesses']} probing "
              f"slots, {vt['sync_entries']} entries ({vt['sync_real']} real); {vt['mismatches']} mismatches; "
              f"{vt['sync_compared']} synchronous plans against syncSchedule; {vt['units']} prefixes "
              f"reproduced by traceOf; chunks {vt['chunks']} (both engines), {vt['chunk_lanes']} chunk "
              f"lanes, duplicate lanes {vt['arena_duplicate_lanes']} + {vt['sync_duplicate_lanes']}; "
              f"top entries {vt['arena_top_entries']} + {vt['sync_top_entries']}; BatchScalar on "
              f"{vt['scalar_batch_checked']} scalar views")
    if not any(v["arena_entries"] for v in vtot.values()):
        print("view: no view compared")
        ok = False
    if not any(v["arena_duplicate_lanes"] for v in vtot.values()):
        print("view: no batch view with duplicate lanes compared")
        ok = False
    report["battery"] = {"fixtures": len(paths), "pass_outright": npass, "wall_seconds": round(wall, 1),
                         "processes": jobs, "unsh_totals": totals, "view_totals": vtot, "runs": rows,
                         "ok": ok}
    return ok


def first_record(lanes):
    for i, r in enumerate(lanes):
        if r is not None:
            return i
    return None


def load_fixture(fixture_dir, name):
    path = os.path.join(fixture_dir, name + ".json")
    if not os.path.exists(path):
        return None
    with open(path) as f:
        return json.load(f)


def mutations(fixture_dir, jobs, report, include_selected=True):
    base_path = os.path.join(fixture_dir, MUTATION_BASE + ".json")
    if not os.path.exists(base_path):
        print(f"mutations: {base_path} missing, skipped")
        return False
    with open(base_path) as f:
        text = f.read()
    base = json.loads(text)
    out_dir = os.path.join(os.path.dirname(fixture_dir.rstrip("/")), "hierarchy-mutations")
    os.makedirs(out_dir, exist_ok=True)
    # name -> (expected exit code, file contents, reasons it must report,
    #          reasons it may report besides (ANY: unconstrained), oracle mode,
    #          for exit 2 a substring of the error)
    cases = {}
    TABLES = {"tables"}
    # A changed trace may move tables and failures; a record the engine never
    # saw (an injected live write) also makes the engine's later unshadowed
    # flags on its key wrong for the mutated trace.
    SIDE = {"tables", "failure_check", "unsh_promise.exact", "unsh_promise.sufficient"}

    def emit(name, fx, expect, must=frozenset(), may=frozenset(), mode="--hierarchy", err=None):
        if name in cases:
            raise ValueError(f"mutation {name} emitted twice")
        cases[name] = (expect, json.dumps(fx, separators=(",", ":")), set(must),
                       None if may is ANY else set(may), mode, err)

    def missing(name):
        cases[name] = (0, "", None, None, "--hierarchy", None)  # reported as missing below

    emit("identity", base, 0)

    # the first table with a main record, and one with a tier record
    def tables_with(pred):
        return [t for t in base["tables"] if t.get("main") is not None and pred(t)]

    with_main = tables_with(lambda t: any(first_record(b) is not None for b in t["main"]))
    with_tier = tables_with(lambda t: first_record(t["tier"] or []) is not None)
    assert with_main and with_tier, "mutation base needs main and tier records"

    fx = copy.deepcopy(base)
    t = next(x for x in fx["tables"] if x["id"] == with_main[0]["id"])
    b = next(i for i, bk in enumerate(t["main"]) if first_record(bk) is not None)
    lane = first_record(t["main"][b])
    t["main"][b][lane]["value"] ^= 1
    emit("main_value", fx, 1, TABLES)

    fx = copy.deepcopy(base)
    t = next(x for x in fx["tables"] if x["id"] == with_tier[0]["id"])
    t["tier"][first_record(t["tier"])] = None
    emit("tier_drop", fx, 1, TABLES)

    # swap a record with a different lane of its bucket (another record or a hole)
    fx = copy.deepcopy(base)
    t = next(x for x in fx["tables"] if x["id"] == with_main[0]["id"])
    b = next(i for i, bk in enumerate(t["main"]) if first_record(bk) is not None)
    i = first_record(t["main"][b])
    j = next(k for k in range(64) if t["main"][b][k] != t["main"][b][i])
    t["main"][b][i], t["main"][b][j] = t["main"][b][j], t["main"][b][i]
    emit("lane_swap", fx, 1, TABLES)

    # change the value of a record of the first ordinal's last unit (the newest
    # version of its key in that ordinal, so level one publishes it); the view
    # replay sees the lane disagree with its operation's value (online.units)
    fx = copy.deepcopy(base)
    unit = fx["units"][0]["units"][-1]
    unit[first_record(unit)]["value"] ^= 1 << 3
    emit("unit_value", fx, 1, TABLES, {"online.units"})

    # change the word of a key of a level-one table under its family: its home moves
    fx = copy.deepcopy(base)
    t = next(x for x in fx["tables"] if x["owner"] == 1 and x["slot_kind"] != "inbox"
             and x["main"] is not None and any(first_record(bk) is not None for bk in x["main"]))
    bk = next(bk for bk in t["main"] if first_record(bk) is not None)
    key = bk[first_record(bk)]["key"]
    w = fx["words"]
    fi = w["families"].index(t["family"])
    ki = w["keys"].index(key)
    w["table"][fi][ki] ^= 1
    emit("word", fx, 1, TABLES, ONLINE_SIDE)

    # a word family the run needs removed: words-missing, malformed
    fx = copy.deepcopy(base)
    w = fx["words"]
    del w["table"][fi]
    del w["families"][fi]
    emit("words_missing", fx, 2, err="words-missing")

    cases["truncated"] = (2, text[: len(text) // 2], set(), set(), "--hierarchy", None)

    # --- the trace premises ------------------------------------------------
    # nodup: a unit's record copied into a free lane of the same unit
    fx = copy.deepcopy(base)
    unit = fx["units"][0]["units"][0]
    src = first_record(unit)
    hole = next(k for k in range(len(unit)) if unit[k] is None)
    unit[hole] = dict(unit[src], value=unit[src]["value"] ^ 1)
    emit("prem_nodup", fx, 1, {"trace_premises.nodup"}, SIDE | ONLINE_SIDE)

    # load: the schema fixes an ordinal at r0 units of 64 s lanes, and
    # 64 r0 s = a U_1 (one slot per access), so no unit-only mutation can
    # exceed the bound; one more flush unit per ordinal (empty but at the
    # fullest ordinal, there 64 s fresh records of keys with words) does
    fx = copy.deepcopy(base)
    lanes = 64 * fx["config"]["stash_buckets"]
    fx["config"]["prefix_flushes"] += 1
    full = max(fx["units"], key=lambda o: sum(r is not None for u in o["units"] for r in u))
    present = {r["key"] for u in full["units"] for r in u if r is not None}
    fresh = [k for k in fx["words"]["keys"] if k not in present][:lanes]
    assert len(fresh) == lanes
    for o in fx["units"]:
        o["units"].append([None] * lanes)
    full["units"][-1] = [{"key": k, "value": 1, "tombstone": False} for k in fresh]
    # (the prefix grows: outcome.prefixes no longer matches the accesses)
    emit("prem_load", fx, 1, {"trace_premises.load"}, SIDE | ONLINE_SIDE | {"evidence.units"})

    # keys: N lowered to the largest unit key (the trace unchanged) ...
    fx = copy.deepcopy(base)
    top_key = max(r["key"] for o in fx["units"] for u in o["units"] for r in u if r is not None)
    fx["config"]["key_bound"] = top_key
    emit("prem_keys_bound", fx, 1, {"trace_premises.keys"})
    # ... and a unit key moved past N (its words copied: same homes, other key)
    fx = copy.deepcopy(base)
    n = fx["config"]["key_bound"]
    unit = fx["units"][0]["units"][-1]
    rec = unit[first_record(unit)]
    w = fx["words"]
    old = w["keys"].index(rec["key"])
    new_key = n + 1
    while new_key in w["keys"]:
        new_key += 1
    w["keys"].append(new_key)
    for row in w["table"]:
        row.append(row[old])
    rec["key"] = new_key
    emit("prem_keys_unit", fx, 1, {"trace_premises.keys"}, SIDE | ONLINE_SIDE)

    # init_nodup: an initialization record repeated (initialized fixture)
    ini = load_fixture(fixture_dir, INIT_BASE)
    if ini is not None:
        fx = copy.deepcopy(ini)
        fx["init"].append(dict(fx["init"][0], value=fx["init"][0]["value"] ^ 1))
        emit("prem_init_nodup", fx, 1, {"trace_premises.init_nodup"}, SIDE | ONLINE_SIDE)
    else:
        missing("prem_init_nodup")

    # --- the unshadowed promise ---------------------------------------------
    # an unflagged tombstone of a top carry whose key is live in the previous
    # top table gets the unshadowed bit in the unit it comes from (the model
    # reads the flag from the units): in the carry's tier the exact form must
    # catch it, in the main the sufficient form; the tables holding it differ
    for part in ("tier", "main"):
        found = unsh_candidate(base, part)
        if found is None:
            print(f"mutation unsh_{part}: no candidate in {MUTATION_BASE}")
            missing(f"unsh_{part}")
            continue
        o_idx, u_idx, lane = found
        fx = copy.deepcopy(base)
        fx["units"][o_idx]["units"][u_idx][lane]["value"] |= 1 << unsh_bit(fx)
        must = {"unsh_promise.exact", "unsh_promise.sufficient"} if part == "tier" \
            else {"unsh_promise.sufficient"}
        emit(f"unsh_{part}", fx, 1, must, TABLES | ONLINE_SIDE)

    # the failure comparison: a forced level-one failure with the engine's
    # failure removed (the model's failing job then has time <= t), or with
    # the named job moved to an ordinal the model completes
    forced = load_fixture(fixture_dir, "i_force_l1")
    if forced is not None:
        fx = copy.deepcopy(forced)
        fx["outcome"]["failure"] = None
        # (without a failure the run must have issued exactly its accesses and
        # settled every level: the completeness checks also object)
        emit("failure_dropped", fx, 1, {"failure_check"}, ANY)
        fx = copy.deepcopy(forced)
        fx["outcome"]["failure"]["ordinal"] -= 1
        emit("failure_renamed", fx, 1, {"failure_check"})
    else:
        missing("failure_dropped")

    view_mutations(base, emit)
    bbase = load_fixture(fixture_dir, BATCH_BASE)
    if bbase is not None:
        batch_view_mutations(bbase, emit)
    else:
        print(f"mutations: {BATCH_BASE} missing")
        missing("batch_base")
    vacuity_mutations(fixture_dir, base, emit, missing, include_selected)

    paths = {}
    ok = True
    for name, (expect, contents, must, may, mode, err) in cases.items():
        if must is None:
            ok = False
            continue
        p = os.path.join(out_dir, f"{name}.json")
        with open(p, "w") as f:
            f.write(contents)
        paths[(p, mode)] = (name, expect, must, may, err)
    t0 = time.time()
    results = run_parallel(list(paths), jobs)
    wall = time.time() - t0
    rows = []
    for item, (name, expect, must, may, err) in sorted(paths.items(), key=lambda kv: kv[1][0]):
        code, out, dt, stderr = results[item]
        reasons = norm(out.get("failures", [])) if out is not None and "failures" in out else set()
        error = (out or {}).get("error", "") if code == 2 else ""
        good = code == expect and must <= reasons and (may is None or reasons <= must | may) and \
            (err is None or err in error)
        ok &= good
        detail = ""
        if out is not None:
            detail = (f"failures={sorted(reasons)} mismatches={out.get('mismatches')}" if "mismatches" in out
                      else f"failures={sorted(reasons)}" if "failures" in out else error[:160])
            up = out.get("unsh_promise", {})
            for form in ("exact", "sufficient"):
                for v in up.get(form, {}).get("first", [])[:1]:
                    detail += f"\n    {form}: finish {v.get('finish')} key {v.get('key')} in {v.get('part')}" \
                              f" live in {v.get('in')}"
        rows.append({"name": name, "exit": code, "expected": expect, "must": sorted(must),
                     "reasons": sorted(reasons), "error": error[:200], "ok": good, "mode": item[1]})
        print(f"mutation {name:28} exit {code} (expected {expect}, must {sorted(must)}"
              f"{', error ' + repr(err) if err else ''}) {'OK' if good else 'UNEXPECTED'} {detail}")
    for name, (expect, contents, must, may, mode, err) in cases.items():
        if must is None:
            print(f"mutation {name:28} MISSING (no base or candidate)")
            rows.append({"name": name, "ok": False, "missing": True})
    print(f"mutations: {sum(1 for r in rows if r['ok'])}/{len(rows)} as expected, wall {wall:.1f} s")
    report["mutations"] = {"cases": rows, "wall_seconds": round(wall, 1), "ok": ok}
    return ok


def vacuity_mutations(fixture_dir, base, emit, missing, include_selected=True):
    """Fixtures with evidence removed (probes that gut a fixture's evidence,
    and one per completeness check): each must be rejected."""
    L = levels_of(base)
    view = base["view"]
    acc = view["arena"]["accesses"]

    # no tables at all; three level-one tables only
    fx = copy.deepcopy(base)
    fx["tables"] = []
    emit("vac_tables_empty", fx, 1, {"evidence.tables"}, ANY)
    fx = copy.deepcopy(base)
    fx["tables"] = [t for t in fx["tables"] if t["owner"] == 1 and t["slot_kind"] != "inbox"][:3]
    emit("vac_tables_three", fx, 1, {"evidence.tables"}, ANY)
    # ... and without the view (and config.view cleared, so the oracle cannot
    # know a view was taken; the driver requires one on every fixture)
    fx = copy.deepcopy(base)
    fx["tables"] = []
    fx["view"] = None
    fx["config"]["view"] = False
    emit("vac_tables_empty_noview", fx, 1, {"evidence.tables"}, ANY)
    # contents nulled: level one's tables, the top's (not a selected run), and the
    # top's with the skip flag set
    fx = copy.deepcopy(base)
    for t in fx["tables"]:
        if t["owner"] == 1 and t["slot_kind"] != "inbox" and t["main"] is not None:
            t["main"] = None
            t["tier"] = None
    emit("vac_level1_contents_null", fx, 1, {"evidence.contents"}, ANY)
    for flag in (False, True):
        fx = copy.deepcopy(base)
        for t in fx["tables"]:
            if t["owner"] == L and t["slot_kind"] != "inbox":
                t["main"] = None
                t["tier"] = None
        fx["config"]["skip_top_contents"] = flag
        emit(f"vac_top_contents_null{'_flagged' if flag else ''}", fx, 1, {"evidence.contents"}, ANY)
    # the whole run cut to its first ordinal: units, tables, view and outcome
    for keep_flag in (True, False):
        fx = copy.deepcopy(base)
        fx["units"] = fx["units"][:1]
        fx["tables"] = [t for t in fx["tables"] if t["owner"] == 1 and t["window"][1] <= 0]
        fx["view"] = None
        fx["outcome"]["last_level_one_ordinal"] = fx["outcome"]["seed_prefixes"]
        if keep_flag:
            emit("vac_gutted", fx, 2, err="view: missing")
        else:
            fx["config"]["view"] = False
            emit("vac_gutted_noview", fx, 1, {"evidence.units"}, ANY)
    # the view: removed, one engine's removed, accesses emptied or truncated
    fx = copy.deepcopy(base)
    fx["view"] = None
    emit("vac_view_null", fx, 2, err="view: missing")
    fx = copy.deepcopy(base)
    del fx["view"]["arena"]
    emit("vac_view_arena_missing", fx, 2, err="view.arena: missing")
    fx = copy.deepcopy(base)
    fx["view"]["sync"] = None
    emit("vac_view_sync_missing", fx, 2, err="view.sync: missing")
    fx = copy.deepcopy(base)
    for e in ("arena", "sync"):
        fx["view"][e]["accesses"] = []
    emit("vac_view_accesses_empty", fx, 1, {"online.arena.recorded", "online.sync.recorded"}, ANY)
    fx = copy.deepcopy(base)
    for e in ("arena", "sync"):
        fx["view"][e]["accesses"] = fx["view"][e]["accesses"][:50]
        fx["view"][e]["recorded"] = 50
    emit("vac_view_truncated", fx, 1, {"online.arena.recorded", "online.sync.recorded"}, ANY)
    # every operation an unprobed write with no access: the units' tombstones
    # (erases) no longer match their operations
    fx = copy.deepcopy(base)
    for e in ("arena", "sync"):
        fx["view"][e]["accesses"] = [None] * len(fx["view"][e]["accesses"])
    for op in fx["ops"]:
        op["op"] = "write_np"
    emit("vac_all_write_np", fx, 1, {"online.units"}, ANY)
    # every write turned into an unrecorded unprobed write: consistent units,
    # but the dummy counters jump where the accesses were removed
    fx = copy.deepcopy(base)
    for j, op in enumerate(fx["ops"]):
        if op["op"] == "write":
            op["op"] = "write_np"
            for e in ("arena", "sync"):
                if j < len(fx["view"][e]["accesses"]):
                    fx["view"][e]["accesses"][j] = None
    emit("vac_writes_unrecorded", fx, 1, {"online.arena.counters", "online.sync.counters"}, ANY)
    # one access's counter moved
    fx = copy.deepcopy(base)
    j = next(j for j, a in enumerate(acc) if a is not None)
    fx["view"]["arena"]["accesses"][j][4] += 1
    emit("vac_counter", fx, 1, {"online.arena.counters"})
    # the probe audit: a violation, and the count removed
    fx = copy.deepcopy(base)
    fx["view"]["arena"]["audit_violations"] = 1
    emit("vac_audit_violation", fx, 1, {"online.arena.audit"})
    fx = copy.deepcopy(base)
    del fx["view"]["arena"]["audit_violations"]
    emit("vac_audit_missing", fx, 2, err="audit_violations")
    # the operations: removed, cut, one more requested
    fx = copy.deepcopy(base)
    del fx["ops"]
    emit("vac_ops_missing", fx, 2, err="\"ops\"")
    fx = copy.deepcopy(base)
    fx["ops"] = fx["ops"][: len(fx["ops"]) // 2]
    emit("vac_ops_truncated", fx, 2, err="more recorded")
    fx = copy.deepcopy(base)
    fx["config"]["accesses_requested"] += 1
    emit("vac_accesses_requested", fx, 1, {"evidence.ops"})
    # the dumper's self-checks: one planted, the report removed
    fx = copy.deepcopy(base)
    fx["checks"]["failures"] = ["planted"]
    emit("vac_dumper_check", fx, 1, {"dumper_checks"})
    fx = copy.deepcopy(base)
    del fx["checks"]
    emit("vac_checks_missing", fx, 2, err="\"checks\"")
    # units: the last ordinal dropped; and dropped with the outcome made to agree
    fx = copy.deepcopy(base)
    fx["units"] = fx["units"][:-1]
    emit("vac_units_dropped", fx, 1, {"evidence.units"}, ANY)
    fx = copy.deepcopy(base)
    fx["units"] = fx["units"][:-1]
    fx["outcome"]["prefixes"] -= 1
    fx["outcome"]["last_level_one_ordinal"] -= 1
    emit("vac_units_cut_consistently", fx, 1, {"evidence.units"}, ANY)
    # the levels' state: removed, one level lowered
    fx = copy.deepcopy(base)
    del fx["outcome"]["levels"]
    emit("vac_levels_missing", fx, 2, err="levels")
    fx = copy.deepcopy(base)
    fx["outcome"]["levels"][1]["published"] -= 1
    emit("vac_levels_lowered", fx, 1, {"evidence.levels"}, ANY)
    # N raised past the theorem's 2^27 and past the address space
    fx = copy.deepcopy(base)
    fx["config"]["key_bound"] = 10 ** 12
    emit("vac_key_bound_huge", fx, 1, {"trace_premises.N"}, ANY)
    fx = copy.deepcopy(base)
    fx["config"]["key_bound"] = 2 * fx["config"]["address_space"]
    emit("vac_key_bound_double", fx, 1, {"trace_premises.N"}, ANY)

    # a lazy run whose levels claim nothing published: no completed job to check
    lazy = load_fixture(fixture_dir, LAZY_BASE)
    if lazy is not None:
        fx = copy.deepcopy(lazy)
        for x in fx["outcome"]["levels"]:
            x["published"] = 0
        emit("vac_lazy_levels_zero", fx, 1, {"evidence.levels"}, ANY)
    else:
        missing("vac_lazy_levels_zero")

    # Initialization may have a different drain; missing or invalid geometry fails.
    ini = load_fixture(fixture_dir, INIT_BASE)
    if ini is not None:
        fx = copy.deepcopy(ini)
        fx["shapes"]["init"]["drain_pages"] += 1
        emit("init_distinct_drain", fx, 0)
        fx = copy.deepcopy(ini)
        fx["shapes"]["init"]["k"] = 0
        emit("vac_init_shape_invalid", fx, 2, err="shapes.init")
        fx = copy.deepcopy(ini)
        fx["shapes"]["init"] = None
        emit("vac_init_shape_missing", fx, 2, err="init")
    else:
        missing("init_distinct_drain")
        missing("vac_init_shape_invalid")
        missing("vac_init_shape_missing")

    # batch: read as a scalar run; chunks and lane tags removed; chunks field removed;
    # a chunk's counter base moved
    bbase = load_fixture(fixture_dir, BATCH_BASE)
    if bbase is not None:
        fx = copy.deepcopy(bbase)
        fx["config"]["batch"] = 0
        emit("vac_batch_as_scalar", fx, 2, err="config.batch = 0")
        fx = copy.deepcopy(bbase)
        for e in ("arena", "sync"):
            fx["view"][e]["chunks"] = []
        for op in fx["ops"]:
            op.pop("batch", None)
        emit("vac_batch_unchunked_all", fx, 2, err="no AccessBatch lane")
        fx = copy.deepcopy(bbase)
        del fx["view"]["arena"]["chunks"]
        emit("vac_batch_chunks_missing", fx, 2, err="view.chunks")
        fx = copy.deepcopy(bbase)
        fx["view"]["arena"]["chunks"][1][3] += 1
        emit("vac_batch_counter", fx, 1, {"online.arena.counters"}, ANY)
    else:
        missing("vac_batch_as_scalar")

    # A label must never open the top-skipping exemption on a small run.
    # These cases run even with --no-selected and cover both view entry points.
    for source, label in ((base, "scalar"), (bbase, "batch")):
        if source is None:
            missing("vac_selected_marker_" + label)
            continue
        for marker in ("unknown", "uniform", "half"):
            fx = copy.deepcopy(source)
            fx["config"].update(selected=marker, skip_top_contents=True)
            top = levels_of(fx)
            for table in fx["tables"]:
                level = table["owner"] - (table["slot_kind"] == "inbox")
                if level == top:
                    table["main"] = table["tier"] = None
            for mode in ("--hierarchy", "--online"):
                emit(f"vac_selected_marker_{label}_{marker}_{mode[2:]}", fx, 2,
                     err="config.selected:", mode=mode)

    # the selected runs: a level-two table's contents nulled, the skip flag
    # cleared (both without the view, to keep the hierarchy replay alone), and
    # a plan with its top entry first (the view alone, --online)
    if not include_selected:
        return
    sel = load_fixture(fixture_dir, SELECTED_BASE)
    if sel is None:
        missing("vac_sel_level2_null")
        return
    for shape in ("top", "prep", "init"):
        fx = copy.deepcopy(sel)
        fx["shapes"][shape] = None
        emit("vac_selected_shape_" + shape, fx, 2, err="shapes.selected:")
    lite = copy.deepcopy(sel)
    lite["view"] = None
    lite["config"]["view"] = False
    fx = copy.deepcopy(lite)
    t = next(t for t in fx["tables"] if t["owner"] == 2 and t["slot_kind"] != "inbox" and t["main"] is not None)
    t["main"] = None
    t["tier"] = None
    emit("vac_sel_level2_null", fx, 1, {"evidence.contents"}, ANY)
    fx = copy.deepcopy(lite)
    fx["config"]["skip_top_contents"] = False
    emit("vac_sel_skip_flag_cleared", fx, 1, {"evidence.contents"})
    del lite
    fx = copy.deepcopy(sel)
    v = fx["view"]["arena"]
    j = next(j for j, a in enumerate(v["accesses"]) if a is not None and len(a[1]) >= 2)
    p = v["accesses"][j][0]
    newp = copy.deepcopy(v["plans"][p])
    for k in ("tables", "ids", "families", "windows"):
        newp[k] = newp[k][-1:] + newp[k][:-1]
    v["plans"].append(newp)
    a = v["accesses"][j]
    a[0] = len(v["plans"]) - 1
    for k in (1, 2, 3):
        a[k] = a[k][-1:] + a[k][:-1]
    emit("vac_sel_top_first", fx, 1, {"online.arena.top_order"}, ANY, mode="--online")


def view_mutations(base, emit):
    """Mutations of the recorded view (the arena's unless named): each must fail
    with its reason."""
    if base.get("view") is None:
        emit("view_missing", base, 1, {"online.arena.view"})  # reported as unexpected
        return
    av = base["view"]["arena"]
    acc = av["accesses"]
    # the first access with a dummy entry and a real entry, and the first with
    # a plan of at least two hashed tables
    dummy_at = next((j, i) for j, a in enumerate(acc) if a is not None
                    for i, r in enumerate(a[2]) if r == 0)
    real_at = next((j, i) for j, a in enumerate(acc) if a is not None
                   for i, r in enumerate(a[2]) if r == 1)
    wide = next(j for j, a in enumerate(acc) if a is not None and len(a[1]) >= 2)

    fx = copy.deepcopy(base)
    j, i = real_at
    fx["view"]["arena"]["accesses"][j][1][i] ^= 1
    emit("view_bucket", fx, 1, {"online.arena.view"})

    fx = copy.deepcopy(base)
    j, i = dummy_at
    fx["view"]["arena"]["accesses"][j][2][i] = 1
    emit("view_real_flag", fx, 1, {"online.arena.real"}, {"online.arena.view"})

    fx = copy.deepcopy(base)
    j, i = dummy_at
    fx["view"]["arena"]["accesses"][j][3][i] ^= 1 << 40  # the high bits: the bucket moves
    # a change of the word that keeps the bucket would not be visible; flip low bits too
    fx["view"]["arena"]["accesses"][j][3][i] ^= 1
    emit("view_dummy_word", fx, 1, {"online.arena.view"})

    def edit_plan(fx, eng, j, f_plan, f_acc):
        """Apply f_plan to a copy of access j's plan and f_acc to every access
        using that plan (the copy becomes a new plan for them)."""
        v = fx["view"][eng]
        p = v["accesses"][j][0]
        newp = copy.deepcopy(v["plans"][p])
        f_plan(newp)
        v["plans"].append(newp)
        for a in v["accesses"]:
            if a is not None and a[0] == p:
                a[0] = len(v["plans"]) - 1
                f_acc(a)

    def drop0(p):
        for k in ("tables", "ids", "families", "windows"):
            del p[k][0]

    def drop0a(a):
        for k in (1, 2, 3):
            del a[k][0]

    fx = copy.deepcopy(base)
    edit_plan(fx, "arena", wide, drop0, drop0a)
    emit("plan_drop", fx, 1, {"online.arena.schedule"},
         {"online.arena.view", "online.arena.real", "online.arena.fresh"})

    def swap01(p):
        for k in ("tables", "ids", "families", "windows"):
            p[k][0], p[k][1] = p[k][1], p[k][0]

    def swap01a(a):
        for k in (1, 2, 3):
            a[k][0], a[k][1] = a[k][1], a[k][0]

    fx = copy.deepcopy(base)
    edit_plan(fx, "arena", wide, swap01, swap01a)
    emit("plan_swap", fx, 1, {"online.arena.schedule"},
         {"online.arena.view", "online.arena.real", "online.arena.fresh"})

    if base["view"].get("sync") is not None:
        fx = copy.deepcopy(base)
        sv = fx["view"]["sync"]
        j = next(j for j, a in enumerate(sv["accesses"]) if a is not None and
                 sv["plans"][a[0]]["consumed"] > 0)
        edit_plan(fx, "sync", j, lambda p: p.update(consumed=p["consumed"] - 1), lambda a: None)
        emit("sync_consumed", fx, 1, {"online.sync.sync_schedule"},
             {"online.sync.schedule", "online.sync.view", "online.sync.real", "online.sync.fresh"})

    # a probing operation turned into an unprobed write: the access it recorded
    # no longer belongs to it, and the model's trace is unchanged
    fx = copy.deepcopy(base)
    j = next(j for j, op in enumerate(fx["ops"]) if op["op"] == "write" and acc[j] is not None)
    fx["ops"][j]["op"] = "write_np"
    emit("op_kind", fx, 1, {"online.arena.kinds"},
         {"online.sync.kinds"} | ONLINE_SIDE)

    # a unit record moved to a free lane of its unit: traceOf no longer
    # reproduces the unit (the operation at the free lane inserted another key)
    fx = copy.deepcopy(base)
    unit = fx["units"][0]["units"][0]
    src = first_record(unit)
    hole = next(k for k in range(len(unit)) if unit[k] is None)
    unit[hole], unit[src] = unit[src], None
    emit("unit_lane", fx, 1, {"online.units"}, {"tables"} | ONLINE_SIDE)


def batch_view_mutations(base, emit):
    """Mutations of a batch view (BATCH_BASE, the arena's unless named): each
    must fail with its reason."""
    av = base["view"]["arena"]
    acc, chunks, plans = av["accesses"], av["chunks"], av["plans"]
    ops = base["ops"]
    keys = [op["key"] for op in ops]
    # a chunk with a duplicate lane (an earlier lane of the chunk has its key)
    dup_at = next((c, f + l) for c, (f, m, p, b, call) in enumerate(chunks) for l in range(m)
                  if keys[f + l] in keys[f:f + l] and acc[f + l] is not None and len(acc[f + l][1]) >= 1)
    real_at = next((f + l, i) for (f, m, p, b, call) in chunks for l in range(m)
                   for i, r in enumerate(acc[f + l][2]) if r == 1)

    def emit_b(name, fx, must, may=frozenset()):
        emit("batch_" + name, fx, 1, must, may)

    fx = copy.deepcopy(base)
    t, i = real_at
    fx["view"]["arena"]["accesses"][t][1][i] ^= 1
    emit_b("bucket", fx, {"online.arena.view"})

    # a duplicate lane (all dummy: the engine starts it found) claimed real
    fx = copy.deepcopy(base)
    t = dup_at[1]
    fx["view"]["arena"]["accesses"][t][2][0] = 1
    emit_b("dup_real", fx, {"online.arena.real"}, {"online.arena.view"})

    # a duplicate lane's dummy word changed: its bucket moves
    fx = copy.deepcopy(base)
    fx["view"]["arena"]["accesses"][t][3][0] ^= (1 << 40) | 1
    emit_b("dup_dummy_word", fx, {"online.arena.view"})

    # one lane records another plan of the same length than its chunk
    fx = copy.deepcopy(base)
    v = fx["view"]["arena"]
    c, t = dup_at
    f, m, p, b, call = v["chunks"][c]
    other = next(q for q in range(len(plans)) if q != p and
                 len(plans[q]["tables"]) == len(plans[p]["tables"]))
    v["accesses"][t][0] = other
    emit_b("lane_plan", fx, {"online.arena.chunks"},
           {"online.arena.view", "online.arena.real", "online.arena.fresh", "online.arena.schedule"})

    # a chunk (and its lanes) reads a copy of its plan with the first hashed
    # table dropped: the windows no longer tile
    wide = next(c for c, (f, m, p, b, call) in enumerate(chunks) if len(plans[p]["tables"]) >= 2)
    fx = copy.deepcopy(base)
    v = fx["view"]["arena"]
    f, m, p, b, call = v["chunks"][wide]
    newp = copy.deepcopy(v["plans"][p])
    for k in ("tables", "ids", "families", "windows"):
        del newp[k][0]
    v["plans"].append(newp)
    v["chunks"][wide][2] = len(v["plans"]) - 1
    for l in range(m):
        a = v["accesses"][f + l]
        a[0] = len(v["plans"]) - 1
        for k in (1, 2, 3):
            del a[k][0]
    emit_b("plan_drop", fx, {"online.arena.schedule"},
           {"online.arena.view", "online.arena.real", "online.arena.fresh"})

    # the synchronous engine's chunk reads a plan with one fewer consumed ordinal
    if base["view"].get("sync") is not None:
        fx = copy.deepcopy(base)
        sv = fx["view"]["sync"]
        c = next(c for c, (f, m, p, b, call) in enumerate(sv["chunks"]) if sv["plans"][p]["consumed"] > 0)
        f, m, p, b, call = sv["chunks"][c]
        newp = dict(copy.deepcopy(sv["plans"][p]), consumed=sv["plans"][p]["consumed"] - 1)
        sv["plans"].append(newp)
        sv["chunks"][c][2] = len(sv["plans"]) - 1
        for l in range(m):
            sv["accesses"][f + l][0] = len(sv["plans"]) - 1
        emit_b("sync_consumed", fx, {"online.sync.sync_schedule"},
               {"online.sync.schedule", "online.sync.view", "online.sync.real", "online.sync.fresh"})

    # a chunk record removed: its lanes become scalar operations of the model
    # (the fixture's operations say they went to AccessBatch), and the two
    # engines no longer cut the same chunks
    fx = copy.deepcopy(base)
    del fx["view"]["arena"]["chunks"][dup_at[0]]
    emit_b("unchunked", fx, {"online.arena.chunks"}, {"online.sync.chunks"} | ONLINE_SIDE)

    # a chunk lane turned into a WriteWithoutProbe (a batch has no such lane)
    fx = copy.deepcopy(base)
    fx["ops"][dup_at[1]]["op"] = "write_np"
    emit_b("write_np_lane", fx, {"online.arena.chunks"}, {"online.sync.chunks"} | ONLINE_SIDE)

    # a superseded lane (a later lane of its chunk repeats its key) that the
    # engine inserted non-real within one aligned chunk. Its unit eventually
    # froze and was captured: giving the lane a record makes traceOf disagree.
    # Supersession across a unit end is now excluded by the public chunk rule.
    E = 64 * base["config"]["stash_buckets"]
    r0 = base["config"]["prefix_flushes"]
    seed1 = base["outcome"]["seed_prefixes"]
    units = {o["ordinal"]: o["units"] for o in base["units"]}
    cand = None
    for (f, m, p, b, call) in chunks:
        if m == 0 or f // E != (f + m - 1) // E:
            continue
        for l in range(m):
            t = f + l
            if any(keys[u] == keys[t] for u in range(t + 1, f + m)):
                o = seed1 + 1 + (t // E) // r0
                if o in units and units[o][(t // E) % r0][t % E] is None:
                    cand = (o, (t // E) % r0, t % E, t)
                    break
        if cand:
            break
    if cand is None:
        print(f"mutation batch_superseded: no captured superseded lane in an aligned chunk in {BATCH_BASE}")
        emit_b("superseded", base, {"online.units"})  # reported as unexpected
    else:
        fx = copy.deepcopy(base)
        o, u, lane, t = cand
        op = ops[t]
        meta = 0x80 if op["op"] in ("erase", "read") else 0
        vb = fx["config"]["value_bytes"]
        fx["units"] = [dict(x) for x in fx["units"]]
        rec = {"key": op["key"], "value": (op["value"] if op["op"] == "write" else 0) | (meta << (8 * (vb - 1))),
               "tombstone": op["op"] in ("erase", "read")}
        for x in fx["units"]:
            if x["ordinal"] == o:
                x["units"] = copy.deepcopy(x["units"])
                x["units"][u][lane] = rec
        emit_b("superseded", fx, {"online.units"}, {"tables"} | SIDE_ALL | ONLINE_SIDE)


def unsh_candidate(fx, part):
    """A unit record to flag: the newest version, within a top carry's window, of
    an unflagged tombstone in the carry's PART ("tier" or "main") whose key is
    live in the previous top table. Returns (units index, unit, lane) or None."""
    c = fx["config"]
    levels = len(c["fanouts"]) + 1
    period = 1
    for b in c["fanouts"]:
        period *= b
    bit = unsh_bit(fx)
    tops = [t for t in fx["tables"] if t["owner"] == levels and t["slot_kind"] == "top"
            and t["main"] is not None]
    for t in fx["tables"]:
        if t["owner"] != levels or t["slot_kind"] != "inbox" or t["main"] is None:
            continue
        v = t["family"][1]
        if v < 2:
            continue
        cp = t["window"][1] // v
        prev = [x for x in tops if x["window"][1] == (v - 1) * cp]
        live = {r["key"] for x in prev for bk in x["main"] + [x["tier"]] for r in bk
                if r is not None and not r["tombstone"]}
        recs = [r for r in t["tier"] if r is not None] if part == "tier" else \
            [r for bk in t["main"] for r in bk if r is not None]
        for r in recs:
            if not r["tombstone"] or (r["value"] >> bit) & 1 or r["key"] not in live:
                continue
            # the newest unit record of the key in the carry's window
            best = None
            for oi, o in enumerate(fx["units"]):
                if not (v - 1) * period < o["ordinal"] <= v * period:
                    continue
                for ui, u in enumerate(o["units"]):
                    for li, x in enumerate(u):
                        if x is not None and x["key"] == r["key"]:
                            best = (oi, ui, li)
            if best is not None:
                oi, ui, li = best
                if fx["units"][oi]["units"][ui][li] == r:
                    return best
    return None




def table_records(t):
    """A table's records as a sorted list (main and tier together)."""
    recs = [r for bk in (t["main"] or []) for r in bk if r is not None] + \
        [r for r in (t["tier"] or []) if r is not None]
    return sorted((r["key"], r["value"], r["tombstone"]) for r in recs)


def view_schedule(v):
    """One engine's word-independent record: per recorded operation its plan
    (dereferenced), its first dummy counter and its real/dummy pattern; the
    chunks with their plans dereferenced. The touched buckets and dummy words
    are left out (they move with the words)."""
    plans = v["plans"]
    acc = [None if a is None else (json.dumps(plans[a[0]], sort_keys=True), a[4], tuple(a[2]))
           for a in v["accesses"]]
    chunks = [(f, m, json.dumps(plans[p], sort_keys=True), b, c) for (f, m, p, b, c) in v.get("chunks", [])]
    return acc, chunks


def two_secret(fixture_dir, report):
    """Every pair s2_X_a / s2_X_b: the same operations under two engine
    secrets must give the same plan schedule (both engines), the same
    real/dummy pattern, chunks, units, outcome and tables (descriptors and
    record sets), while the words differ."""
    names = [p + "_a" for p in MANIFEST["PAIRS"]]
    ok = True
    rows = []
    if not names:
        print("two-secret: no pairs")
        report["two_secret"] = {"pairs": [], "ok": False}
        return False
    for na in names:
        nb = na[:-2] + "_b"
        a, b = load_fixture(fixture_dir, na), load_fixture(fixture_dir, nb)
        row = {"pair": na[:-2], "ok": False}
        rows.append(row)
        if a is None or b is None:
            print(f"two-secret {na[:-2]}: {na if a is None else nb} missing")
            ok = False
            continue
        diffs = []
        ca = {k: v for k, v in a["config"].items() if k != "secret_seed"}
        cb = {k: v for k, v in b["config"].items() if k != "secret_seed"}
        if a["config"]["secret_seed"] == b["config"]["secret_seed"]:
            diffs.append("same secret")
        if ca != cb:
            diffs.append("config")
        for k in ("ops", "init", "units", "outcome"):
            if a[k] != b[k]:
                diffs.append(k)
        if a["words"] == b["words"]:
            diffs.append("words identical (the secrets do not differ)")
        desc = ("id", "owner", "slot", "slot_kind", "family", "window", "ident", "seen", "main_buckets",
                "tier_buckets")
        ta, tb = a["tables"], b["tables"]
        placement_differs = 0
        if [{k: t.get(k) for k in desc} for t in ta] != [{k: t.get(k) for k in desc} for t in tb]:
            diffs.append("table descriptors")
        else:
            for x, y in zip(ta, tb):
                if table_records(x) != table_records(y):
                    diffs.append(f"records of table {x['id']}")
                    break
                if (x["main"], x["tier"]) != (y["main"], y["tier"]):
                    placement_differs += 1
        entries = touched_differs = 0
        accesses = {}
        for e in ("arena", "sync"):
            va, vb = (a.get("view") or {}).get(e), (b.get("view") or {}).get(e)
            if va is None or vb is None:
                diffs.append(f"view.{e} missing")
                continue
            sa, sb = view_schedule(va), view_schedule(vb)
            if sa[0] != sb[0]:
                k = next((i for i, (x, y) in enumerate(zip(sa[0], sb[0])) if x != y), min(len(sa[0]), len(sb[0])))
                diffs.append(f"view.{e} schedule (first at operation {k})")
            if sa[1] != sb[1]:
                diffs.append(f"view.{e} chunks")
            accesses[e] = sum(1 for x in va["accesses"] if x is not None)
            for x, y in zip(va["accesses"], vb["accesses"]):
                if x is not None and y is not None:
                    entries += len(x[1])
                    touched_differs += sum(1 for p, q in zip(x[1], y[1]) if p != q)
        if touched_differs == 0:
            diffs.append("no touched bucket differs (the secrets do not reach the view)")
        row.update({"ok": not diffs, "diffs": diffs, "probing": accesses, "entries": entries,
                    "touched_differ": touched_differs, "tables": len(ta),
                    "tables_placed_differently": placement_differs,
                    "drive": a["config"].get("drive"), "policy": a["config"].get("flush_policy"),
                    "batch": a["config"].get("batch", 0) != 0,
                    "secrets": [a["config"]["secret_seed"], b["config"]["secret_seed"]]})
        ok &= not diffs
        print(f"two-secret {na[:-2]:26} {'OK' if not diffs else 'DIFFERS'} drive {row['drive']} policy "
              f"{row['policy']} batch {row['batch']}: probing {accesses}, {entries} plan entries with "
              f"identical plans, counters and real flags ({touched_differs} touched buckets differ); "
              f"{len(ta)} tables with identical descriptors and record sets ({placement_differs} placed "
              f"differently); units, outcome identical {'' if not diffs else diffs}")
    report["two_secret"] = {"pairs": rows, "ok": ok}
    return ok


def shapes(fixture_dir, report):
    sel = [os.path.join(fixture_dir, f) for f in ("j_selected_uniform.json", "j_selected_half.json")
           if os.path.exists(os.path.join(fixture_dir, f))]
    if not sel:
        print("shapes: no selected fixtures, skipped")
        report["shapes"] = {"ok": False}
        return False
    cmd = ["lake", "env", "lean", "--run", "spec_tests/HierarchyReplayShapes.lean"]
    p = subprocess.run(cmd + sel, cwd=LEAN, capture_output=True, text=True)
    print(p.stdout.strip())
    ok = p.returncode == 0
    lines = p.stdout.strip().splitlines()
    # a mutated separated row, and a mutated initialization drain, must be caught
    with open(sel[0]) as f:
        fx = json.load(f)
    out_dir = os.path.join(os.path.dirname(fixture_dir.rstrip("/")), "hierarchy-mutations")
    os.makedirs(out_dir, exist_ok=True)
    muts = {}
    for name, edit in (("sep_row", lambda x: x["shapes"]["sep"][0].update(stash_pages=x["shapes"]["sep"][0]["stash_pages"] + 1)),
                       ("init_drain", lambda x: x["shapes"]["init"].update(drain_pages=x["shapes"]["init"]["drain_pages"] + 1))):
        y = copy.deepcopy(fx)
        edit(y)
        mut = os.path.join(out_dir, f"selected.{name}.json")
        with open(mut, "w") as f:
            json.dump(y, f, separators=(",", ":"))
        q = subprocess.run(cmd + [mut], cwd=LEAN, capture_output=True, text=True)
        caught = q.returncode == 1
        muts[name] = caught
        print(f"shapes mutation ({name}) exit {q.returncode} (expected 1) {'OK' if caught else 'UNEXPECTED'}")
        ok &= caught
    report["shapes"] = {"ok": ok, "lines": lines, "mutations_caught": muts}
    return ok


def git(*args):
    try:
        return subprocess.run(["git", *args], cwd=LEAN, capture_output=True, text=True).stdout.strip()
    except OSError:
        return ""


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--no-generate", action="store_true", help="use the existing fixtures")
    ap.add_argument("--no-selected", action="store_true", help="skip the selected runs")
    ap.add_argument("-j", "--jobs", type=int, default=min(16, os.cpu_count() or 4))
    ap.add_argument("--report", default=os.path.join(LEAN, ".lake", "oracle", "hierarchy-report.json"))
    ap.add_argument("--summary", default=None, help="also write the summary here")
    args = ap.parse_args()
    t_start = time.time()
    fixture_dir = os.environ.get("HIERARCHY_FIXTURES", os.path.join(LEAN, ".lake", "oracle", "hierarchy"))
    report = {"date": datetime.datetime.now().astimezone().isoformat(timespec="seconds"),
              "commit": git("rev-parse", "HEAD"),
              "worktree_clean": git("status", "--porcelain", "--untracked-files=no", "--", ".") == "",
              "command": "python3 oracle/hierarchy_replay_tests.py " + " ".join(shlex.quote(a) for a in sys.argv[1:]),
              "fixture_dir": fixture_dir}
    if not args.no_generate:
        gen = [os.path.join(HERE, "gen_hierarchy_fixtures.sh"), "-j", str(min(args.jobs, 12))]
        if args.no_selected:
            gen.append("--no-selected")
        t0 = time.time()
        if subprocess.run(gen, cwd=LEAN).returncode != 0:
            print("fixture generation failed")
            return 1
        report["generation_seconds"] = round(time.time() - t0, 1)
    if subprocess.run(["lake", "build", "oracle"], cwd=LEAN).returncode != 0:
        print("lake build oracle failed")
        return 1
    ok = battery(fixture_dir, args.jobs, report, not args.no_selected)
    if report["inventory"]["ok"]:
        ok &= mutations(fixture_dir, args.jobs, report, not args.no_selected)
        ok &= two_secret(fixture_dir, report)
        if not args.no_selected:
            ok &= shapes(fixture_dir, report)
    report["total_seconds"] = round(time.time() - t_start, 1)
    report["all_ok"] = bool(ok)
    os.makedirs(os.path.dirname(os.path.abspath(args.report)), exist_ok=True)
    with open(args.report, "w") as f:
        json.dump(report, f, indent=1)
    print(f"report: {args.report}")
    if args.summary:
        r = subprocess.run([sys.executable, "-I", os.path.join(HERE, "hierarchy_battery_summary.py"),
                            args.report, args.summary])
        ok &= r.returncode == 0
    print(f"total {report['total_seconds']} s")
    print("ALL OK" if ok else "SOME CHECKS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
