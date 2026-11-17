"""analysis/allocation_reconcile.py on synthetic audit rows: measured allocations
reconciled against the main-table memory model, with no allocation audit run."""
from pathlib import Path
import contextlib
import io
import json
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "analysis"))
import allocation_reconcile as rec
import level_arena_model as model

K, V, CAP = 8, 48, 65536
W = 59
BUCKET = 64 * W
FAN, D = [4, 8], 8


def slots():
    z = model.ladder_from_capacity(FAN, D, CAP)
    return model.ladder_slots(FAN, D, z, [1, 1, 1], "no-clone")


def synthetic_row(extra_data_bytes=0, drop_data_block=False):
    """An incremental row whose blocks are exactly what the model enumerates."""
    levels = slots()
    mains = [sum(s[1] for s in lv) for lv in levels]
    tiers = [sum(s[2] for s in lv) for lv in levels]
    blocks = []
    for l, (m, t) in enumerate(zip(mains, tiers)):
        size = rec.aligned64_bytes((m + t) * BUCKET) + (extra_data_bytes if l == 2 else 0)
        if not (drop_data_block and l == 1):
            blocks.append(dict(role="arena_combined", where="data", bytes=size, count=1, granted=size))
        blocks.append(dict(role="arena_combined", where="masks", bytes=(m + t) * 8, count=1,
                           granted=(m + t) * 8))
    blocks.append(dict(role="arena_combined", where="tier pool", bytes=sum(tiers) * BUCKET,
                       count=1, granted=sum(tiers) * BUCKET))
    blocks.append(dict(role="scratch", where="s", bytes=1000, count=2, granted=2048))
    blocks.append(dict(role="online_stash", where="d", bytes=500, count=1, granted=512))
    blocks.append(dict(role="metadata", where="m", bytes=300, count=1, granted=320))
    blocks.append(dict(role="harness_runtime", where="h", bytes=104, count=1, granted=104))
    live = sum(b["bytes"] * b["count"] for b in blocks) - 104
    granted = sum(b["granted"] for b in blocks) - 104
    mains_total = 64 * sum(mains) * W
    phase = dict(live_requested=live, live_granted=granted, peak_requested=live + 10,
                 peak_granted=granted + 10, allocations=0, harness_live_requested=104,
                 all_peak_requested=live + 114, hwm=live * 3, rss=live * 2)
    return dict(
        scheme="hierarchical_incremental", capacity=CAP, actual_capacity=CAP, key_bytes=K,
        value_bytes=V, ok=True, constructed=dict(phase), filled=dict(phase), steady=dict(phase),
        leaked_requested=0, blocks=blocks,
        choices={"hierarchy.levels": "3", "hierarchy.fanout.1": "4", "hierarchy.fanout.2": "8",
                 "hierarchy.top_digit": "8", "hierarchy.tier.1": "1", "hierarchy.tier.2": "1",
                 "hierarchy.tier.3": "1", "hierarchy.bank_first": "1"},
        components=[dict(component="hierarchy.mains", bytes=mains_total, coverage="tallied"),
                    dict(component="hierarchy.tiers", bytes=sum(tiers) * BUCKET, coverage="tallied"),
                    dict(component="hierarchy.retained tier holes", bytes=sum(tiers) * BUCKET,
                         coverage="tallied"),
                    dict(component="hierarchy.masks", bytes=sum(mains) * 8, coverage="tallied")]
    ), mains_total


def baseline_row():
    phase = dict(library=dict(live_requested=1000, live_granted=1100, peak_requested=3000,
                              peak_granted=3200, blocks=5, allocations=0),
                 harness=dict(live_requested=40), all_peak_requested=3040, rss=9000, hwm=12000,
                 threads=3)
    return dict(scheme="h2o2ram", build="patched", capacity=100, actual_capacity=128, key_bytes=8,
                value_bytes=8, accesses=200, baseline=dict(live_requested=11, rss=1, hwm=1, threads=1),
                role_attribution="none", filled=phase, steady=phase, leaked_requested=7)


def values(results):
    return {q.name: q for q in results}


class AllocationReconcileTest(unittest.TestCase):
    def test_model_slot_enumeration_matches_main_buckets(self):
        z = model.ladder_from_capacity(FAN, D, CAP)
        self.assertEqual(sum(s[1] for lv in slots() for s in lv),
                         model.ladder_main_buckets(FAN, D, z)["M"])
        # The bank-first run is a tier-only slot over the odd bank.
        runs = [s for lv in slots() for s in lv if s[0] == "run"]
        self.assertEqual(runs, [("run", 0, 1)])

    def test_exact_blocks_reconcile_to_zero(self):
        row, mains = synthetic_row()
        q = values(rec.reduce_row(row))
        self.assertEqual(q["model_main_payload"].value, mains)
        self.assertEqual(q["stored_slot_width_W"].value, W)
        self.assertEqual(q["role_main_payload_bytes"].value, mains)
        self.assertEqual(q["measured_minus_model_main_bytes"].value, 0)
        self.assertEqual(q["role_partition_residual_bytes"].value, 0)
        self.assertEqual(q["role_unattributed_bytes"].value, 0)
        self.assertEqual(q["ladder_level_blocks_found"].value, "3/3")
        live = q["library_live_requested_bytes"].value
        self.assertEqual(q["total_minus_main_bytes"].value, live - mains)
        # Ratios are over requested_capacity*(k+v), then over actual capacity.
        self.assertAlmostEqual(q["library_live_requested_per_requested"].value,
                               live / (CAP * (K + V)))
        self.assertEqual(q["vmhwm_bytes"].value, live * 3)
        self.assertEqual(q["harness_live_requested_bytes"].value, 104)
        # Not the bare payload: the arena bill adds tiers, holes and masks.
        self.assertGreater(q["main_arena_bytes_model"].value, mains)
        self.assertEqual(q["main_arena_minus_bare_payload_bytes"].value,
                         q["main_arena_bytes_model"].value - mains)

    def test_a_larger_level_block_shows_as_a_positive_delta(self):
        row, mains = synthetic_row(extra_data_bytes=4096)
        q = values(rec.reduce_row(row))
        self.assertEqual(q["measured_minus_model_main_bytes"].value, 4096)
        self.assertEqual(q["role_partition_residual_bytes"].value, 0)
        self.assertTrue(any("paired" in x.value for x in rec.reduce_row(row) if x.name == "note"))

    def test_missing_block_is_reported_and_stays_in_the_partition(self):
        row, _ = synthetic_row(drop_data_block=True)
        results = rec.reduce_row(row)
        q = values(results)
        self.assertEqual(q["ladder_level_blocks_found"].value, "2/3")
        self.assertEqual(q["role_partition_residual_bytes"].value, 0)
        self.assertTrue(any("not found" in x.value for x in results if x.name == "note"))

    def test_uncaptured_bytes_are_unattributed_not_guessed(self):
        row, _ = synthetic_row()
        row["filled"]["live_requested"] += 777  # live bytes no block accounts for
        q = values(rec.reduce_row(row))
        self.assertEqual(q["role_unattributed_bytes"].value, 777)
        self.assertEqual(q["role_partition_residual_bytes"].value, 0)

    def test_tree_with_unmatched_arena_is_counted_once(self):
        # Payload planes allocate several arena blocks, none the size of the
        # modeled single `tree.arenas` allocation.  The whole tree role is then
        # reported once (role_tree), not also as metadata.
        phase = dict(live_requested=1100, live_granted=1200, peak_requested=1100,
                     peak_granted=1200, allocations=0, harness_live_requested=0,
                     all_peak_requested=1100, hwm=5000, rss=4000)
        row = dict(scheme="tree", capacity=64, actual_capacity=64, key_bytes=8, value_bytes=256,
                   ok=True, constructed=dict(phase), filled=dict(phase), steady=dict(phase),
                   leaked_requested=0, choices={},
                   components=[dict(component="tree.arenas", bytes=1000, coverage="tallied")],
                   blocks=[dict(role="tree", where="plane0", bytes=500, count=1, granted=512),
                           dict(role="tree", where="plane1", bytes=480, count=1, granted=512),
                           dict(role="position_map", where="pm", bytes=120, count=1, granted=128)])
        q = values(rec.reduce_row(row))
        self.assertEqual(q["role_partition_residual_bytes"].value, 0)
        self.assertEqual(q["role_tree_bytes"].value, 980)
        self.assertEqual(q["role_masks_tags_metadata_bytes"].value, 0)

    def test_null_hwm_reports_no_vmhwm(self):
        # The audit prints a null `hwm` when it could not reset the peak RSS
        # before the row; the process's peak may then be an earlier row's.
        row, _ = synthetic_row()
        for p in ("constructed", "filled", "steady"):
            row[p]["hwm"] = None
        results = rec.reduce_row(row)
        q = values(results)
        self.assertNotIn("vmhwm_bytes", q)
        self.assertTrue(any("VmHWM" in x.value for x in results if x.name == "note"))
        self.assertIn("library_live_requested_bytes", q)

    def test_baseline_row_has_totals_and_no_roles(self):
        q = values(rec.reduce_row(baseline_row()))
        self.assertEqual(q["role_attribution"].value, "none")
        self.assertEqual(q["main_payload"].value, "n/a")
        self.assertEqual(q["library_peak_requested_bytes"].value, 3000)
        self.assertAlmostEqual(q["library_peak_requested_per_requested"].value, 3000 / (100 * 16))
        self.assertAlmostEqual(q["library_peak_requested_per_actual"].value, 3000 / (128 * 16))
        self.assertEqual(q["vmhwm_bytes"].value, 12000)
        self.assertNotIn("role_main_payload_bytes", q)

    def test_files_and_outputs(self):
        row, _ = synthetic_row()
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "a.jsonl"
            path.write_text("AUDIT_ROW " + json.dumps(row) + "\nALLOC_AUDIT "
                            + json.dumps(baseline_row()) + "\nnoise\n")
            rows = rec.load_rows(str(path))
            self.assertEqual(len(rows), 2)
            results = [(rec.rowid(r), rec.reduce_row(r)) for r in rows]
            csv_text = rec.to_csv(results)
            self.assertTrue(csv_text.startswith("row,quantity,value,unit,basis,note"))
            self.assertIn("measured_minus_model_main_bytes", csv_text)
            self.assertIn("### h2o2ram/k8:v8/N100", rec.to_markdown(results))

    def test_live_over_model_is_total_minus_main_when_every_level_matches(self):
        row, mains = synthetic_row()
        q = values(rec.reduce_row(row))
        live = q["library_live_requested_bytes"].value
        self.assertAlmostEqual(q["library_live_over_model_main"].value, live / mains)
        self.assertAlmostEqual(100 * (q["library_live_over_model_main"].value - 1),
                               q["total_minus_main_pct_of_main"].value)
        self.assertAlmostEqual(q["library_live_minus_model_main_pct"].value,
                               q["total_minus_main_pct_of_main"].value)

    def test_unnamed_sites_give_a_note_not_a_traceback(self):
        # A default (PIE) build names no site: every block is unattributed, no
        # level block matches, and the counted main would be zero.
        row, mains = synthetic_row()
        for b in row["blocks"]:
            b["role"], b["where"] = "unattributed", "?"
        results = rec.reduce_row(row)
        q = values(results)
        notes = [x.value for x in results if x.name == "note"]
        self.assertEqual(q["ladder_level_blocks_found"].value, "0/3")
        self.assertIn(rec.NO_SITE_NAMES, notes)
        self.assertIn(rec.NO_LEVEL_MATCH, notes)
        self.assertFalse(any("not found" in n for n in notes))
        self.assertNotIn("total_minus_main_pct_of_main", q)
        self.assertNotIn("role_main_payload_bytes", q)
        self.assertEqual(q["role_partition_residual_bytes"].value, 0)
        live = q["library_live_requested_bytes"].value
        self.assertEqual(q["role_unattributed_bytes"].value, live)
        # The model ratio needs no site names.
        self.assertAlmostEqual(q["library_live_over_model_main"].value, live / mains)
        self.assertIn("-fno-pie", rec.to_markdown([("r", results)]))

    def test_arena_blocks_of_no_model_size_stay_whole(self):
        row, _ = synthetic_row()
        for b in row["blocks"]:
            if b["role"] == "arena_combined":
                b["bytes"] = b["granted"] = 3  # nothing near any model size
        results = rec.reduce_row(row)
        q = values(results)
        self.assertEqual(q["ladder_level_blocks_found"].value, "0/3")
        self.assertNotIn(rec.NO_SITE_NAMES, [x.value for x in results if x.name == "note"])
        self.assertEqual(q["role_partition_residual_bytes"].value, 0)
        self.assertGreater(q["role_arena_or_tables_unsplit_bytes"].value, 0)

    def test_rows_without_blocks_still_report_live_over_model(self):
        row, mains = synthetic_row()
        del row["blocks"]
        q = values(rec.reduce_row(row))
        self.assertEqual(q["main_payload"].value, "n/a")
        self.assertEqual(q["model_main_payload"].value, mains)
        self.assertAlmostEqual(q["library_live_over_model_main"].value,
                               row["filled"]["live_requested"] / mains)

    def test_main_reads_audit_files(self):
        row, _ = synthetic_row()
        for b in row["blocks"]:
            b["role"] = "unattributed"
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "audit.txt"
            path.write_text("scheme k:v ...\nAUDIT_ROW " + json.dumps(row) + "\n")
            rec.main([str(path), "--csv", str(Path(d) / "out.csv"), "--md", str(Path(d) / "out.md")])
            text = (Path(d) / "out.csv").read_text()
            self.assertIn("library_live_over_model_main", text)
            self.assertIn("-fno-pie", text)

    def test_failed_rows_are_reported_and_set_the_exit_status(self):
        row, _ = synthetic_row()
        failed = dict(scheme="tree", capacity=4096, key_bytes=8, value_bytes=0, ok=False,
                      error="value_bytes must be nonzero")
        with tempfile.TemporaryDirectory() as d:
            good = Path(d) / "good.txt"
            good.write_text("AUDIT_ROW " + json.dumps(row) + "\n")
            mixed = Path(d) / "mixed.txt"
            mixed.write_text("AUDIT_ROW " + json.dumps(row) + "\nAUDIT_ROW " + json.dumps(failed) + "\n")
            empty = Path(d) / "empty.txt"
            empty.write_text("scheme k:v ...\n")
            md = str(Path(d) / "out.md")
            with contextlib.redirect_stderr(io.StringIO()) as err:
                self.assertEqual(rec.main([str(good), "--md", md]), 0)
                self.assertEqual(rec.main([str(mixed), "--csv", str(Path(d) / "out.csv"), "--md", md]), 1)
                self.assertIn("tree/k8:v0/N4096,failed,value_bytes must be nonzero",
                              (Path(d) / "out.csv").read_text())
                self.assertIn("tree/k8:v0/N4096 failed", err.getvalue())
                self.assertEqual(rec.main([str(empty), "--md", md]), 1)

    def test_aligned64_rounding_matches_the_library_rule(self):
        self.assertEqual(rec.aligned64_bytes(2 * 1024 * 1024 - 1), 2 * 1024 * 1024 - 1)
        self.assertEqual(rec.aligned64_bytes(2 * 1024 * 1024), 2 * 1024 * 1024)
        self.assertEqual(rec.aligned64_bytes(2 * 1024 * 1024 + 1), 4 * 1024 * 1024)

    def test_uniform_ladder_agrees_with_geometry(self):
        for B in (2, 4, 8):
            for L in (2, 3, 4):
                for mode in ("off", "no-clone"):
                    g = model.Geometry(B=B, L=L, D=min(B, 4), bank_first=mode)
                    sl = model.ladder_slots([B] * (L - 1), g.D, g.U(1), [1] * L, mode)
                    self.assertEqual(sum(s[1] for lv in sl for s in lv), g.main_buckets)
                    self.assertEqual(sum(1 for lv in sl for s in lv if s[0] == "run"), g.run_tiers)


if __name__ == "__main__":
    unittest.main()
