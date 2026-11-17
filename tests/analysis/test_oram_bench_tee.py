"""Confidential-VM detection and report evidence (analysis/oram_bench/tee.py) with injected
devices, CPU flags, kernel logs and a fake configfs-tsm; no TEE needed."""
import contextlib
import io
import os
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from analysis.oram_bench.attestation import (attest_campaign, binding, capture_path, launch_gate, protection,
                                             record_verdict)
from analysis.oram_bench.codec import ValidationError, decode, load_json, plain
from analysis.oram_bench.doctor import class_cmdline, inspect
from analysis.oram_bench.planner import expand, write_plan
from analysis.oram_bench.resolution import resolve_campaign
from analysis.oram_bench.schema import Campaign, Environment
from analysis.oram_bench.tee import (AttestationBinding, TeeDetection, assess_tee, detect_tee, fetch_report, kernel_log,
                                     report_data, report_facts, runtime_contract)
from analysis.oram_bench.__main__ import main
from test_oram_bench_resolution import stub_worker

TDX_LINE = "Memory Encryption Features active: Intel TDX"
SNP_LINE = "Memory Encryption Features active: AMD SEV SEV-ES SEV-SNP"


def detected(flags=(), devices=(), log=(True, None)):
    return detect_tee(set(flags) | {"avx512f"}, lambda path: path in devices, lambda: log)


def tdx_guest(log=(True, TDX_LINE)):
    return detected({"tdx_guest"}, {"/dev/tdx_guest"}, log)


def snp_guest(log=(True, SNP_LINE)):
    return detected({"sev", "sev_es", "sev_snp"}, {"/dev/sev-guest"}, log)


PLAIN = detected()


def snp_report(data, policy=0x30000, info=0b10001):
    blob = bytearray(0x4A0)
    blob[0:4] = (3).to_bytes(4, "little")
    blob[0x08:0x10] = policy.to_bytes(8, "little")
    blob[0x40:0x48] = info.to_bytes(8, "little")
    blob[0x50:0x90] = data
    return bytes(blob)


def tdx_quote(data, version=4, attributes=0, tee_type=0x81):
    header = bytearray(48)
    header[0:2] = version.to_bytes(2, "little")
    header[4:8] = tee_type.to_bytes(4, "little")
    descriptor = b"" if version == 4 else (3).to_bytes(2, "little") + (648).to_bytes(4, "little")
    body = bytearray(584)
    body[120:128] = attributes.to_bytes(8, "little")
    body[520:584] = data
    return bytes(header) + descriptor + bytes(body) + b"signature data"


class FakeTsm:
    """configfs-tsm's semantics: inblob writes increment generation; outblob reflects inblob."""

    def __init__(self, provider, report, extra_writers=0, auxiliary=None):
        self.provider, self.report, self.extra_writers, self.auxiliary = provider, report, extra_writers, auxiliary
        self.generation, self.inblob, self.entered, self.exited = 7, None, 0, 0

    def __enter__(self):
        self.entered += 1
        return self

    def __exit__(self, *exc):
        self.exited += 1

    def read(self, name):
        if name == "generation":
            return f"{self.generation}\n".encode()
        if name == "outblob":
            return self.report(self.inblob)
        if name == "auxblob":
            if self.auxiliary is None:
                raise OSError(6, "no auxiliary blob")
            return self.auxiliary
        assert name == "provider"
        return f"{self.provider}\n".encode()

    def write(self, name, data):
        assert name == "inblob"
        self.inblob = data
        self.generation += 1 + self.extra_writers


class DetectionTests(unittest.TestCase):
    def test_guest_kinds(self):
        tdx = tdx_guest()
        self.assertEqual((tdx.indicated, tdx.shown, tdx.missing_evidence), (["tdx"], "tdx", []))
        self.assertEqual(tdx.cpu_flags, ["tdx_guest"])
        snp = snp_guest()
        self.assertEqual((snp.indicated, snp.shown, snp.missing_evidence), (["snp"], "snp", []))
        self.assertEqual((PLAIN.indicated, PLAIN.shown, PLAIN.missing_evidence), ([], None, []))
        # A plain VM on SNP-capable hardware shows the sev* flags; they are not a guest signal.
        host = detected({"sev", "sev_es", "sev_snp"})
        self.assertEqual((host.indicated, host.shown), ([], None))
        # Bare-metal SME prints the line without naming a TEE.
        self.assertEqual(detected(log=(True, "Memory Encryption Features active: AMD SME")).indicated, [])
        self.assertEqual(decode(TeeDetection, plain(tdx)), tdx)

    def test_unreadable_log_and_absent_line(self):
        tdx = tdx_guest(log=(False, None))
        self.assertEqual((tdx.shown, tdx.missing_evidence), ("tdx", ["tee:kernel_log_unreadable"]))
        self.assertFalse(tdx.kernel_names("tdx"))
        snp = snp_guest(log=(True, None))  # the ring buffer wrapped
        self.assertEqual((snp.shown, snp.missing_evidence), ("snp", ["tee:kernel_line_absent"]))
        self.assertEqual(detected(log=(False, None)).missing_evidence, ["tee:kernel_log_unreadable"])
        self.assertEqual(detect_tee(None, lambda path: False, lambda: (True, None)).missing_evidence,
                         ["tee:cpu_flags_unreadable"])

    def test_partial_and_conflicting_signals(self):
        flag_only = detected({"tdx_guest"})
        self.assertEqual((flag_only.indicated, flag_only.shown), (["tdx"], None))
        self.assertIn("tee:incomplete_tdx_evidence", flag_only.missing_evidence)
        wrong_line = detected(devices={"/dev/sev-guest"}, log=(True, TDX_LINE))
        self.assertEqual((wrong_line.indicated, wrong_line.shown), (["tdx", "snp"], None))
        self.assertIn("tee:conflicting_indications", wrong_line.missing_evidence)
        line_only = detected(log=(True, SNP_LINE))
        self.assertEqual((line_only.indicated, line_only.shown), (["snp"], None))

    def test_derived_fields_are_checked(self):
        document = plain(PLAIN)
        document["shown"] = "tdx"
        with self.assertRaises(ValidationError):
            decode(TeeDetection, document)
        for flags in (["tdx_guest", "sev"], ["avx512f"]):
            with self.assertRaises(ValidationError):
                assess_tee(flags, False, False, True, None, False)
        with self.assertRaises(ValidationError):
            assess_tee([], False, False, False, TDX_LINE, False)

    def test_kernel_log_sources(self):
        def runner(outputs):
            def run(command, **kwargs):
                code, text = outputs[command[0]]
                if code is None:
                    raise OSError("not installed")
                return SimpleNamespace(returncode=code, stdout=text)
            return run
        journal = "boot\n[    0.000000] " + TDX_LINE + "\n"
        self.assertEqual(kernel_log(runner({"dmesg": (1, ""), "journalctl": (0, journal)})), (True, TDX_LINE))
        self.assertEqual(kernel_log(runner({"dmesg": (0, "[0.1] x\n"), "journalctl": (0, "")})), (True, None))
        self.assertEqual(kernel_log(runner({"dmesg": (0, "  \n"), "journalctl": (None, "")})), (False, None))


class ContractTests(unittest.TestCase):
    def test_labels_match_what_the_host_shows(self):
        self.assertEqual(runtime_contract("tdx", tdx_guest()), [])
        self.assertEqual(runtime_contract("tdx", PLAIN), ["runtime:tdx_not_shown"])
        self.assertEqual(runtime_contract("snp", tdx_guest()), ["runtime:snp_not_shown"])
        self.assertEqual(runtime_contract("native", PLAIN), [])
        self.assertEqual(runtime_contract("native", tdx_guest()), ["runtime:native_on_tee_host:tdx"])
        # Any positive signal refuses the control, even one too weak to show a TEE.
        self.assertEqual(runtime_contract("native", detected({"tdx_guest"})), ["runtime:native_on_tee_host:tdx"])
        self.assertEqual(runtime_contract("fake", tdx_guest()), [])
        self.assertEqual(runtime_contract("tdx", None), ["runtime:tee_detection_missing"])


def host_files(cmdline="BOOT_IMAGE=/vmlinuz-6.8 root=PARTUUID=abc ro console=ttyS0"):
    return {"/proc/cpuinfo": "processor\t: 0\ncpu family\t: 6\nmodel\t\t: 173\nmodel name\t: Intel Xeon\n"
                             "stepping\t: 1\nmicrocode\t: 0x10003a2\nflags\t\t: tdx_guest avx512f\n\n"
                             "processor\t: 1\ncpu family\t: 99\n",
            "/sys/kernel/mm/transparent_hugepage/enabled": "always [madvise] never",
            "/sys/kernel/mm/transparent_hugepage/defrag": "always defer defer+madvise [madvise] never",
            "/proc/cmdline": cmdline, "/proc/stat": "cpu  10 0 5 900 3 0 1 42 0 0\ncpu0 1 0 0 90 0 0 0 4 0 0"}


class DoctorTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.worker = Path(self.directory.name) / "worker"
        self.worker.write_bytes(b"synthetic binary identity")

    def tearDown(self):
        self.directory.cleanup()

    def inspect(self, execution, detection, files=None):
        files = host_files() if files is None else files
        memory = {"guest_total_bytes": 1024, "ancestors": [], "missing_evidence": []}
        with patch("analysis.oram_bench.doctor.detect_tee", return_value=detection), \
             patch("analysis.oram_bench.doctor._text", side_effect=lambda path: files.get(str(path))), \
             patch("analysis.oram_bench.doctor.memory_evidence", return_value=memory), \
             patch("analysis.oram_bench.doctor.source_identity", return_value="synthetic-source"):
            return inspect(self.worker, execution)

    def test_host_facts_and_class(self):
        observed = self.inspect("tdx", tdx_guest())
        self.assertEqual((observed["cpu_family"], observed["cpu_model_number"], observed["cpu_stepping"]), (6, 173, 1))
        self.assertEqual((observed["microcode"], observed["steal_ticks"]), ("0x10003a2", 42))
        self.assertEqual((observed["thp_enabled"], observed["thp_defrag"]), ("madvise", "madvise"))
        self.assertEqual(observed["tee"]["shown"], "tdx")
        self.assertIn("protected_attestation", observed["missing_evidence"])
        self.assertEqual(decode(Environment, observed).runtime, "tdx")
        self.assertEqual(class_cmdline(observed["kernel_cmdline"]), "ro console=ttyS0")
        base = observed["environment_class"]
        # The boot disk does not move results; idle=poll, a THP mode or a stepping does.
        moved = host_files("BOOT_IMAGE=/vmlinuz-6.8 root=PARTUUID=def ro console=ttyS0")
        self.assertEqual(self.inspect("tdx", tdx_guest(), moved)["environment_class"], base)
        for path, value in (("/proc/cmdline", host_files()["/proc/cmdline"] + " idle=poll"),
                            ("/sys/kernel/mm/transparent_hugepage/enabled", "always madvise [never]"),
                            ("/proc/cpuinfo", host_files()["/proc/cpuinfo"].replace("stepping\t: 1", "stepping\t: 2"))):
            with self.subTest(path=path):
                self.assertNotEqual(self.inspect("tdx", tdx_guest(), {**host_files(), path: value})
                                    ["environment_class"], base)
        self.assertNotEqual(self.inspect("native", tdx_guest())["environment_class"], base)

    def test_doctor_refuses_a_label_the_host_does_not_show(self):
        output = Path(self.directory.name) / "doctor.json"
        memory = {"guest_total_bytes": 1024, "ancestors": [], "missing_evidence": []}
        for execution, detection, code in (("tdx", tdx_guest(), 0), ("tdx", PLAIN, 2), ("snp", tdx_guest(), 2),
                                           ("native", tdx_guest(), 2), ("native", PLAIN, 0),
                                           ("snp", snp_guest(), 0)):
            with self.subTest(execution=execution, shown=detection.shown), \
                 patch("analysis.oram_bench.doctor.detect_tee", return_value=detection), \
                 patch("analysis.oram_bench.doctor.memory_evidence", return_value=memory), \
                 patch("analysis.oram_bench.doctor.source_identity", return_value="synthetic-source"), \
                 contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(main(["doctor", "--execution", execution, "--worker", str(self.worker),
                                       "--output", str(output)]), code)
                recorded = [r for r in load_json(output)["missing_evidence"] if r.startswith("runtime:")]
                self.assertEqual(bool(recorded), code == 2)

    def test_protected_verification_needs_a_tee_runtime(self):
        document = self.inspect("tdx", tdx_guest())
        decode(Environment, {**document, "protected_verified": True, "verification_reference": "verdict"})
        with self.assertRaises(ValidationError):
            decode(Environment, {**document, "protected_verified": True})
        native = self.inspect("native", PLAIN)
        with self.assertRaises(ValidationError):
            decode(Environment, {**native, "protected_verified": True, "verification_reference": "verdict"})
        reference = {"path": "attestations/x.json", "sha256": "a" * 64, "bytes": 1}
        decode(Environment, {**document, "attestation": reference})
        with self.assertRaises(ValidationError):
            decode(Environment, {**native, "attestation": reference})
        with self.assertRaises(ValidationError):
            decode(Environment, {**document, "attestation": {**reference, "path": "../x.json"}})


class ReportTests(unittest.TestCase):
    def test_snp_report(self):
        data = bytes(range(64))
        facts = report_facts("snp", snp_report(data, policy=0x30000 | 1 << 19), data)
        self.assertEqual((facts.layout, facts.report_version, facts.report_data_matches, facts.debug),
                         ("snp_report", 3, True, True))
        self.assertEqual((facts.snp_platform_info, facts.snp_ciphertext_hiding), (17, True))
        facts = report_facts("snp", snp_report(data, info=1), bytes(64))
        self.assertEqual((facts.report_data_matches, facts.debug, facts.snp_ciphertext_hiding), (False, False, False))
        self.assertEqual(report_facts("snp", snp_report(data)[:-1], data).layout, "unrecognized")

    def test_tdx_quotes(self):
        data = bytes(range(64, 128))
        for version in (4, 5):
            facts = report_facts("tdx", tdx_quote(data, version, attributes=1), data)
            self.assertEqual((facts.layout, facts.report_data_matches, facts.debug),
                             (f"tdx_quote_v{version}", True, True))
            self.assertIsNone(facts.snp_platform_info)
        self.assertFalse(report_facts("tdx", tdx_quote(data), bytes(64)).report_data_matches)
        for blob in (tdx_quote(data, tee_type=0), tdx_quote(data, version=3), tdx_quote(data)[:600], b""):
            self.assertEqual(report_facts("tdx", blob, data).layout, "unrecognized")

    def test_configfs_fetch(self):
        data = bytes(range(64))
        tsm = FakeTsm("tdx_guest", tdx_quote)
        provider, blob, auxiliary, generation = fetch_report(data, tsm)
        self.assertEqual((provider, blob, auxiliary, generation), ("tdx_guest", tdx_quote(data), None, 8))
        self.assertEqual((tsm.entered, tsm.exited), (1, 1))
        self.assertEqual(fetch_report(data, FakeTsm("sev_guest", snp_report, auxiliary=b"certs"))[2], b"certs")
        racing = FakeTsm("tdx_guest", tdx_quote, extra_writers=1)
        with self.assertRaisesRegex(ValidationError, "another writer"):
            fetch_report(data, racing)
        self.assertEqual(racing.exited, 1)
        with self.assertRaises(ValidationError):
            fetch_report(data[:63], FakeTsm("tdx_guest", tdx_quote))
        with self.assertRaisesRegex(ValidationError, "empty report"):
            fetch_report(data, FakeTsm("tdx_guest", lambda inblob: b""))


def configuration(runtime="tdx", protected=True):
    return {"schema_version": 1, "name": "tee-fixture", "repetitions": 1,
            "resources": {"physical_cores": 4}, "execution": {"runtime": runtime, "require_protected": protected},
            "stages": [{"name": "fixture", "kind": "smoke", "capacities": [128],
                        "shapes": [{"name": "small", "key_bytes": 4, "value_bytes": 8}],
                        "candidates": [{"name": "pinned", "overrides": {"scheme": "hierarchical_incremental"}}],
                        "api_modes": ["scalar"]}],
            "timing": {"warmup_ns": 0, "measurement_ns": 1000000, "max_trial_ns": 5000000000,
                       "setup_allowance_ns": 1000000000, "drain_deadline_ns": 1000000000}}


class CampaignAttestationTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.root = Path(self.directory.name)
        self.worker = stub_worker(self.root)
        self.reducer = self.root / "reducer"
        self.reducer.write_text("never executed")
        os.environ["STUB_WORKER_LOG"] = str(self.root / "calls.jsonl")

    def tearDown(self):
        self.directory.cleanup()

    def campaign(self, data=None, name="campaign"):
        path = self.root / name
        write_plan(expand(decode(Campaign, data or configuration())), path)
        resolve_campaign(path, self.worker)
        return path

    def attest(self, campaign, detection=None, tsm=None):
        with patch("analysis.oram_bench.doctor.detect_tee", return_value=detection or tdx_guest()):
            return attest_campaign(campaign, tsm or FakeTsm("tdx_guest", tdx_quote))

    def run_to_launch(self, campaign, detection=None):
        """Run up to the first attempt: past both gates, with the environment recorded, the
        per-attempt memory preflight is reached, and the fixture stops there."""
        from analysis.oram_bench.campaign import run_campaign
        compatible = {"status": "compatible", "rejection_reasons": [], "missing_evidence": []}
        with patch("analysis.oram_bench.doctor.detect_tee", return_value=detection or tdx_guest()), \
             patch("analysis.oram_bench.campaign.topology_check", return_value=compatible), \
             patch("analysis.oram_bench.campaign.attempt_preflight",
                   side_effect=RuntimeError("fixture reached launch")):
            try:
                return run_campaign(campaign, self.reducer, min_free_bytes=0)
            except RuntimeError as error:
                self.assertEqual(str(error), "fixture reached launch")
                return None

    def test_capture_run_verdict(self):
        campaign = self.campaign()
        result = self.attest(campaign)
        self.assertEqual(result["status"], "captured")
        self.assertEqual((result["facts"]["layout"], result["facts"]["report_data_matches"]), ("tdx_quote_v4", True))
        capture = load_json(campaign / result["capture"])
        self.assertEqual(capture["binding"]["runtime"], "tdx")
        self.assertEqual(bytes.fromhex(capture["report_data"]),
                         report_data(decode(AttestationBinding, capture["binding"])))
        # One report per boot: a second attest reuses the capture without touching configfs.
        unused = FakeTsm("tdx_guest", tdx_quote)
        self.assertEqual(self.attest(campaign, tsm=unused)["status"], "existing")
        self.assertEqual(unused.entered, 0)

        self.assertIsNone(self.run_to_launch(campaign))
        [environment_path] = (campaign / "environments").glob("*.json")
        environment = load_json(environment_path)
        self.assertEqual(environment["runtime"], "tdx")
        self.assertEqual(environment["attestation"]["path"], result["capture"])
        self.assertEqual(protection(campaign, environment), (False, None))

        log = self.root / "verifier.log"
        log.write_text("go-tdx-guest check: quote verified\n")
        verdict = record_verdict(campaign, result["capture"], "go-tdx-guest check (fixture)", "verified",
                                 "fixture-reference", log)
        self.assertTrue((campaign / verdict["output"]["path"]).exists())
        verified, reference = protection(campaign, environment)
        self.assertTrue(verified)
        self.assertIn("fixture-reference", reference)
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(main(["verdict", "--campaign", str(campaign), "--capture", result["capture"],
                                   "--verifier", "Intel Trust Authority (fixture)", "--result", "failed",
                                   "--reference", "token"]), 0)
        self.assertEqual(protection(campaign, environment), (False, None))  # a failure outweighs a success

    def test_tampered_capture_is_not_verified(self):
        campaign = self.campaign()
        result = self.attest(campaign)
        self.assertIsNone(self.run_to_launch(campaign))
        environment = load_json(next((campaign / "environments").glob("*.json")))
        record_verdict(campaign, result["capture"], "fixture verifier", "verified", "reference")
        self.assertTrue(protection(campaign, environment)[0])
        report = campaign / load_json(campaign / result["capture"])["report"]["path"]
        report.chmod(0o644)
        report.write_bytes(report.read_bytes()[:-1] + b"!")
        self.assertEqual(protection(campaign, environment), (False, None))

    def test_run_blocks_without_this_boots_capture_or_on_the_wrong_host(self):
        campaign = self.campaign()
        result = self.run_to_launch(campaign)
        self.assertEqual(result["launched"], 0)
        blocked = load_json(campaign / "coordinator_status.json")
        self.assertEqual((blocked["status"], blocked["reason"]), ("blocked", "runtime"))
        self.assertEqual(blocked["assessment"]["rejection_reasons"], ["attestation:no_capture_this_boot"])
        self.assertFalse((campaign / "trials").exists())
        self.run_to_launch(campaign, PLAIN)
        self.assertEqual(load_json(campaign / "coordinator_status.json")["assessment"]["rejection_reasons"],
                         ["runtime:tdx_not_shown"])
        native = self.campaign(configuration("native", False), "native")
        self.run_to_launch(native)
        self.assertEqual(load_json(native / "coordinator_status.json")["assessment"]["rejection_reasons"],
                         ["runtime:native_on_tee_host:tdx"])
        self.assertIsNone(self.run_to_launch(native, PLAIN))

    def test_attest_refusals(self):
        campaign = self.campaign()
        with self.assertRaisesRegex(ValidationError, "does not show"):
            self.attest(campaign, PLAIN)
        with self.assertRaisesRegex(ValidationError, "boot log"):
            self.attest(campaign, tdx_guest(log=(False, None)))
        with self.assertRaisesRegex(ValidationError, "provider"):
            self.attest(campaign, tsm=FakeTsm("sev_guest", tdx_quote))
        with self.assertRaisesRegex(ValidationError, "bound report data"):
            self.attest(campaign, tsm=FakeTsm("tdx_guest", lambda inblob: tdx_quote(bytes(64))))
        self.assertFalse((campaign / "attestations").exists() and any((campaign / "attestations").glob("*.json")))
        with self.assertRaisesRegex(ValidationError, "tdx or snp"):
            attest_campaign(self.campaign(configuration("native", False), "native"))

    def test_debug_guest_blocks_a_protected_campaign(self):
        campaign = self.campaign()
        self.attest(campaign, tsm=FakeTsm("tdx_guest", lambda inblob: tdx_quote(inblob, attributes=1)))
        self.run_to_launch(campaign)
        self.assertEqual(load_json(campaign / "coordinator_status.json")["assessment"]["rejection_reasons"],
                         ["attestation:debug_guest"])
        exploratory = self.campaign(configuration("tdx", False), "exploratory")
        self.attest(exploratory, tsm=FakeTsm("tdx_guest", lambda inblob: tdx_quote(inblob, attributes=1)))
        self.assertIsNone(self.run_to_launch(exploratory))

    def attest_snp(self, campaign, report=snp_report, detection=None):
        return self.attest(campaign, detection or snp_guest(), FakeTsm("sev_guest", report))

    def test_snp_capture_run_verdict(self):
        campaign = self.campaign(configuration("snp"))
        result = self.attest_snp(campaign, lambda inblob: snp_report(inblob, info=0b00001))
        self.assertEqual(result["status"], "captured")
        facts = result["facts"]
        self.assertEqual((facts["layout"], facts["report_data_matches"], facts["debug"]), ("snp_report", True, False))
        self.assertEqual((facts["snp_platform_info"], facts["snp_ciphertext_hiding"]), (1, False))
        capture = load_json(campaign / result["capture"])
        self.assertEqual((capture["binding"]["runtime"], capture["provider"]), ("snp", "sev_guest"))
        self.assertEqual(bytes.fromhex(capture["report_data"]),
                         report_data(decode(AttestationBinding, capture["binding"])))
        self.assertIsNone(self.run_to_launch(campaign, snp_guest()))
        environment = load_json(next((campaign / "environments").glob("*.json")))
        self.assertEqual(environment["runtime"], "snp")
        self.assertEqual(protection(campaign, environment), (False, None))
        record_verdict(campaign, result["capture"], "snpguest verify attestation (fixture)", "verified", "vcek-fixture")
        verified, reference = protection(campaign, environment)
        self.assertTrue(verified)
        self.assertIn("vcek-fixture", reference)
        record_verdict(campaign, result["capture"], "snpguest verify attestation (fixture)", "failed", "vcek-bad")
        self.assertEqual(protection(campaign, environment), (False, None))

    def test_snp_ciphertext_hiding_is_recorded_when_on(self):
        campaign = self.campaign(configuration("snp"))
        result = self.attest_snp(campaign, lambda inblob: snp_report(inblob, info=0b10001))
        self.assertEqual((result["facts"]["snp_platform_info"], result["facts"]["snp_ciphertext_hiding"]), (17, True))

    def test_snp_refusals_and_debug_guest(self):
        campaign = self.campaign(configuration("snp"))
        with self.assertRaisesRegex(ValidationError, "does not show"):
            self.attest_snp(campaign, detection=tdx_guest())
        with self.assertRaisesRegex(ValidationError, "provider"):
            self.attest(campaign, snp_guest(), FakeTsm("tdx_guest", snp_report))
        with self.assertRaisesRegex(ValidationError, "bound report data"):
            self.attest_snp(campaign, lambda inblob: snp_report(bytes(64)))
        self.attest_snp(campaign, lambda inblob: snp_report(inblob, policy=0x30000 | 1 << 19))
        self.run_to_launch(campaign, snp_guest())
        self.assertEqual(load_json(campaign / "coordinator_status.json")["assessment"]["rejection_reasons"],
                         ["attestation:debug_guest"])

    def test_snp_run_blocks_without_capture_or_on_a_tdx_guest(self):
        campaign = self.campaign(configuration("snp"))
        self.run_to_launch(campaign, snp_guest())
        self.assertEqual(load_json(campaign / "coordinator_status.json")["assessment"]["rejection_reasons"],
                         ["attestation:no_capture_this_boot"])
        self.run_to_launch(campaign, tdx_guest())
        self.assertEqual(load_json(campaign / "coordinator_status.json")["assessment"]["rejection_reasons"],
                         ["runtime:snp_not_shown"])
        native = self.campaign(configuration("native", False), "native")
        self.run_to_launch(native, snp_guest())
        self.assertEqual(load_json(native / "coordinator_status.json")["assessment"]["rejection_reasons"],
                         ["runtime:native_on_tee_host:snp"])

    def test_gate_reads_the_environments_runtime_evidence(self):
        environment = {"runtime": "tdx", "boot_identity": None, "missing_evidence": []}
        gate = launch_gate(self.root, {"runtime": "tdx", "require_protected": True}, environment)
        self.assertEqual(gate["rejection_reasons"], ["attestation:boot_identity_unknown"])
        environment = {"runtime": "native", "boot_identity": "b", "missing_evidence": ["runtime:native_on_tee_host:snp"]}
        gate = launch_gate(self.root, {"runtime": "native", "require_protected": False}, environment)
        self.assertEqual((gate["status"], gate["attestation"]), ("blocked", None))
        self.assertTrue(capture_path(binding({"runtime": "snp", "host_identity": "h", "boot_identity": "b",
                                              "environment_class": "c"})).startswith("attestations/"))


if __name__ == "__main__":
    unittest.main()
