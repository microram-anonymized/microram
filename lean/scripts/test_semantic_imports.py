#!/usr/bin/env python3
"""Guard the semantic entrypoints against transitive numerical imports.

Run from lean/: python3 scripts/test_semantic_imports.py
Uses a source-closure walker over explicit imports; no build is required.
The numerical control ensures that removing traversal cannot make this pass.
"""

from pathlib import Path
import unittest

from configuration_family_baseline import (FAMILY_ANALYTIC_ROOTS, GENERIC_SPEC_ROOTS, PROBABILITY_ROOTS,
                                           SEMANTIC_ROOTS, scan)

KEY_FOUNDATION_ROOTS = (
    "RebuildBound.Spec.Key", "RebuildBound.Proofs.Key",
    "RebuildBound.Spec.IdealKeyLaw", "RebuildBound.Proofs.IdealKeyLaw",
    "RebuildBound.Spec.IdealHierarchy", "RebuildBound.Proofs.IdealHierarchy",
    "RebuildBound.Spec.IdealMeasurable", "RebuildBound.Proofs.IdealMeasurable",
    "RebuildBound.Spec.IdealFailure", "RebuildBound.Proofs.IdealFailure",
    "RebuildBound.Spec.IdealSeed", "RebuildBound.Proofs.IdealSeed",
    "RebuildBound.Spec.IdealInitialization", "RebuildBound.Proofs.IdealInitialization",
)
# Exposure reuses legacy deterministic induction helpers; its public contracts
# are universe-free.
KEY_EXPOSURE_ROOTS = (
    "RebuildBound.Spec.IdealExposure", "RebuildBound.Proofs.IdealExposure",
    "RebuildBound.Spec.IdealFreshness", "RebuildBound.Proofs.IdealFreshness",
)
KEY_JOB_ROOTS = tuple(
    f"RebuildBound.{layer}.{name}"
    for name in ("IdealDirectFresh", "IdealDirectLocal", "IdealDirect",
                 "IdealDirectA", "IdealSepUnion", "IdealSepA", "IdealTopPrep", "IdealTopFinish")
    for layer in ("Spec", "Proofs")
)
KEY_COMPOSITION_ROOTS = (
    "RebuildBound.Spec.IdealGeometry", "RebuildBound.Proofs.IdealGeometry",
    "RebuildBound.Spec.IdealGeometryFamily", "RebuildBound.Proofs.IdealGeometryFamily",
    "RebuildBound.Spec.IdealProbe", "RebuildBound.Proofs.IdealProbe",
    "RebuildBound.Spec.IdealFresh", "RebuildBound.Proofs.IdealFresh",
    "RebuildBound.Spec.IdealCapacity", "RebuildBound.Proofs.IdealCapacity.Analytic",
    "RebuildBound.Spec.IdealOblivious",
    "RebuildBound.Spec.IdealBounded",
)
KEY_HISTORY_ROOTS = (
    "RebuildBound.Spec.ApiCapacity", "RebuildBound.Proofs.ApiCapacity",
    "RebuildBound.Spec.RequesterCuts", "RebuildBound.Proofs.RequesterCuts",
    "RebuildBound.Spec.ApiContinuation", "RebuildBound.Proofs.ApiContinuation",
    "RebuildBound.Spec.HierarchyStructural", "RebuildBound.Proofs.HierarchyStructural",
    "RebuildBound.Spec.HierarchyLive", "RebuildBound.Proofs.HierarchyLive",
)
API_REQUEST_ROOTS = (
    "RebuildBound.Spec.ApiAdaptiveCorrectness",
    "RebuildBound.Spec.ApiStructural", "RebuildBound.Proofs.ApiStructural",
    "RebuildBound.Spec.ApiLegal", "RebuildBound.Proofs.ApiLegal",
    "RebuildBound.Spec.ApiSeed", "RebuildBound.Proofs.ApiSeed",
    "RebuildBound.Spec.ApiBounded", "RebuildBound.Proofs.ApiBounded",
    "RebuildBound.Proofs.ApiAdaptive.Correctness",
)


class SemanticImportsTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.control = "RebuildBound.Proofs.Adaptive"
        cls.closures = scan(Path(__file__).resolve().parent.parent,
                            (*GENERIC_SPEC_ROOTS, *SEMANTIC_ROOTS, *PROBABILITY_ROOTS,
                             *FAMILY_ANALYTIC_ROOTS, *KEY_FOUNDATION_ROOTS,
                             *API_REQUEST_ROOTS, *KEY_HISTORY_ROOTS, *KEY_EXPOSURE_ROOTS,
                             *KEY_JOB_ROOTS, *KEY_COMPOSITION_ROOTS, cls.control))

    def test_key_and_request_foundations_need_no_numerical_certificates(self):
        for root in (*KEY_FOUNDATION_ROOTS, *API_REQUEST_ROOTS, *KEY_HISTORY_ROOTS,
                     *KEY_EXPOSURE_ROOTS, *KEY_JOB_ROOTS, *KEY_COMPOSITION_ROOTS):
            with self.subTest(root=root):
                self.assertEqual(self.closures[root]["matrix_module_count"], 0)
                self.assertEqual([module for module in self.closures[root]["modules"]
                                  if module.startswith(("RebuildBound.Numerics.",
                                                        "RebuildBound.Proofs.Numerics"))], [])

    def test_new_executable_models_import_only_core_or_std(self):
        roots = ("RebuildBound.Spec.Model.ApiCapacity", "RebuildBound.Spec.Model.RequesterCuts",
                 "RebuildBound.Spec.Model.ApiContinuation", "RebuildBound.Spec.Model.ApiLegal")
        closures = scan(Path(__file__).resolve().parent.parent, roots)
        for root in roots:
            with self.subTest(root=root):
                self.assertEqual([module for module in closures[root]["direct_external_imports"]
                                  if module.split(".")[0] not in ("Init", "Std")], [])

    def test_new_history_specs_have_no_legacy_universe_imports(self):
        for root in (*KEY_HISTORY_ROOTS, *KEY_EXPOSURE_ROOTS, "RebuildBound.Spec.IdealProbe", "RebuildBound.Spec.IdealFresh", "RebuildBound.Spec.ApiStructural", "RebuildBound.Spec.ApiSeed", "RebuildBound.Spec.ApiBounded"):
            if ".Spec." not in root:
                continue
            with self.subTest(root=root):
                self.assertEqual([module for module in self.closures[root]["modules"]
                                  if "KeyRelabel" in module or "KeyUniverse" in module], [])

    def test_key_laws_have_no_universe_or_relabel_imports(self):
        for root in KEY_FOUNDATION_ROOTS:
            with self.subTest(root=root):
                self.assertEqual([module for module in self.closures[root]["modules"]
                                  if "KeyRelabel" in module or "KeyUniverse" in module], [])

    def test_semantics_need_no_numerical_certificates_or_family_inventory(self):
        for root in (*GENERIC_SPEC_ROOTS, *SEMANTIC_ROOTS, *PROBABILITY_ROOTS):
            with self.subTest(root=root):
                closure = self.closures[root]
                self.assertEqual(closure["matrix_module_count"], 0)
                forbidden = [module for module in
                             closure["modules"] + closure["direct_external_imports"]
                             if module.startswith(("RebuildBound.Numerics.",
                                                   "RebuildBound.Proofs.Numerics"))
                             or "ConfigurationFamily" in module]
                self.assertEqual(forbidden, [])

    def test_family_probability_needs_no_numerical_certificates(self):
        for root in FAMILY_ANALYTIC_ROOTS:
            with self.subTest(root=root):
                closure = self.closures[root]
                self.assertEqual(closure["matrix_module_count"], 0)
                self.assertEqual([module for module in closure["modules"]
                                  if module.startswith(("RebuildBound.Numerics.",
                                                        "RebuildBound.Proofs.Numerics"))], [])

    def test_generic_spec_needs_no_concrete_31_statements(self):
        for root in GENERIC_SPEC_ROOTS:
            with self.subTest(root=root):
                self.assertEqual([module for module in self.closures[root]["modules"]
                                  if any(part.endswith("31") for part in module.split("."))], [])

    def test_exact_assembly_needs_no_causal_job_spec(self):
        closure = self.closures["RebuildBound.Proofs.AdaptiveAssembly.Exact"]
        for module in ("RebuildBound.Spec.AdaptiveStepsAssembly",
                       "RebuildBound.Spec.AdaptiveStepsJobs"):
            self.assertNotIn(module, closure["modules"])

    def test_generic_key_spec_has_no_family_inventory_or_universe(self):
        modules = self.closures["RebuildBound.Spec.IdealGeometry"]["modules"]
        self.assertEqual([module for module in modules
                          if any(name in module for name in
                                 ("ConfigurationFamily", "KeyUniverse", "KeyRelabel"))], [])

    def test_numerical_control_reaches_matrices_transitively(self):
        self.assertGreater(self.closures[self.control]["matrix_module_count"], 0)
        self.assertIn("RebuildBound.Spec.Configuration31", self.closures[self.control]["modules"])


if __name__ == "__main__":
    unittest.main()
