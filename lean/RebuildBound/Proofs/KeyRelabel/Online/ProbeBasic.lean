import RebuildBound.Proofs.KeyRelabel.Core
import RebuildBound.Spec.Model.Probe

namespace RebuildBound.KeyRelabel
open Model Model.Hierarchy

/-- Renaming preserves the selected record and the complete address sequence. -/
def probeResult (e : LogicalKey ≃ LogicalKey) (r : Probe.Result) : Probe.Result :=
  ⟨r.found.map (rec e), r.addresses⟩

@[simp] theorem latest_rename (e : LogicalKey ≃ LogicalKey) (k : LogicalKey) (rs : List Rec) :
    DirectPrefix.latest (e k) (rs.map (rec e)) =
      (DirectPrefix.latest k rs).map (rec e) := by
  simp only [DirectPrefix.latest, ← List.map_reverse, List.find?_map]
  congr 2
  funext r
  exact key_beq e r.key k

@[simp] theorem probe_decode (e : LogicalKey ≃ LogicalKey) (r : Option Rec) :
    Probe.decode (r.map (rec e)) = Probe.decode r := by
  cases r <;> rfl

@[simp] theorem probe_latestValue (e : LogicalKey ≃ LogicalKey) (k : LogicalKey) (rs : List Rec) :
    Probe.latestValue (e k) (rs.map (rec e)) = Probe.latestValue k rs := by
  simp [Probe.latestValue]

@[simp] theorem probe_scan (e : LogicalKey ≃ LogicalKey) (k : LogicalKey) (o : Output) (address : Nat) :
    Probe.scan (e k) (output e o) address = (Probe.scan k o address).map (rec e) := by
  have hg : (buckets e o.main).getD address [] = bucket e (o.main.getD address []) := by
    change ((o.main.map (bucket e))[address]?).getD (bucket e []) = _
    simp only [List.getElem?_map, Option.getD_map]
    rfl
  unfold Probe.scan
  simp only [output, hg, bucket_recs]
  change DirectPrefix.latest (e k)
    ((o.main.getD address []).recs.map (rec e) ++ (Bucket.recs o.tier).map (rec e)) = _
  rw [← List.map_append, latest_rename]


@[simp] theorem option_orElse_rec (e : LogicalKey ≃ LogicalKey) (a b : Option Rec) :
    (a.map (rec e)).orElse (fun _ => b.map (rec e)) =
      (a.orElse (fun _ => b)).map (rec e) := by cases a <;> rfl

 theorem probe_cascade (e : LogicalKey ≃ LogicalKey) (k : LogicalKey) (tableAt : Nat × Nat → Output)
    (real : Nat × Nat → Nat) (dummy : Nat → Nat × Nat → Nat)
    (cs : List (Nat × Nat)) (initial : Option Rec) (offset : Nat) :
    Probe.cascade (e k) (fun c => output e (tableAt c)) real dummy cs
      (initial.map (rec e)) offset =
    probeResult e (Probe.cascade k tableAt real dummy cs initial offset) := by
  induction cs generalizing initial offset with
  | nil => rfl
  | cons c cs ih =>
    simp only [Probe.cascade, probe_scan] at ih
    simp only [Probe.cascade, Probe.cascadeWith, Option.isSome_map, probe_scan, option_orElse_rec]
    rw [ih]
    rfl


end RebuildBound.KeyRelabel
