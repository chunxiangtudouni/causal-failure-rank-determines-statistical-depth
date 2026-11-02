module

public import PaperProofs.Paid.RepresentationClaims
public import PaperProofs.Common.NativeHeadContinuation

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u v

theorem overlay_actualOrdinaryDecision_written_exists (P : Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type u}
    (rule : PolicyRule P.sharedInstance Seed) (sample : Seed × (P.input fee hfee).World)
    (stage : P.sharedInstance.Stage) (bit : Bool)
    (hd : P.actualOrdinaryDecision fee hfee C mode accounting rule sample stage = some bit) :
    ∃ (n : ℕ) (written : Bool),
      (run (P.input fee hfee) C.val mode accounting rule sample n).ledger.written stage = some written := by
  classical
  unfold PaperProofs.Paid.Parameters.actualOrdinaryDecision at hd
  split_ifs at hd with ht hf
  · obtain ⟨n, hn⟩ := ht
    exact ⟨n, true, hn⟩
  · obtain ⟨n, hn⟩ := hf
    exact ⟨n, false, hn⟩

/-- Any actual ordinary write in the original early-report Native protocol
has a genuine report at a finite prefix. No simulator or a.s. input is
needed. This supplies the report-existence side condition in the FP law. -/
theorem overlay_actualOrdinaryDecision_report_exists (P : Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type u}
    (rule : PolicyRule P.sharedInstance Seed) (hl : LegalRule (P.input fee hfee) C.val mode accounting rule)
    (sample : Seed × (P.input fee hfee).World) (stage : P.sharedInstance.Stage) (bit : Bool)
    (hd : P.actualOrdinaryDecision fee hfee C mode accounting rule sample stage = some bit) :
    ∃ n : ℕ, (historyReport (run (P.input fee hfee) C.val mode accounting rule sample n).history stage).isSome = true := by
  obtain ⟨n, written, hw⟩ := overlay_actualOrdinaryDecision_written_exists P fee hfee C mode accounting rule sample stage bit hd
  obtain ⟨k, _, hp⟩ := run_has_prefix (P.input fee hfee) C.val mode accounting rule hl sample n
  obtain ⟨time, ht⟩ := prefix_early_written_reported (P.input fee hfee) C.val C.property.1.1 mode accounting
    rule sample.1 _ _ hp stage (by rw [hw]; simp)
  have hr := prefix_historyReport_early (P.input fee hfee) C.val C.property.1.1 mode accounting rule sample.1 _ _ hp stage
  rw [ht] at hr
  exact ⟨n, by rw [hr]; rfl⟩

/-- Virtual-error measurability follows from the actual measurable run and
the measurable visible-history transducer, without any PathCoupling input. -/
theorem overlay_measurableSet_virtualWriteError (P : Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type u} {SimSeed : Type v} [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (rule : PolicyRule P.sharedInstance SimSeed) (hm : MeasurableRule rule)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed) (hd : RecordSimulatorMeasurable data)
    (stage : P.sharedInstance.Stage) :
    MeasurableSet {sample : SimSeed × (P.input fee hfee).World |
      P.virtualWriteError fee hfee C accounting rule data stage sample} := by
  have each (n : ℕ) : MeasurableSet {sample : SimSeed × (P.input fee hfee).World |
      reportedWriteError (data.shadow sample.1 (run (P.input fee hfee) C.val .uncapped accounting rule sample n).history) stage = some true} := by
    have hh := (measurable_of_countable (State.history (I := P.sharedInstance))).comp
      (measurable_run (P.input fee hfee) C.val .uncapped accounting rule hm n)
    have hs := hd.2.1.comp (measurable_fst.prodMk hh)
    exact hs (MeasurableSpace.measurableSet_top (s :=
      {history : List (VisibleEvent P.sharedInstance) | reportedWriteError history stage = some true}))
  have heq : {sample : SimSeed × (P.input fee hfee).World |
      P.virtualWriteError fee hfee C accounting rule data stage sample} =
      ⋃ n : ℕ, {sample : SimSeed × (P.input fee hfee).World |
        reportedWriteError (data.shadow sample.1 (run (P.input fee hfee) C.val .uncapped accounting rule sample n).history) stage = some true} := by
    ext sample
    simp only [PaperProofs.Paid.Parameters.virtualWriteError, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [heq]
  exact MeasurableSet.iUnion each

end PDROC
