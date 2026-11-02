module

public import PaperProofs.Star.PStarLR_LateReports_005
public import PaperProofs.Star.PStarLR_ToolChoice_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star PaperProofs.Star.Parameters

namespace PStarLR

variable {I : Instance}

theorem prefix_referenceVisibleHandle_valid (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {state : State I} (path : Prefix input C mode accounting policy seed truth tapes n state)
    (handle : MismatchHandle I) (valid : validHandle state handle) :
    referenceVisibleHandle state.history handle.stage = some handle := by
  rw [referenceVisibleHandle, prefix_historyWrite input C mode accounting policy seed truth tapes path,
    valid.1]
  simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
  congr 1
  cases handle with
  | mk stage serial => simpa only [MismatchHandle.mk.injEq, true_and] using valid.2.1.symm

theorem prefix_reportedError_genuine (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {state : State I} (path : Prefix input C mode accounting policy seed truth tapes n state)
    (stage : I.Stage) (wrong : reportedError state.history stage = true) :
    validHandle state ⟨stage, state.ledger.writeSerial stage⟩ := by
  unfold reportedError at wrong
  rw [prefix_historyWritten input C mode accounting policy seed truth tapes path,
    prefix_historyReport_all_contracts input C mode accounting policy seed truth tapes path] at wrong
  cases hw : state.ledger.written stage with
  | none => simp [hw] at wrong
  | some bit =>
    cases hr : state.ledger.reportTime stage with
    | none => simp [hr] at wrong
    | some time =>
      refine ⟨?_, rfl, time, hr⟩
      cases ht : state.ledger.truth stage <;> cases bit <;>
        simp [hw, hr, ht] at wrong ⊢

theorem prefix_complete_reportedError (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {state : State I} (path : Prefix input C mode accounting policy seed truth tapes n state)
    (complete : allWritten state.ledger) (stage : I.Stage) :
    reportedError state.history stage = true ↔ stage ∈ PaperProofs.Retained.ordinaryMismatches state.ledger := by
  have reported := prefix_allWritten_reported input C mode accounting policy seed truth tapes path complete stage
  unfold reportedError
  rw [prefix_historyWritten input C mode accounting policy seed truth tapes path,
    prefix_historyReport_all_contracts input C mode accounting policy seed truth tapes path]
  rw [PaperProofs.Retained.mem_ordinaryMismatches]
  cases hw : state.ledger.written stage with
  | none => exact (complete stage hw).elim
  | some bit =>
    cases hr : state.ledger.reportTime stage with
    | none => exact (reported hr).elim
    | some time => cases ht : state.ledger.truth stage <;> cases bit <;> simp

theorem prefix_complete_reportedCorrect (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {state : State I} (path : Prefix input C mode accounting policy seed truth tapes n state)
    (complete : allWritten state.ledger) (stage : I.Stage) :
    reportedCorrect state.history stage = true ↔ state.ledger.written stage = some (state.ledger.truth stage) := by
  have reported := prefix_allWritten_reported input C mode accounting policy seed truth tapes path complete stage
  unfold reportedCorrect
  rw [prefix_historyWritten input C mode accounting policy seed truth tapes path,
    prefix_historyReport_all_contracts input C mode accounting policy seed truth tapes path]
  cases hw : state.ledger.written stage with
  | none => exact (complete stage hw).elim
  | some bit =>
    cases hr : state.ledger.reportTime stage with
    | none => exact (reported hr).elim
    | some time => cases ht : state.ledger.truth stage <;> cases bit <;> simp

theorem prefix_complete_errors (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {state : State I} (path : Prefix input C mode accounting policy seed truth tapes n state)
    (complete : allWritten state.ledger) :
    (Finset.univ.filter fun stage => reportedError state.history stage) =
      PaperProofs.Retained.ordinaryMismatches state.ledger := by
  classical
  ext stage
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact prefix_complete_reportedError input C mode accounting policy seed truth tapes path complete stage

end PStarLR
