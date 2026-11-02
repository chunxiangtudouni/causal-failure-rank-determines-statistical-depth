module

public import PaperProofs.Star.PStarLR_PrefixFrame_003
public import PaperProofs.Common.ReferenceTermination
public import PaperProofs.Common.NativeHeadAccounting

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native

namespace PStarLR

variable {I : Instance}

theorem run_halts_after_allWritten (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (rule : PolicyRule I Seed) (legal : LegalRule input C mode accounting rule)
    (sample : Seed × input.World) (start : ℕ)
    (complete : allWritten (run input C mode accounting rule sample start).ledger) :
    ∃ n, start ≤ n ∧ (run input C mode accounting rule sample n).halted = true := by
  classical
  have finite := (run_finiteCounters input C mode accounting rule legal sample start).1
  have numbers : ∀ stage : I.Stage, ∃ count : ℕ,
      (run input C mode accounting rule sample start).ledger.reviews stage = count := by
    intro stage
    lift (run input C mode accounting rule sample start).ledger.reviews stage to ℕ using finite stage with count
    exact ⟨count, rfl⟩
  choose quota hquota using numbers
  let bound := reviewBoundedActionBound I quota
  by_contra never
  have active : (run input C mode accounting rule sample (start+bound+1)).halted = false := by
    apply Bool.eq_false_iff.mpr
    intro halted
    exact never ⟨start+bound+1, by omega, halted⟩
  have path := run_prefix_of_active input C mode accounting rule legal sample (start+bound+1) active
  have bounded : ∀ stage : I.Stage,
      (run input C mode accounting rule sample (start+bound+1)).ledger.reviews stage ≤ (quota stage : ℕ∞) := by
    intro stage
    cases written : (run input C mode accounting rule sample start).ledger.written stage with
    | none => exact (complete stage written).elim
    | some bit =>
      rw [show start+bound+1=start+(bound+1) by omega,
        run_reviews_written_port input C mode accounting rule legal sample start (bound+1) stage bit written,
        hquota stage]
  have length := prefix_length_le_of_reviews_bounded input C mode accounting rule sample.1
    (input.truthAt sample.2) (worldTapes input sample.2) path quota bounded
  change start+bound+1 ≤ bound at length
  omega

end PStarLR
