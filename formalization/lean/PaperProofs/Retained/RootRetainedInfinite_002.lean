module

public import PaperProofs.Retained.RootRetainedInfinite_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace RootRetainedInfinite

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained

variable {I : Instance}

theorem prefix_reviews_zero (input : StatisticalInput I) (top : girth I = ⊤)
    (C : Contract I) (accounting : NormalAccounting I) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {state : State I}
    (hp : Prefix input C .uncapped accounting (retainedRule input budget limit) seed truth tapes n state)
    (stage : I.Stage) : state.ledger.reviews stage = 0 := by
  have gate : ∀ (clock : ℕ) (s : State I),
      Prefix input C .uncapped accounting (retainedRule input budget limit) seed truth tapes clock s →
      s.halted = false → ∀ i : I.Stage, retainedRule input budget limit seed s.history = .review i →
        s.ledger.reviews i < ((0 : ℕ) : ℕ∞) := by
    intro clock s _path _active i review
    exact (rule_ne_review input top budget limit seed s.history i review).elim
  have bound := prefix_reviews_le_of_review_gate input C .uncapped accounting
    (retainedRule input budget limit) seed truth tapes (fun _ => 0) gate hp stage
  exact le_antisymm bound bot_le

theorem run_reviews_zero (input : StatisticalInput I) (top : girth I = ⊤)
    (C : Contract I) (hearly : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (limit : ReferenceObservationLimit I) (sample : Unit × input.World) (n : ℕ) (stage : I.Stage) :
    (run input C .uncapped accounting (retainedRule input budget limit) sample n).ledger.reviews stage = 0 := by
  obtain ⟨_,_,hp⟩ := run_has_prefix input C .uncapped accounting (retainedRule input budget limit)
    (retainedRule_uncapped_legal input C hearly accounting budget limit) sample n
  exact prefix_reviews_zero input top C accounting budget limit sample.1 _ _ hp stage

theorem run_halts (input : StatisticalInput I) (top : girth I = ⊤)
    (C : Contract I) (hearly : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (limit : ReferenceObservationLimit I) (sample : Unit × input.World) :
    ∃ n, (run input C .uncapped accounting (retainedRule input budget limit) sample n).halted = true := by
  let bound := reviewBoundedActionBound I (fun _ => 0)
  by_contra never
  have active : (run input C .uncapped accounting (retainedRule input budget limit) sample (bound+1)).halted = false :=
    Bool.eq_false_iff.mpr (not_exists.mp never (bound+1))
  have hp := run_prefix_of_active input C .uncapped accounting (retainedRule input budget limit)
    (retainedRule_uncapped_legal input C hearly accounting budget limit) sample (bound+1) active
  have length := prefix_length_le_of_reviews_bounded input C .uncapped accounting
    (retainedRule input budget limit) sample.1 _ _ hp (fun _ => 0)
      (fun stage => (run_reviews_zero input top C hearly accounting budget limit sample (bound+1) stage).le)
  change bound+1 ≤ bound at length
  omega

theorem runObservationBill_zero (input : StatisticalInput I) (top : girth I = ⊤)
    (C : Contract I) (hearly : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (limit : ReferenceObservationLimit I) (sample : Unit × input.World) :
    runObservationBill input C .uncapped accounting (retainedRule input budget limit) sample = 0 := by
  simp only [runObservationBill, Ledger.observationBill,
    run_reviews_zero input top C hearly accounting budget limit, ENat.toENNReal_zero,
    mul_zero, Finset.sum_const_zero, iSup_const]

theorem expectedObservationBill_zero (input : StatisticalInput I) (top : girth I = ⊤)
    (C : Contract I) (hearly : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (limit : ReferenceObservationLimit I) :
    expectedObservationBill input C .uncapped accounting (retainedRule input budget limit) (Measure.dirac ()) = 0 := by
  simp only [expectedObservationBill, runObservationBill_zero input top C hearly accounting budget limit,
    lintegral_zero]

end RootRetainedInfinite
