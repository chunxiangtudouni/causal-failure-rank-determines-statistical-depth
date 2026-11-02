module

public import PaperProofs.Paid.PDMenu_MajorityInvariant_032

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters

def majorityActionBound (P : Parameters) : ℕ :=
  P.certificate.stages * P.certificate.t0 + P.tools + P.tools + P.certificate.stages + P.certificate.stages + 1

theorem majority_prefix_actionProgress_le (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (seed : Unit) (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {n : ℕ} {state : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C.val .uncapped accounting P.majorityRule seed truth tapes n state) :
    actionProgress state ≤ (majorityActionBound P : ℕ∞) := by
  have hcaps := (majority_prefix_reviewInvariant P fee hfee C accounting seed truth tapes hp).review_le
  have hwf := prefix_ledgerWellFormed (P.input fee hfee) C.val .uncapped accounting P.majorityRule seed truth tapes hp
  have hcursor := (prefix_cursorInvariant (P.input fee hfee) C.val .uncapped accounting P.majorityRule seed truth tapes hp).bound
  rw [P.stageCount_eq] at hcursor
  have hStageCard : Fintype.card P.sharedInstance.Stage = P.certificate.stages :=
    (Fintype.card_fin P.sharedInstance.compatibility.length).trans P.stageCount_eq
  have hToolCard : Fintype.card P.sharedInstance.Tool = P.tools := Fintype.card_fin P.tools
  have hreviews : (∑ stage, state.ledger.reviews stage) ≤ ((P.certificate.stages * P.certificate.t0 : ℕ) : ℕ∞) := by
    calc
      _ ≤ ∑ _stage : P.sharedInstance.Stage, (P.certificate.t0 : ℕ∞) := Finset.sum_le_sum (fun stage _ => hcaps stage)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, hStageCard, nsmul_eq_mul, ENat.natCast_mul]
  have hcommitments : state.ledger.commitments.length ≤ P.tools := by
    have hh := hwf.commitment_tools.length_le_card
    simpa only [List.length_map, hToolCard] using hh
  have hexecutions : state.ledger.executions.length ≤ P.tools :=
    (Ledger.execution_count_le hwf).trans (min_le_right _ _)
  have hwritten : (writtenPorts state.ledger).card ≤ P.certificate.stages := by
    have hh := Finset.card_le_card (Finset.subset_univ (writtenPorts state.ledger))
    simpa only [Finset.card_univ, hStageCard] using hh
  have hhalted : (if state.halted then (1 : ℕ∞) else 0) ≤ 1 := by
    cases state.halted <;> simp
  have ht := add_le_add
    (add_le_add
      (add_le_add
        (add_le_add (add_le_add hreviews (ENat.natCast_le_natCast.mpr hcommitments))
          (ENat.natCast_le_natCast.mpr hexecutions))
        (ENat.natCast_le_natCast.mpr hcursor))
      (ENat.natCast_le_natCast.mpr hwritten)) hhalted
  simpa only [actionProgress, majorityActionBound, ENat.natCast_add, ENat.natCast_one] using ht

theorem majority_run_halts (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (sample : Unit × (P.input fee hfee).World) :
    (run (P.input fee hfee) C.val .uncapped accounting P.majorityRule sample (majorityActionBound P + 1)).halted = true := by
  by_contra hh
  have ha := Bool.eq_false_iff.mpr hh
  have hp := run_prefix_of_active (P.input fee hfee) C.val .uncapped accounting P.majorityRule
    (P.majorityPolicy fee hfee C accounting).legal sample (majorityActionBound P + 1) ha
  have hbound := majority_prefix_actionProgress_le P fee hfee C accounting sample.1 _ _ hp
  rw [prefix_actionProgress (P.input fee hfee) C.val .uncapped accounting P.majorityRule sample.1 _ _ hp] at hbound
  have hnat := ENat.natCast_le_natCast.mp hbound
  omega

theorem majority_run_terminal_counts (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (sample : Unit × (P.input fee hfee).World) :
    ∀ stage, (run (P.input fee hfee) C.val .uncapped accounting P.majorityRule sample
      (majorityActionBound P + 1)).ledger.reviews stage = (P.certificate.t0 : ℕ∞) := by
  obtain ⟨_, _, hp⟩ := run_has_prefix (P.input fee hfee) C.val .uncapped accounting P.majorityRule
    (P.majorityPolicy fee hfee C accounting).legal sample (majorityActionBound P + 1)
  have hcursor := majority_prefix_halted_cursor P fee hfee C accounting sample.1 _ _ hp
    (majority_run_halts P fee hfee C accounting sample)
  intro stage
  apply (majority_prefix_reviewInvariant P fee hfee C accounting sample.1 _ _ hp).written_count
  apply majority_prefix_behind_written P fee hfee C accounting sample.1 _ _ hp stage
  rw [hcursor]
  simpa [sharedInstance] using stage.isLt

theorem majority_prefix_not_abandoned (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (seed : Unit) (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {n : ℕ} {state : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C.val .uncapped accounting P.majorityRule seed truth tapes n state) :
    state.ledger.abandoned = false := by
  induction hp with
  | initial => rfl
  | @next n state next earlier hs ih =>
    have hactive := step_source_active (P.input fee hfee) C.val .uncapped accounting tapes hs
    have hcontrol := majorityRule_eq_atState P fee hfee C accounting seed truth tapes earlier hactive
    generalize ha : P.majorityRule seed state.history = action at hs
    cases hs with
    | write =>
      classical
      simp only [record, reportedWriteLedger]
      split_ifs <;> exact ih
    | stop => rfl
    | abandon => exact (majorityAtState_ne_abandon P state (hcontrol.symm.trans ha)).elim
    | review | allocate | execute | advance => exact ih

end PDMenu
