module

public import PaperProofs.Star.Claims
public import PaperProofs.Common.ReferenceMassFlow

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PStarLR

variable {I : Instance}

def PastWritten (state : State I) : Prop :=
  ∀ stage : I.Stage, stage.val < state.cursor → state.ledger.written stage ≠ none

theorem step_pastWritten (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {state next : State I} {action : Action I}
    (step : Step input C mode accounting tapes state action next)
    (known : PastWritten state) : PastWritten next := by
  have preserve (stage : I.Stage) (hstage : stage.val < state.cursor) :
      next.ledger.written stage ≠ none := by
    obtain ⟨bit, hbit⟩ := Option.ne_none_iff_exists'.mp (known stage hstage)
    have hnext := step_written_some input C mode accounting tapes step stage bit hbit
    rw [hnext]
    simp
  cases step with
  | advance stage live written resources =>
    intro other hother
    by_cases hbefore : other.val < state.cursor
    · exact preserve other hbefore
    · have heq : other = stage := by
        apply Fin.ext
        have hcursor := live.2
        change other.val < state.cursor + 1 at hother
        omega
      subst other
      exact written
  | review | write | allocate | execute | stop | abandon =>
    exact fun stage hstage => preserve stage hstage

theorem prefix_pastWritten (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {state : State I} (path : Prefix input C mode accounting rule seed truth tapes n state) :
    PastWritten state := by
  induction path with
  | initial => intro stage hstage; change stage.val < 0 at hstage; omega
  | next earlier step ih => exact step_pastWritten input C mode accounting tapes step ih

theorem prefix_allWritten_of_terminal (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {state : State I} (path : Prefix input C mode accounting rule seed truth tapes n state)
    (terminal : state.cursor = I.stageCount) : allWritten state.ledger := by
  intro stage
  apply prefix_pastWritten input C mode accounting rule seed truth tapes path stage
  have hstage : stage.val < I.stageCount := stage.isLt
  omega

theorem prefix_cursor_lt_of_not_allWritten (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {state : State I} (path : Prefix input C mode accounting rule seed truth tapes n state)
    (incomplete : ¬ allWritten state.ledger) : state.cursor < I.stageCount := by
  have bound := (prefix_cursorInvariant input C mode accounting rule seed truth tapes path).bound
  have hne : state.cursor ≠ I.stageCount := fun heq =>
    incomplete (prefix_allWritten_of_terminal input C mode accounting rule seed truth tapes path heq)
  omega

theorem star_maxCorrection_le (P : PaperProofs.Star.Parameters) (order : Order) :
    (P.input order).fees.maxCorrection ≤ ENNReal.ofReal (P.correctionFee : ℝ) := by
  unfold Fees.maxCorrection
  apply Finset.sup_le
  intro pair _hpair
  exact le_rfl

theorem referenceAllPathCharges_of_legal (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (r : ℝ) (limit : Option ℕ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order))
    (legal : LegalRule (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r limit (Seed := Unit))) :
    P.ReferenceAllPathCharges order kind r limit C accounting := by
  intro sample
  have hcount : min (starInstance P.tools order).stageCount (starInstance P.tools order).toolCount ≤ P.tools :=
    min_le_right _ _
  have hcountENN : ((min (starInstance P.tools order).stageCount
      (starInstance P.tools order).toolCount : ℕ) : ℝ≥0∞) ≤ P.tools := by exact_mod_cast hcount
  refine ⟨?_, ?_⟩
  · intro n
    exact (run_actualCorrections_le (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r limit) legal sample n).trans hcount
  · exact (runActualBill_le_observation_add (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r limit) legal sample).trans
        (add_le_add le_rfl (mul_le_mul' hcountENN (star_maxCorrection_le P order)))

end PStarLR
