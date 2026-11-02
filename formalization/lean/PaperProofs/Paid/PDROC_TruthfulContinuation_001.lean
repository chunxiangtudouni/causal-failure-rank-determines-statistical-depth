module

public import PaperProofs.Paid.RepresentationClaims
public import PaperProofs.Common.NativeDeadlines
public import PaperProofs.Common.NativeCausality

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

def PastPortsWritten (s : State I) : Prop :=
  ∀ i : I.Stage, i.val < s.cursor → s.ledger.written i ≠ none

def ExistingPhysicallyCorrect (s : State I) : Prop :=
  ∀ i : I.Stage, s.ledger.written i ≠ none →
    s.ledger.written i = some (s.ledger.truth i) ∨ ∃ e ∈ s.ledger.executions, e.handle.stage = i

theorem step_pastPortsWritten (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I} (hp : PastPortsWritten s)
    (hs : Step input C mode accounting tapes s action next) : PastPortsWritten next := by
  classical
  intro i hi
  cases hs with
  | write stage bit live port resources =>
    have hne : i ≠ stage := by intro he; subst i; have hc := live.2; simp only [record] at hi; omega
    have hw : (reportedWriteLedger C s stage bit).written i = s.ledger.written i := by
      simp only [reportedWriteLedger]
      split_ifs <;> simp only [writeLedger, Function.update_of_ne hne]
    exact hw ▸ hp i hi
  | advance stage live written resources =>
    have hc := live.2
    change i.val < s.cursor + 1 at hi
    by_cases he : i = stage
    · subst i; exact written
    · have hlt : i.val < s.cursor := by have hval : i.val ≠ stage.val := fun h => he (Fin.ext h); omega
      exact hp i hlt
  | review | allocate | execute | stop | abandon => exact hp i hi

theorem prefix_pastPortsWritten (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s) :
    PastPortsWritten s := by
  induction hp with
  | initial => intro i hi; exact (Nat.not_lt_zero _ hi).elim
  | next _ hs ih => exact step_pastPortsWritten input C mode accounting tapes ih hs

theorem truthfulWrite_preserves_existingCorrect (C : Contract I) (accounting : NormalAccounting I)
    (s : State I) (stage : I.Stage) (hc : ExistingPhysicallyCorrect s) :
    ExistingPhysicallyCorrect (record accounting s (.write stage (s.ledger.truth stage))
      (writeResponses C s stage (s.ledger.truth stage))
      (reportedWriteLedger C s stage (s.ledger.truth stage)) s.cursor false) := by
  classical
  have hf : (reportedWriteLedger C s stage (s.ledger.truth stage)).written =
        Function.update s.ledger.written stage (some (s.ledger.truth stage)) ∧
      (reportedWriteLedger C s stage (s.ledger.truth stage)).truth = s.ledger.truth ∧
      (reportedWriteLedger C s stage (s.ledger.truth stage)).executions = s.ledger.executions := by
    simp only [reportedWriteLedger]
    split_ifs <;> exact ⟨rfl, rfl, rfl⟩
  intro i hi
  change (reportedWriteLedger C s stage (s.ledger.truth stage)).written i ≠ none at hi
  change (reportedWriteLedger C s stage (s.ledger.truth stage)).written i =
      some ((reportedWriteLedger C s stage (s.ledger.truth stage)).truth i) ∨
      ∃ e ∈ (reportedWriteLedger C s stage (s.ledger.truth stage)).executions, e.handle.stage = i
  simp only [hf.1, hf.2.1, hf.2.2] at hi ⊢
  by_cases he : i = stage
  · subst i; exact Or.inl (Function.update_self _ _ _)
  · simp only [Function.update_of_ne he] at hi ⊢
    exact hc i hi

/-- A concrete finite uncapped successful continuation: after all existing
writes are physically correct, write each remaining truth, advance, and
actually stop. This is a semantic feasibility witness, not a policy granted
access to hidden truth or a modification to the original comparator. -/
theorem truthfulContinuation_exists (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input) (s : State I)
    (hinv : Invariant C s) (htime : DeadlineInvariant C s.ledger s.cursor s.clock)
    (hcursor : CursorInvariant s) (hactive : s.halted = false)
    (hpast : PastPortsWritten s) (hcorrect : ExistingPhysicallyCorrect s) :
    ∃ final : State I,
      Relation.ReflTransGen (fun before after => ∃ action,
        Step input C .uncapped accounting tapes before action after) s final ∧
      final.halted = true ∧ final.ledger.success C := by
  classical
  induction hremaining : I.stageCount - s.cursor using Nat.strong_induction_on generalizing s with
  | h remaining ih =>
    by_cases hend : s.cursor = I.stageCount
    · have hall : allWritten s.ledger := by
        intro i
        exact hpast i (by rw [hend]; exact i.isLt)
      have hs : Step input C .uncapped accounting tapes s .stop (stopState s false) := .stop s hactive
      refine ⟨stopState s false, .single ⟨.stop, hs⟩, rfl, ?_⟩
      apply (success_iff_physical
        (step_invariant input C .uncapped accounting tapes hs hinv).wellFormed
        (step_deadlineInvariant input C .uncapped accounting tapes htime hs)).mpr
      refine ⟨?_, rfl, ?_⟩
      · simp only [stopState, hall, decide_true]
      · intro i
        apply (finalOutput_correct_iff _ i).mpr
        exact hcorrect i (hall i)
    · have hlt : s.cursor < I.stageCount := lt_of_le_of_ne hcursor.bound hend
      let stage : I.Stage := ⟨s.cursor, hlt⟩
      have finishFromWritten (written : State I)
          (hpath : Relation.ReflTransGen (fun before after => ∃ action,
            Step input C .uncapped accounting tapes before action after) s written)
          (hi : Invariant C written) (ht : DeadlineInvariant C written.ledger written.cursor written.clock)
          (hcu : CursorInvariant written) (ha : written.halted = false)
          (hpa : PastPortsWritten written) (hco : ExistingPhysicallyCorrect written)
          (hcur : written.cursor = s.cursor) (hw : written.ledger.written stage ≠ none) :
          ∃ final : State I,
            Relation.ReflTransGen (fun before after => ∃ action,
              Step input C .uncapped accounting tapes before action after) s final ∧
            final.halted = true ∧ final.ledger.success C := by
        let next := record accounting written (.advance stage) [.advanced stage]
          (advanceLedger written stage) (written.cursor + 1) false
        have hs : Step input C .uncapped accounting tapes written (.advance stage) next :=
          .advance written stage ⟨ha, hcur⟩ hw (Or.inl rfl)
        have hn : I.stageCount - next.cursor < remaining := by
          change I.stageCount - (written.cursor + 1) < remaining
          omega
        have hnextCorrect : ExistingPhysicallyCorrect next := hco
        obtain ⟨final, hp, hh, hc⟩ := ih (I.stageCount - next.cursor) hn next
          (step_invariant input C .uncapped accounting tapes hs hi)
          (step_deadlineInvariant input C .uncapped accounting tapes ht hs)
          (step_cursorInvariant input C .uncapped accounting tapes hcu hs) rfl
          (step_pastPortsWritten input C .uncapped accounting tapes hpa hs) hnextCorrect rfl
        exact ⟨final, hpath.trans ((Relation.ReflTransGen.single ⟨.advance stage, hs⟩).trans hp), hh, hc⟩
      by_cases hopen : s.ledger.written stage = none
      · let written := record accounting s (.write stage (s.ledger.truth stage))
          (writeResponses C s stage (s.ledger.truth stage))
          (reportedWriteLedger C s stage (s.ledger.truth stage)) s.cursor false
        have hs : Step input C .uncapped accounting tapes s (.write stage (s.ledger.truth stage)) written :=
          .write s stage (s.ledger.truth stage) ⟨hactive, rfl⟩ hopen (Or.inl rfl)
        apply finishFromWritten written (.single ⟨.write stage (s.ledger.truth stage), hs⟩)
          (step_invariant input C .uncapped accounting tapes hs hinv)
          (step_deadlineInvariant input C .uncapped accounting tapes htime hs)
          (step_cursorInvariant input C .uncapped accounting tapes hcursor hs) rfl
          (step_pastPortsWritten input C .uncapped accounting tapes hpast hs)
          (truthfulWrite_preserves_existingCorrect C accounting s stage hcorrect) rfl
        dsimp only [written, record, reportedWriteLedger]
        split_ifs <;> simp only [writeLedger, Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true]
      · exact finishFromWritten s .refl hinv htime hcursor hactive hpast hcorrect rfl hopen

end PDROC
