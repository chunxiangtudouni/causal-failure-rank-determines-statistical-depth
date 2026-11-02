module

public import PaperProofs.Paid.PDROC_SimulatorLaw_006
public import PaperProofs.Paid.PDROC_Postwrite_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {I : Instance} {Seed : Type u}

/-- Only finitely many visible guard queries are needed to realize a full
postwrite stage. This predicate has no existential hidden-world witness. -/
def sourcePostwriteGuardGood (source : PolicyRule I Seed) (seed : Seed) (stage : I.Stage)
    (history : List (VisibleEvent I)) : Prop :=
  ∀ k : ℕ, k < 3 →
    historyHalted (postwriteStageTrace source seed stage history k) = false →
    historyCursor (postwriteStageTrace source seed stage history k) = stage.val →
    historyAllowsAction (postwriteStageTrace source seed stage history k)
      (source seed (postwriteStageTrace source seed stage history k))

theorem measurableSet_sourcePostwriteGuardGood [MeasurableSpace Seed]
    (source : PolicyRule I Seed) (hm : MeasurableRule source) (stage : I.Stage) :
    MeasurableSet {sample : Seed × List (VisibleEvent I) |
      sourcePostwriteGuardGood source sample.1 stage sample.2} := by
  have each (k : ℕ) : MeasurableSet {sample : Seed × List (VisibleEvent I) |
      k < 3 → historyHalted (postwriteStageTrace source sample.1 stage sample.2 k) = false →
      historyCursor (postwriteStageTrace source sample.1 stage sample.2 k) = stage.val →
      historyAllowsAction (postwriteStageTrace source sample.1 stage sample.2 k)
        (source sample.1 (postwriteStageTrace source sample.1 stage sample.2 k))} := by
    have ht := measurable_postwriteStageTrace source hm stage k
    have ha := hm.comp (measurable_fst.prodMk ht)
    have hc : MeasurableSet {pair : List (VisibleEvent I) × Action I |
        k < 3 → historyHalted pair.1 = false → historyCursor pair.1 = stage.val →
          historyAllowsAction pair.1 pair.2} := (Set.to_countable _).measurableSet
    exact hc.preimage (ht.prodMk ha)
  simpa only [sourcePostwriteGuardGood, Set.ofPred_forall] using MeasurableSet.iInter each

theorem sourcePostwriteGuardGood_of_halted (source : PolicyRule I Seed) (seed : Seed) (stage : I.Stage)
    (history : List (VisibleEvent I)) (hh : historyHalted history = true) :
    sourcePostwriteGuardGood source seed stage history := by
  intro k _hk ha
  rw [postwriteStageTrace_of_halted seed stage history hh k, hh] at ha
  cases ha

/-- Every finite transducer prefix is an actual original source history,
freezing once the source leaves the specified written stage. -/
theorem postwriteStageTrace_eq_run_at_or_before (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hl : LegalRule input C mode accounting source) (sample : Seed × input.World)
    (start : ℕ) (stage : I.Stage)
    (hw : (run input C mode accounting source sample start).ledger.written stage ≠ none) (k : ℕ) :
    ∃ clock : ℕ, start ≤ clock ∧ clock ≤ start + k ∧
      postwriteStageTrace source sample.1 stage (run input C mode accounting source sample start).history k =
        (run input C mode accounting source sample clock).history := by
  induction k with
  | zero => exact ⟨start, le_rfl, by omega, rfl⟩
  | succ k ih =>
    obtain ⟨clock, hlo, hhi, hhistory⟩ := ih
    rw [postwriteStageTrace, hhistory]
    obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting source hl sample clock
    have hh := prefix_historyHalted input C mode accounting source sample.1 _ _ hp
    have hc := prefix_historyCursor input C mode accounting source sample.1 _ _ hp
    by_cases hhalt : (run input C mode accounting source sample clock).halted = true
    · refine ⟨clock, hlo, by omega, ?_⟩
      simp only [postwriteStageStep, hh, hhalt, ↓reduceIte]
    · have ha : (run input C mode accounting source sample clock).halted = false := Bool.eq_false_iff.mpr hhalt
      by_cases hcursor : (run input C mode accounting source sample clock).cursor = stage.val
      · obtain ⟨bit, hbit⟩ := Option.ne_none_iff_exists'.mp hw
        have hwNow : (run input C mode accounting source sample clock).ledger.written stage ≠ none := by
          have htime : start + (clock - start) = clock := by omega
          have hpersist := run_written_some_after input C mode accounting source hl sample start
            (clock - start) stage bit hbit
          rw [htime] at hpersist
          rw [hpersist]
          simp only [ne_eq, reduceCtorEq, not_false_eq_true]
        have hs := run_actualStep_of_active input C mode accounting source hl sample clock ha
        refine ⟨clock + 1, by omega, by omega, ?_⟩
        exact postwriteStageStep_eq_nextHistory input C mode accounting source sample.1 _ _ stage hp ha hcursor hwNow hs
      · refine ⟨clock, hlo, by omega, ?_⟩
        simp only [postwriteStageStep, hh, ha, Bool.false_eq_true, ↓reduceIte, hc,
          ite_eq_right hcursor]

/-- This measurable visible guard condition is proved on every original
written-stage run, including failures and arbitrary later spending. -/
theorem sourcePostwriteGuardGood_of_run (input : StatisticalInput I) (C : Contract I)
    (hpay : C.IsCurrentPayment) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hl : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (start : ℕ) (stage : I.Stage)
    (hw : (run input C mode accounting source sample start).ledger.written stage ≠ none) :
    sourcePostwriteGuardGood source sample.1 stage (run input C mode accounting source sample start).history := by
  intro k _hk hactive _hcursor
  obtain ⟨clock, _, _, hhistory⟩ := postwriteStageTrace_eq_run_at_or_before input C mode accounting source hl sample start stage hw k
  rw [hhistory] at hactive ⊢
  obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting source hl sample clock
  rw [prefix_historyHalted input C mode accounting source sample.1 _ _ hp] at hactive
  have hs := run_actualStep_of_active input C mode accounting source hl sample clock hactive
  exact historyAllowsAction_of_step input C hpay mode accounting source sample.1 _ _ hp hs

end PDROC
