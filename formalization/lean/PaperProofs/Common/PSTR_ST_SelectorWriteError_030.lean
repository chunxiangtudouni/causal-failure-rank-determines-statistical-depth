module

public import PaperProofs.Common.PSTR_ST_SelectorBranch_028
public import PaperProofs.Common.PSTR_ST_SelectorDecision_029
public import PaperProofs.Common.PSTR_ST_SelectorObservation_026

/-! Original local target bound for every actual wrong ordinary first-stage
write, including null entries and later failed paths. This is the probability
factor used for the fixed inherited bad continuation in the fee recurrence. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.PSTRStatistics.MaxSelector.WriteError

open PaperProofs.Statistics

variable {I : Instance}

private theorem prefix_eq_run_sample  (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Unit) (sample : Unit × input.World)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting rule sample.1 (input.truthAt sample.2)
      (worldTapes input sample.2) n s) : run input C .uncapped accounting rule sample n = s := by
  have he := prefix_eq_run input C .uncapped accounting rule sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp
  have hw : replayWorld input (input.truthAt sample.2) (worldTapes input sample.2) = sample.2 := rfl
  simpa only [hw] using he

/-- The original run has at some time an actually wrong ordinary bit.
Repairs never modify this event or rewrite the ordinary ledger. -/
theorem measurableSet_selectorStageWriteError (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ) (stage : I.Stage) :
    MeasurableSet (Branch.selectorStageWriteError input C accounting available selector budget stage) := by
  have heq : Branch.selectorStageWriteError input C accounting available selector budget stage =
      ⋃ n : ℕ, {sample : Unit × input.World |
        let s := run input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) sample n
        s.ledger.written stage = some (!s.ledger.truth stage)} := by
    ext sample
    simp only [Branch.selectorStageWriteError, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [heq]
  apply MeasurableSet.iUnion
  intro n
  exact (measurable_run input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none)
    ((measurable_of_countable (fun history => MaxSelector.rule selector.choose input available budget none () history)).comp measurable_snd) n)
    (MeasurableSpace.measurableSet_top (s := {s : State I | s.ledger.written stage = some (!s.ledger.truth stage)}))

/-- On a finite-target entry, any actual wrong ordinary bit belongs to the
same genuine posterior-write error event already bounded by the entry kernel. -/
theorem selectorStageWriteError_on_entry_subset
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (stage : I.Stage) (history : List (VisibleEvent I)) (p : ℚ)
    (htarget : Origin.selectorEntryTarget input available selector budget history = some p) :
    Branch.selectorStageWriteError input C accounting available selector budget stage ∩
        {sample | entryHistory input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) stage sample = some history} ⊆
      Decision.selectorStagePosteriorError input C hearly accounting available selector budget stage ∩
        {sample | entryHistory input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) stage sample = some history} := by
  rintro ⟨⟨⟩, world⟩ ⟨⟨n, hw⟩, hentry⟩
  have hlegal := rule_uncapped_legal selector.choose input C hearly accounting available budget none
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) hlegal ((), world) n
  obtain ⟨m, old, _, hpold, hactive, hwrite⟩ := prefix_written_has_write input C .uncapped accounting
    (MaxSelector.rule selector.choose input available budget none) () (input.truthAt world) (worldTapes input world) hp stage _ hw
  have ht := congrFun (run_truth input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) hlegal ((), world) n) stage
  have hwrong : (!(run input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) ((), world) n).ledger.truth stage) ≠
      (world stage).1 := by
    rw [ht]
    exact Bool.not_ne_self _
  refine ⟨⟨m, (!(run input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) ((), world) n).ledger.truth stage), history, p, ?_⟩, hentry⟩
  dsimp only [Decision.selectorIdealPolicy, policy]
  rw [prefix_eq_run_sample input C accounting (MaxSelector.rule selector.choose input available budget none) ((), world) hpold]
  exact ⟨hactive, hwrite, hentry, htarget, hwrong⟩

theorem selectorStageWriteError_on_entry_le
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage)
    (history : List (VisibleEvent I)) (p : ℚ)
    (htarget : Origin.selectorEntryTarget input available selector budget history = some p) :
    input.seededWorldLaw (Measure.dirac ())
      (Branch.selectorStageWriteError input C accounting available selector budget stage ∩
        {sample | entryHistory input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) stage sample = some history}) ≤
      ENNReal.ofReal (p : ℝ) * input.seededWorldLaw (Measure.dirac ())
        {sample | entryHistory input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) stage sample = some history} :=
  (measure_mono (selectorStageWriteError_on_entry_subset input C hearly accounting available selector budget stage history p htarget)).trans
    (Decision.selectorStagePosteriorError_on_entry_le input C hearly accounting available selector budget hbudget hsmall stage history p htarget)


/-- Actual ordinary wrong-write mass at the original first-stage target.
No success gate or positive-entry-mass division is introduced. -/
theorem selectorFirstStageWriteError_le (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (first : I.Stage) (hfirst : first.val = 0) (p : ℚ)
    (htarget : referenceAvailableEntryTarget input available budget [] = some p) :
    input.seededWorldLaw (Measure.dirac ())
      (Branch.selectorStageWriteError input C accounting available selector budget first) ≤
        ENNReal.ofReal (p : ℝ) := by
  have htarget' := (Fees.selectorEntryTarget_initial input available selector budget hbudget hsmall).trans htarget
  have hentry : {sample : Unit × input.World | entryHistory input C .uncapped accounting
      (MaxSelector.rule selector.choose input available budget none) first sample = some []} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro sample
    exact entryHistory_stageZero input C .uncapped accounting _ first hfirst sample
  have hb := selectorStageWriteError_on_entry_le input C hearly accounting available selector budget
    hbudget hsmall first [] p htarget'
  simpa only [hentry, Set.inter_univ, measure_univ, mul_one] using hb

end PaperProofs.Common.Native.PSTRStatistics.MaxSelector.WriteError
