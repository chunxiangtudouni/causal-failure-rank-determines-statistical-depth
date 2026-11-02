module

public import PaperProofs.Paid.PDROC_SourceTerminal_002
public import PaperProofs.Paid.PDROC_Postwrite_001
public import PaperProofs.Paid.PDROC_SimulatorLaw_014

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {I : Instance} {Seed : Type u}

/-- Only a generated, active terminal-cursor exit requests a source tail
permission. Never-entry remains an irrelevant analysis completion. -/
def terminalExitTailAllowedFlag (source : PolicyRule I Seed)
    (result : (Seed × EntryHistory I) × EntryHistory I) : Bool :=
  match result.2 with
  | none => true
  | some history =>
      if result.1.2.isSome = true ∧ historyCursor history = I.stageCount ∧ historyHalted history = false then
        decide (historyAllowsAction history (source result.1.1 history))
      else true

theorem measurable_terminalExitTailAllowedFlag [MeasurableSpace Seed]
    (source : PolicyRule I Seed) (hm : MeasurableRule source) :
    Measurable (terminalExitTailAllowedFlag source) := by
  let build := fun pair : Seed × (EntryHistory I × EntryHistory I) =>
    terminalExitTailAllowedFlag source ((pair.1, pair.2.1), pair.2.2)
  have hb : Measurable build := by
    apply measurable_from_prod_countable_left
    rintro ⟨prior, exit⟩
    cases exit with
    | none => exact measurable_const
    | some history =>
      change Measurable (fun seed : Seed =>
        if prior.isSome = true ∧ historyCursor history = I.stageCount ∧ historyHalted history = false then
          decide (historyAllowsAction history (source seed history)) else true)
      by_cases hg : prior.isSome = true ∧ historyCursor history = I.stageCount ∧ historyHalted history = false
      · simp only [ite_eq_left hg]
        exact (measurable_of_countable (fun action : Action I => decide (historyAllowsAction history action))).comp
          (hm.comp (measurable_id.prodMk measurable_const))
      · simp only [ite_eq_right hg]
        exact measurable_const
  exact hb.comp (((measurable_fst.comp measurable_fst)).prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

theorem terminalExitTailAllowedFlag_permission (source : PolicyRule I Seed)
    (result : (Seed × EntryHistory I) × EntryHistory I) (history : List (VisibleEvent I))
    (hx : result.2 = some history) (hp : result.1.2.isSome = true)
    (hc : historyCursor history = I.stageCount) (hh : historyHalted history = false)
    (hg : terminalExitTailAllowedFlag source result = true) :
    historyAllowsAction history (source result.1.1 history) := by
  simpa only [terminalExitTailAllowedFlag, hx, hp, hc, hh, and_self, ↓reduceIte, decide_eq_true_eq] using hg

variable [MeasurableSpace Seed]

/-- The final tail permission is proved on the actual source's full exit
law using true Native Prefixes, then expressed as a measurable flag. -/
theorem sourceEventualStageExit_tailAllowed_ae (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤) :
    ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw ν,
      terminalExitTailAllowedFlag source.rule (sourceEventualStageExitSome P fee hfee C accounting source stage sample) = true := by
  filter_upwards [sourceEventualStageSample_finite_ae P fee hfee C accounting source ν stage hfinite] with sample hs
  let result := sourceEventualStageExitSome P fee hfee C accounting source stage sample
  let history := (sourceEventualStageExit P fee hfee C accounting source stage sample).2
  have hx : result.2 = some history := rfl
  change terminalExitTailAllowedFlag source.rule result = true
  rw [terminalExitTailAllowedFlag, hx]
  change (if result.1.2.isSome = true ∧ historyCursor history = P.sharedInstance.stageCount ∧ historyHalted history = false then
    decide (historyAllowsAction history (source.rule result.1.1 history)) else true) = true
  by_cases hg : result.1.2.isSome = true ∧ historyCursor history = P.sharedInstance.stageCount ∧ historyHalted history = false
  · rw [ite_eq_left hg, decide_eq_true_eq]
    have hseed := sourceEventualStageExitSome_seed P fee hfee C accounting source stage sample
    have hpriorEq : result.1.2 = entryHistory (P.input fee hfee) C.val .uncapped accounting source.rule stage sample :=
      congrArg Prod.snd hseed
    have hprior : (entryHistory (P.input fee hfee) C.val .uncapped accounting source.rule stage sample).isSome = true := by
      rw [← hpriorEq]
      exact hg.1
    cases he : entryHistory (P.input fee hfee) C.val .uncapped accounting source.rule stage sample with
    | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at hprior
    | some entry =>
      obtain ⟨clock, hclock, _⟩ := sourceEventualStageExitSome_actual_exit_of_finite P fee hfee C accounting source stage sample hs entry he
      have hhistory : (run (P.input fee hfee) C.val .uncapped accounting source.rule sample clock).history = history :=
        Option.some.inj (hclock.symm.trans hx)
      obtain ⟨n, _, hp⟩ := run_has_prefix (P.input fee hfee) C.val .uncapped accounting source.rule source.legal sample clock
      have ha : (run (P.input fee hfee) C.val .uncapped accounting source.rule sample clock).halted = false := by
        have hh := prefix_historyHalted (P.input fee hfee) C.val .uncapped accounting source.rule sample.1 _ _ hp
        rw [hhistory] at hh
        exact hh.symm.trans hg.2.2
      have hstep := run_actualStep_of_active (P.input fee hfee) C.val .uncapped accounting source.rule source.legal sample clock ha
      have hallow := historyAllowsAction_of_step (P.input fee hfee) C.val C.property .uncapped accounting
        source.rule sample.1 _ _ hp hstep
      rw [hhistory] at hallow
      rw [show result.1.1 = sample.1 from congrArg Prod.fst hseed]
      exact hallow
  · simp only [ite_eq_right hg]

/-- Transfer only the measurable permission flag under the proved full
stage-exit joint law. No semantic source-world range or RCP is used. -/
theorem simulatorEventualStageExit_tailAllowed_ae_of_entryLaw
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hentry : ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
      (simulatorVirtualEntryGate P fee hfee C accounting source.rule stage) =
        sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage) :
    ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν),
      terminalExitTailAllowedFlag source.rule (simulatorEventualStageExit P fee hfee C accounting source.rule stage sample) = true := by
  have hp := (measurable_terminalExitTailAllowedFlag source.rule source.measurable_rule) (measurableSet_singleton true)
  have hsource : ∀ᵐ result ∂((P.input fee hfee).seededWorldLaw ν).map
      (sourceEventualStageExitSome P fee hfee C accounting source stage), terminalExitTailAllowedFlag source.rule result = true :=
    (ae_map_iff (measurable_sourceEventualStageExitSome P fee hfee C accounting source stage).aemeasurable hp).mpr
      (sourceEventualStageExit_tailAllowed_ae P fee hfee C accounting source ν stage hfinite)
  rw [← simulatorEventualStageExit_law_of_entryLaw P fee hfee C accounting source ν stage hfinite hentry] at hsource
  exact ae_of_ae_map (measurable_simulatorEventualStageExit P fee hfee C accounting source.rule source.measurable_rule stage).aemeasurable hsource

end PDROC
