module

public import PaperProofs.Paid.PDROC_OverlaySimulator_008
public import PaperProofs.Paid.PDROC_OverlaySimulator_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

noncomputable def overlayDrawAction (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage)
    (coins : AuxiliaryRecord → Bool × Bool) (draw : Option (SimulatorDraw P.sharedInstance)) : Action P.sharedInstance :=
  match draw with
  | none => .abandon
  | some draw =>
    match draw.record.decision with
    | none => reserialAction history (fun _ bit => bit) draw.action
    | some _ => overlayMixtureAction history stage
        (P.binarySymmetric.rocIndex (P.overlayRecordTarget fee draw.record)
          (P.overlayRecordTarget_pos fee hfee draw.record)) (coins draw.record)

noncomputable def overlayPostwriteAction (P : Parameters) (source : PolicyRule P.sharedInstance Seed)
    (seed : OverlaySeed P Seed) (history : List (VisibleEvent P.sharedInstance)) (cache : SimulatorCache P.sharedInstance) :
    Action P.sharedInstance :=
  reserialAction history (fun _ bit => bit)
    (source seed.1 (cache.shadow ++ overlayGhostEvents (overlaySeedGhost P source seed cache)))

theorem measurable_overlayPostwriteAction_fixed (P : Parameters) (source : PolicyRule P.sharedInstance Seed)
    (hm : MeasurableRule source) (history : List (VisibleEvent P.sharedInstance)) (cache : SimulatorCache P.sharedInstance) :
    Measurable (fun seed => overlayPostwriteAction P source seed history cache) := by
  have hg : Measurable (fun seed : OverlaySeed P Seed => overlaySeedGhost P source seed cache) :=
    (measurable_overlayGhostAtCache_fixed source hm cache).comp measurable_fst
  have hv := (measurable_of_countable (fun calls : List (OverlayGhostCall P.sharedInstance) =>
    cache.shadow ++ overlayGhostEvents calls)).comp hg
  exact (measurable_of_countable (reserialAction history (fun _ bit => bit))).comp
    (hm.comp (measurable_fst.prodMk hv))

noncomputable def overlayCandidateAtCache (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (seed : OverlaySeed P Seed)
    (history : List (VisibleEvent P.sharedInstance)) (cache : SimulatorCache P.sharedInstance) : Action P.sharedInstance :=
  if historyHalted history then .stop else
    match simulatorStageAt history with
    | none => overlayPostwriteAction P source seed history cache
    | some stage =>
      if historyWritten history stage = none then
        overlayDrawAction P fee hfee history stage (overlaySeedCoins P seed stage)
          (overlaySeedDraw P source seed stage cache.shadow)
      else overlayPostwriteAction P source seed history cache

theorem measurable_overlayCandidateAtCache_fixed (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (history : List (VisibleEvent P.sharedInstance)) (cache : SimulatorCache P.sharedInstance) :
    Measurable (fun seed => overlayCandidateAtCache P fee hfee source seed history cache) := by
  by_cases hh : historyHalted history = true
  · simpa only [overlayCandidateAtCache, hh, ite_true] using
      (measurable_const (a := Action.stop) : Measurable (fun _ : OverlaySeed P Seed => Action.stop))
  · simp only [overlayCandidateAtCache, hh, Bool.false_eq_true, ite_false]
    cases hs : simulatorStageAt history with
    | none => exact measurable_overlayPostwriteAction_fixed P source hm history cache
    | some stage =>
      dsimp only
      by_cases hw : historyWritten history stage = none
      · simp only [hw, ite_true]
        have hfixed (draw : Option (SimulatorDraw P.sharedInstance)) :
            Measurable (fun seed : OverlaySeed P Seed =>
              overlayDrawAction P fee hfee history stage (overlaySeedCoins P seed stage) draw) := by
          cases draw with
          | none => exact measurable_const
          | some draw =>
            simp only [overlayDrawAction]
            cases hd : draw.record.decision with
            | none => exact measurable_const
            | some decision =>
              exact (measurable_of_countable (fun coins : Bool × Bool =>
                overlayMixtureAction history stage
                  (P.binarySymmetric.rocIndex (P.overlayRecordTarget fee draw.record)
                    (P.overlayRecordTarget_pos fee hfee draw.record)) coins)).comp
                ((measurable_overlaySeedCoins P stage).comp (measurable_id.prodMk measurable_const))
        have hf : Measurable (fun pair : OverlaySeed P Seed × Option (SimulatorDraw P.sharedInstance) =>
            overlayDrawAction P fee hfee history stage (overlaySeedCoins P pair.1 stage) pair.2) :=
          measurable_from_prod_countable_left hfixed
        exact hf.comp (measurable_id.prodMk ((measurable_overlaySeedDraw P source hm stage).comp
          (measurable_id.prodMk measurable_const)))
      · simpa only [hw, ite_false] using measurable_overlayPostwriteAction_fixed P source hm history cache

noncomputable def overlayCandidate (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) : PolicyRule P.sharedInstance (OverlaySeed P Seed) :=
  fun seed history => overlayCandidateAtCache P fee hfee source seed history (overlaySeedReplay P source seed history)

theorem measurable_overlayCandidate (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) :
    MeasurableRule (overlayCandidate P fee hfee source) := by
  apply measurable_from_prod_countable_left
  intro history
  have hc : Measurable (fun pair : OverlaySeed P Seed × SimulatorCache P.sharedInstance =>
      overlayCandidateAtCache P fee hfee source pair.1 history pair.2) :=
    measurable_from_prod_countable_left (fun cache =>
      measurable_overlayCandidateAtCache_fixed P fee hfee source hm history cache)
  exact hc.comp (measurable_id.prodMk ((measurable_overlaySeedReplay P source hm).comp
    (measurable_id.prodMk measurable_const)))

/-- The output is a genuine uncapped Native controller, with the original
visible permission guard. Correctness and nonbinding guards remain separate
proof obligations; no risk or payment conclusion is a Policy field. -/
noncomputable def overlayRule (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) : PolicyRule P.sharedInstance (OverlaySeed P Seed) :=
  fun seed history =>
    let action := overlayCandidate P fee hfee source seed history
    if historyAllowsAction history action then action else .abandon

theorem measurable_overlayRule (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) :
    MeasurableRule (overlayRule P fee hfee source) :=
  (measurable_of_countable (fun pair : List (VisibleEvent P.sharedInstance) × Action P.sharedInstance =>
    if historyAllowsAction pair.1 pair.2 then pair.2 else .abandon)).comp
      (measurable_snd.prodMk (measurable_overlayCandidate P fee hfee source hm))

omit [MeasurableSpace Seed] in
theorem overlayRule_legal (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) :
    LegalRule (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) := by
  intro seed truth tapes n s hp ha
  by_cases hallow : historyAllowsAction s.history (overlayCandidate P fee hfee source seed s.history)
  · obtain ⟨next, hs⟩ := historyAllowsAction_sound (P.input fee hfee) C.val C.property.1.1 accounting
      (overlayRule P fee hfee source) seed truth tapes hp ha _ hallow
    exact ⟨next, by simpa only [overlayRule, hallow, ite_true] using hs⟩
  · exact ⟨stopState s true, by simpa only [overlayRule, hallow, ite_false] using
      (Step.abandon (input := P.input fee hfee) (C := C.val) (mode := ResourceMode.uncapped)
        (accounting := accounting) (tapes := tapes) s ha)⟩

noncomputable def overlayPolicy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting Seed) :
    Policy (P.input fee hfee) C.val .uncapped accounting (OverlaySeed P Seed) where
  rule := overlayRule P fee hfee source.rule
  measurable_rule := measurable_overlayRule P fee hfee source.rule source.measurable_rule
  legal := overlayRule_legal P fee hfee C accounting source.rule

end PDROC
