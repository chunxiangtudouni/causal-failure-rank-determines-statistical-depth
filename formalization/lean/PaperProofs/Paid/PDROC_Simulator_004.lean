module

public import PaperProofs.Paid.PDROC_Simulator_003
public import PaperProofs.Paid.PDROC_CoordinateCoupling_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

def simulatorObservedScore {I : Instance} (history : List (VisibleEvent I)) (stage : I.Stage) : ℤ :=
  ((historyObservations history stage).map (fun symbol => if symbol = 1 then (1 : ℤ) else -1)).sum

def simulatorBoundaryAction {I : Instance} (history : List (VisibleEvent I))
    (stage : I.Stage) (record : AuxiliaryRecord) (coin : Bool) : Action I :=
  match record.decision with
  | none => .abandon
  | some decision =>
      if record.level = 0 then .write stage (Bool.xor decision (Bool.xor record.orientation coin))
      else if record.level ≤ (simulatorObservedScore history stage).natAbs then
        .write stage (Bool.xor decision (Bool.xor record.orientation (decide (0 ≤ simulatorObservedScore history stage))))
      else .review stage

def simulatorDrawAction {I : Instance} (history : List (VisibleEvent I)) (stage : I.Stage)
    (coin : Bool) (draw : Option (SimulatorDraw I)) : Action I :=
  match draw with
  | none => .abandon
  | some draw => match draw.record.decision with
    | none => reserialAction history (fun _ bit => bit) draw.action
    | some _ => simulatorBoundaryAction history stage draw.record coin

def simulatorStageAt {I : Instance} (history : List (VisibleEvent I)) : Option I.Stage :=
  if hstage : historyCursor history < I.compatibility.length then
    some ⟨historyCursor history, hstage⟩ else none

def simulatorCandidateFromData {I : Instance} (history : List (VisibleEvent I))
    (action : Action I) (draws : I.Stage → Option (SimulatorDraw I)) (coins : I.Stage → Bool) : Action I :=
  if historyHalted history then .stop else
  match simulatorStageAt history with
  | some stage =>
    if historyWritten history stage = none then
      simulatorDrawAction history stage (coins stage) (draws stage)
    else reserialAction history (fun _ bit => bit) action
  | none => reserialAction history (fun _ bit => bit) action

noncomputable def simulatorCandidateAtCache (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed)
    (history : List (VisibleEvent P.sharedInstance)) (cache : SimulatorCache P.sharedInstance) :
    Action P.sharedInstance :=
  simulatorCandidateFromData history (source seed.1 cache.shadow)
    (fun stage => simulatorSeedDraw P fee hfee source seed stage cache.shadow) seed.2.2

theorem measurable_simulatorCandidateAtCache_fixed (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (history : List (VisibleEvent P.sharedInstance)) (cache : SimulatorCache P.sharedInstance) :
    Measurable (fun seed => simulatorCandidateAtCache P fee hfee source seed history cache) := by
  have ha : Measurable (fun seed : SimulatorSeed P Seed => source seed.1 cache.shadow) :=
    hm.comp (measurable_fst.prodMk measurable_const)
  have hd : Measurable (fun seed : SimulatorSeed P Seed =>
      fun stage => simulatorSeedDraw P fee hfee source seed stage cache.shadow) := by
    apply measurable_pi_iff.mpr
    intro stage
    exact (measurable_simulatorSeedDraw P fee hfee source hm stage).comp
      (measurable_id.prodMk measurable_const)
  have hb : Measurable (fun seed : SimulatorSeed P Seed => seed.2.2) :=
    measurable_snd.comp measurable_snd
  exact (measurable_of_countable (fun data : Action P.sharedInstance ×
      ((P.sharedInstance.Stage → Option (SimulatorDraw P.sharedInstance)) × (P.sharedInstance.Stage → Bool)) =>
    simulatorCandidateFromData history data.1 data.2.1 data.2.2)).comp (ha.prodMk (hd.prodMk hb))

noncomputable def simulatorCandidate (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) : PolicyRule P.sharedInstance (SimulatorSeed P Seed) :=
  fun seed history => simulatorCandidateAtCache P fee hfee source seed history
    (simulatorReplay (simulatorSeedDraw P fee hfee source) seed history)

theorem measurable_simulatorCandidate (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) :
    MeasurableRule (simulatorCandidate P fee hfee source) := by
  apply measurable_from_prod_countable_left
  intro history
  have he : Measurable (fun seed : SimulatorSeed P Seed => (seed, history)) :=
    measurable_id.prodMk measurable_const
  have hcache := (measurable_simulatorReplay (simulatorSeedDraw P fee hfee source)
    (measurable_simulatorSeedDraw P fee hfee source hm)).comp he
  dsimp only [Function.comp_def] at hcache
  have hc : Measurable (fun pair : SimulatorSeed P Seed × SimulatorCache P.sharedInstance =>
      simulatorCandidateAtCache P fee hfee source pair.1 history pair.2) :=
    measurable_from_prod_countable_left (fun cache =>
      measurable_simulatorCandidateAtCache_fixed P fee hfee source hm history cache)
  have hx : Measurable (fun seed : SimulatorSeed P Seed =>
      (seed, simulatorReplay (simulatorSeedDraw P fee hfee source) seed history)) :=
    measurable_id.prodMk hcache
  have h := hc.comp hx
  simpa only [simulatorCandidate, Function.comp_def] using h

/-- The concrete simulator is an actual legal Native policy on every path.
The existing visible permission guard adds abandonment on malformed paths;
its nonbinding behavior and full-history law remain separate obligations. -/
noncomputable def simulatorRule (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) : PolicyRule P.sharedInstance (SimulatorSeed P Seed) :=
  fun seed history =>
    let action := simulatorCandidate P fee hfee source seed history
    if historyAllowsAction history action then action else .abandon

theorem measurable_simulatorRule (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) :
    MeasurableRule (simulatorRule P fee hfee source) :=
  (measurable_of_countable (fun pair : List (VisibleEvent P.sharedInstance) × Action P.sharedInstance =>
    if historyAllowsAction pair.1 pair.2 then pair.2 else .abandon)).comp
      (measurable_snd.prodMk (measurable_simulatorCandidate P fee hfee source hm))

omit [MeasurableSpace Seed] in
theorem simulatorRule_legal (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) :
    LegalRule (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) := by
  intro seed truth tapes n s hp ha
  by_cases hallow : historyAllowsAction s.history (simulatorCandidate P fee hfee source seed s.history)
  · obtain ⟨next, hs⟩ := historyAllowsAction_sound (P.input fee hfee) C.val C.property.1.1 accounting
      (simulatorRule P fee hfee source) seed truth tapes hp ha _ hallow
    exact ⟨next, by simpa only [simulatorRule, hallow, ↓reduceIte] using hs⟩
  · exact ⟨stopState s true, by simpa only [simulatorRule, hallow, ↓reduceIte] using
      (Step.abandon (input := P.input fee hfee) (C := C.val) (mode := ResourceMode.uncapped)
        (accounting := accounting) (tapes := tapes) s ha)⟩

noncomputable def simulatorPolicy (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed) :
    Policy (P.input fee hfee) C.val .uncapped accounting (SimulatorSeed P Seed) where
  rule := simulatorRule P fee hfee source.rule
  measurable_rule := measurable_simulatorRule P fee hfee source.rule source.measurable_rule
  legal := simulatorRule_legal P fee hfee C accounting source.rule

noncomputable def simulatorData (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) : RecordSimulatorData P.sharedInstance Seed (SimulatorSeed P Seed) where
  sourceSeed := Prod.fst
  shadow := simulatorShadow P fee hfee source
  record := fun seed stage entry => simulatorDrawRecord
    (simulatorSeedDraw P fee hfee source seed stage (simulatorShadow P fee hfee source seed entry))
  endpointCoin := fun seed stage => seed.2.2 stage
  mixtureCoins := fun seed stage => (seed.2.2 stage, seed.2.2 stage)
  falsePositiveCoin := fun _ _ => false

omit [MeasurableSpace Seed] in
theorem simulatorData_shadowCausal (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) : P.ShadowCausal (simulatorData P fee hfee source) := by
  refine ⟨fun _ => rfl, ?_⟩
  exact simulatorReplay_shadow_causal (simulatorSeedDraw P fee hfee source)

theorem simulatorData_measurable (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) :
    RecordSimulatorMeasurable (simulatorData P fee hfee source) := by
  have hs := measurable_simulatorShadow P fee hfee source hm
  refine ⟨measurable_fst, hs, ?_, ?_, ?_, fun _ => measurable_const⟩
  · intro stage
    exact (measurable_of_countable simulatorDrawRecord).comp
      ((measurable_simulatorSeedDraw P fee hfee source hm stage).comp (measurable_fst.prodMk hs))
  · intro stage
    exact (measurable_pi_apply stage).comp (measurable_snd.comp measurable_snd)
  · intro stage
    exact ((measurable_pi_apply stage).comp (measurable_snd.comp measurable_snd)).prodMk
      ((measurable_pi_apply stage).comp (measurable_snd.comp measurable_snd))

end PDROC
