module

public import PaperProofs.Paid.PDROC_Simulator_001
public import PaperProofs.Paid.PDROC_CoordinateCoupling_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u

structure SimulatorCache (I : Instance) where
  seen : List (VisibleEvent I)
  shadow : List (VisibleEvent I)
  chosen : I.Stage → Option AuxiliaryRecord
  deriving Countable

instance simulatorCacheMeasurable (I : Instance) : MeasurableSpace (SimulatorCache I) := ⊤
instance simulatorCacheSingleton (I : Instance) : MeasurableSingletonClass (SimulatorCache I) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

def simulatorInitialCache (I : Instance) : SimulatorCache I := ⟨[], [], fun _ => none⟩

def simulatorEmptyRecord : AuxiliaryRecord := ⟨[], none⟩

def simulatorDrawRecord {I : Instance} (draw : Option (SimulatorDraw I)) : AuxiliaryRecord :=
  (draw.map SimulatorDraw.record).getD simulatorEmptyRecord

def simulatorReviewPacket {I : Instance} (stage : I.Stage) (record : AuxiliaryRecord) :
    List (VisibleEvent I) := record.observations.map (fun symbol => .observation stage symbol.val)

def simulatorAppend {I : Instance} (cache : SimulatorCache I) (event : VisibleEvent I)
    (packet : List (VisibleEvent I)) : SimulatorCache I :=
  { cache with seen := cache.seen ++ [event], shadow := cache.shadow ++ packet }

/-- A causal event transducer. The only truth input is the actual report
event. Auxiliary observations are inserted at the real write/termination;
real observations never enter the virtual controller. -/
def simulatorStep {I : Instance} {SimSeed : Type u}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (cache : SimulatorCache I) (event : VisibleEvent I) : SimulatorCache I :=
  match event with
  | .observation _ _ => simulatorAppend cache event []
  | .wrote stage bit _ =>
      let record := simulatorDrawRecord (draw seed stage cache.shadow)
      let reviews := simulatorReviewPacket stage record
      let serial := (historyActions cache.shadow).length + record.observations.length
      let next := simulatorAppend cache event (reviews ++ [.wrote stage (record.decision.getD bit) serial])
      { next with chosen := Function.update cache.chosen stage (some record) }
  | .report stage truth _ =>
      let record := (cache.chosen stage).getD simulatorEmptyRecord
      let oldBit := record.decision.getD ((historyWritten cache.shadow stage).getD false)
      let realBit := (historyWritten cache.seen stage).getD false
      let virtualTruth := Bool.xor truth (Bool.xor oldBit realBit)
      simulatorAppend cache event [.report stage virtualTruth (historyWriteSerial cache.shadow stage)]
  | .committed handle tool =>
      simulatorAppend cache event [.committed (reserialHandle cache.shadow handle) tool]
  | .executed handle tool =>
      simulatorAppend cache event [.executed (reserialHandle cache.shadow handle) tool]
  | .advanced stage => simulatorAppend cache event [.advanced stage]
  | .stopped | .abandoned =>
      if hstage : historyCursor cache.seen < I.stageCount then
        let stage : I.Stage := ⟨historyCursor cache.seen, hstage⟩
        if historyWritten cache.seen stage = none then
          let record := simulatorDrawRecord (draw seed stage cache.shadow)
          simulatorAppend cache event (simulatorReviewPacket stage record ++ [event])
        else simulatorAppend cache event [event]
      else simulatorAppend cache event [event]

def simulatorReplay {I : Instance} {SimSeed : Type u}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (history : List (VisibleEvent I)) : SimulatorCache I :=
  history.foldl (simulatorStep draw seed) (simulatorInitialCache I)

theorem simulatorStep_seen {I : Instance} {SimSeed : Type u}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (cache : SimulatorCache I) (event : VisibleEvent I) :
    (simulatorStep draw seed cache event).seen = cache.seen ++ [event] := by
  cases event <;> simp only [simulatorStep, simulatorAppend]
  all_goals split_ifs <;> rfl

theorem simulatorStep_shadow_prefix {I : Instance} {SimSeed : Type u}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (cache : SimulatorCache I) (event : VisibleEvent I) :
    cache.shadow.IsPrefix (simulatorStep draw seed cache event).shadow := by
  cases event <;> simp only [simulatorStep, simulatorAppend]
  all_goals (try split_ifs) <;> exact List.prefix_append _ _

theorem simulatorFold_shadow_prefix {I : Instance} {SimSeed : Type u}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (cache : SimulatorCache I) :
    cache.shadow.IsPrefix (history.foldl (simulatorStep draw seed) cache).shadow := by
  induction history generalizing cache with
  | nil => exact List.prefix_refl _
  | cons event rest ih =>
    exact (simulatorStep_shadow_prefix draw seed cache event).trans (ih (simulatorStep draw seed cache event))

theorem simulatorReplay_seen {I : Instance} {SimSeed : Type u}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (history : List (VisibleEvent I)) :
    (simulatorReplay draw seed history).seen = history := by
  have hfold (history : List (VisibleEvent I)) (cache : SimulatorCache I) :
      (history.foldl (simulatorStep draw seed) cache).seen = cache.seen ++ history := by
    induction history generalizing cache with
    | nil => simp
    | cons event rest ih =>
      simp only [List.foldl_cons, ih, simulatorStep_seen, List.append_assoc, List.singleton_append]
  exact hfold history (simulatorInitialCache I)

theorem simulatorReplay_shadow_empty {I : Instance} {SimSeed : Type u}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I)) (seed : SimSeed) :
    (simulatorReplay draw seed []).shadow = [] := rfl

theorem simulatorReplay_shadow_causal {I : Instance} {SimSeed : Type u}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (before after : List (VisibleEvent I)) (hp : before.IsPrefix after) :
    (simulatorReplay draw seed before).shadow.IsPrefix (simulatorReplay draw seed after).shadow := by
  obtain ⟨rest, rfl⟩ := hp
  simp only [simulatorReplay, List.foldl_append]
  exact simulatorFold_shadow_prefix draw seed rest _

end PDROC
