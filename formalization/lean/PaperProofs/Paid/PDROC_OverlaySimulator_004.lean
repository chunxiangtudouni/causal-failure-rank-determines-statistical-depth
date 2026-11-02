module

public import PaperProofs.Paid.PDROC_OverlaySimulator_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

instance overlayGhostCallsMeasurable (I : Instance) : MeasurableSpace (List (OverlayGhostCall I)) := ⊤

instance overlayGhostCallsSingleton (I : Instance) : MeasurableSingletonClass (List (OverlayGhostCall I)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

universe u
variable {I : Instance} {SimSeed : Type u} [MeasurableSpace SimSeed]

theorem measurable_overlayStep_fixed
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (hd : ∀ stage, Measurable (fun pair : SimSeed × List (VisibleEvent I) => draw pair.1 stage pair.2))
    (hm : ∀ stage record, Measurable (fun seed => mark seed stage record))
    (hg : ∀ cache, Measurable (fun seed => ghost seed cache))
    (cache : SimulatorCache I) (event : VisibleEvent I) :
    Measurable (fun seed => overlayStep draw mark ghost seed cache event) := by
  have hdraw (stage : I.Stage) : Measurable (fun seed => draw seed stage cache.shadow) :=
    (hd stage).comp (measurable_id.prodMk measurable_const)
  cases event with
  | observation | committed | executed => exact measurable_const
  | wrote stage bit serial =>
    exact measurable_simulatorStep_fixed draw hd cache (.wrote stage bit serial)
  | report stage truth serial =>
    exact (measurable_of_countable (fun flag : Bool =>
      simulatorAppend cache (.report stage truth serial) [.report stage
        (overlayReportTruth ((historyWritten cache.seen stage).getD false)
          (((cache.chosen stage).getD simulatorEmptyRecord).decision.getD
            ((historyWritten cache.shadow stage).getD false)) truth flag)
        (historyWriteSerial cache.shadow stage)])).comp
      (hm stage ((cache.chosen stage).getD simulatorEmptyRecord))
  | advanced stage =>
    exact (measurable_of_countable (fun calls : List (OverlayGhostCall I) =>
      simulatorAppend cache (.advanced stage) (overlayGhostEvents calls ++ [VisibleEvent.advanced stage]))).comp (hg cache)
  | stopped | abandoned =>
    simp only [overlayStep]
    split_ifs
    all_goals first
    | exact (measurable_of_countable (fun data : Option (SimulatorDraw I) × List (OverlayGhostCall I) =>
        simulatorAppend cache _ (simulatorReviewPacket _ (simulatorDrawRecord data.1) ++
          overlayGhostEvents data.2 ++ [_]))).comp ((hdraw _).prodMk (hg cache))
    | exact (measurable_of_countable (fun calls : List (OverlayGhostCall I) =>
        simulatorAppend cache _ (overlayGhostEvents calls ++ [_]))).comp (hg cache)

theorem measurable_overlayStep
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (hd : ∀ stage, Measurable (fun pair : SimSeed × List (VisibleEvent I) => draw pair.1 stage pair.2))
    (hm : ∀ stage record, Measurable (fun seed => mark seed stage record))
    (hg : ∀ cache, Measurable (fun seed => ghost seed cache))
    (event : VisibleEvent I) :
    Measurable (fun pair : SimSeed × SimulatorCache I => overlayStep draw mark ghost pair.1 pair.2 event) :=
  measurable_from_prod_countable_left (fun cache => measurable_overlayStep_fixed draw mark ghost hd hm hg cache event)

theorem measurable_overlayFold
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (hd : ∀ stage, Measurable (fun pair : SimSeed × List (VisibleEvent I) => draw pair.1 stage pair.2))
    (hm : ∀ stage record, Measurable (fun seed => mark seed stage record))
    (hg : ∀ cache, Measurable (fun seed => ghost seed cache))
    (history : List (VisibleEvent I)) :
    Measurable (fun pair : SimSeed × SimulatorCache I => history.foldl (overlayStep draw mark ghost pair.1) pair.2) := by
  induction history with
  | nil => exact measurable_snd
  | cons event rest ih =>
    exact ih.comp (measurable_fst.prodMk (measurable_overlayStep draw mark ghost hd hm hg event))

theorem measurable_overlayReplay
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (hd : ∀ stage, Measurable (fun pair : SimSeed × List (VisibleEvent I) => draw pair.1 stage pair.2))
    (hm : ∀ stage record, Measurable (fun seed => mark seed stage record))
    (hg : ∀ cache, Measurable (fun seed => ghost seed cache)) :
    Measurable (fun pair : SimSeed × List (VisibleEvent I) => overlayReplay draw mark ghost pair.1 pair.2) := by
  apply measurable_from_prod_countable_left
  intro history
  have h := (measurable_overlayFold draw mark ghost hd hm hg history).comp
    (measurable_id.prodMk (measurable_const (a := simulatorInitialCache I)))
  simpa only [overlayReplay, Function.comp_def, id_eq] using h

end PDROC
