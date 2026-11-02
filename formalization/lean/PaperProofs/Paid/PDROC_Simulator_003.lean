module

public import PaperProofs.Paid.PDROC_Simulator_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u

variable {I : Instance} {SimSeed : Type u} [MeasurableSpace SimSeed]

theorem measurable_simulatorStep_fixed
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (hm : ∀ stage, Measurable (fun pair : SimSeed × List (VisibleEvent I) => draw pair.1 stage pair.2))
    (cache : SimulatorCache I) (event : VisibleEvent I) :
    Measurable (fun seed => simulatorStep draw seed cache event) := by
  have hd (stage : I.Stage) : Measurable (fun seed => draw seed stage cache.shadow) :=
    (hm stage).comp (measurable_id.prodMk measurable_const)
  cases event with
  | observation | report | committed | executed | advanced => exact measurable_const
  | wrote stage bit serial =>
    exact (measurable_of_countable (fun chosen : Option (SimulatorDraw I) =>
      let record := simulatorDrawRecord chosen
      let next := simulatorAppend cache (.wrote stage bit serial)
        (simulatorReviewPacket stage record ++ [.wrote stage (record.decision.getD bit)
          ((historyActions cache.shadow).length + record.observations.length)])
      { next with chosen := Function.update cache.chosen stage (some record) })).comp (hd stage)
  | stopped | abandoned =>
    simp only [simulatorStep]
    split_ifs <;> try exact measurable_const
    all_goals
      exact (measurable_of_countable (fun chosen : Option (SimulatorDraw I) =>
        simulatorAppend cache _ (simulatorReviewPacket _ (simulatorDrawRecord chosen) ++ [_]))).comp (hd _)

theorem measurable_simulatorStep
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (hm : ∀ stage, Measurable (fun pair : SimSeed × List (VisibleEvent I) => draw pair.1 stage pair.2))
    (event : VisibleEvent I) :
    Measurable (fun pair : SimSeed × SimulatorCache I => simulatorStep draw pair.1 pair.2 event) :=
  measurable_from_prod_countable_left (fun cache => measurable_simulatorStep_fixed draw hm cache event)

theorem measurable_simulatorFold
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (hm : ∀ stage, Measurable (fun pair : SimSeed × List (VisibleEvent I) => draw pair.1 stage pair.2))
    (history : List (VisibleEvent I)) :
    Measurable (fun pair : SimSeed × SimulatorCache I => history.foldl (simulatorStep draw pair.1) pair.2) := by
  induction history with
  | nil => exact measurable_snd
  | cons event rest ih =>
    exact ih.comp (measurable_fst.prodMk (measurable_simulatorStep draw hm event))

theorem measurable_simulatorReplay
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (hm : ∀ stage, Measurable (fun pair : SimSeed × List (VisibleEvent I) => draw pair.1 stage pair.2)) :
    Measurable (fun pair : SimSeed × List (VisibleEvent I) => simulatorReplay draw pair.1 pair.2) := by
  apply measurable_from_prod_countable_left
  intro history
  have hi : Measurable (fun seed : SimSeed => (seed, simulatorInitialCache I)) :=
    measurable_id.prodMk measurable_const
  have h := (measurable_simulatorFold draw hm history).comp hi
  simpa only [simulatorReplay, Function.comp_def] using h

variable {Seed : Type u} [MeasurableSpace Seed]

noncomputable def simulatorSeedDraw (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed)
    (stage : P.sharedInstance.Stage) (entry : List (VisibleEvent P.sharedInstance)) :
    Option (SimulatorDraw P.sharedInstance) :=
  simulatorDrawAt P fee hfee source stage seed.1 entry (seed.2.1 stage)

theorem measurable_simulatorSeedDraw (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (fun pair : SimulatorSeed P Seed × List (VisibleEvent P.sharedInstance) =>
      simulatorSeedDraw P fee hfee source pair.1 stage pair.2) := by
  have ht : Measurable (fun pair : SimulatorSeed P Seed × List (VisibleEvent P.sharedInstance) =>
      pair.1.2.1 stage) :=
    (measurable_pi_apply stage).comp ((measurable_fst.comp measurable_snd).comp measurable_fst)
  exact (measurable_simulatorDrawAt P fee hfee source hm stage).comp
    (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk ht)

noncomputable def simulatorShadow (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed)
    (history : List (VisibleEvent P.sharedInstance)) : List (VisibleEvent P.sharedInstance) :=
  (simulatorReplay (simulatorSeedDraw P fee hfee source) seed history).shadow

theorem measurable_simulatorShadow (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) :
    Measurable (fun pair : SimulatorSeed P Seed × List (VisibleEvent P.sharedInstance) =>
      simulatorShadow P fee hfee source pair.1 pair.2) :=
  (measurable_of_countable (SimulatorCache.shadow (I := P.sharedInstance))).comp
    (measurable_simulatorReplay (simulatorSeedDraw P fee hfee source)
      (measurable_simulatorSeedDraw P fee hfee source hm))

end PDROC
