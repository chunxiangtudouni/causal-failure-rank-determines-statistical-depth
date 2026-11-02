module
public import PaperProofs.Paid.PDROC_LocalRecord_014
public import PaperProofs.Paid.PDROC_LocalRecord_010
public import PaperProofs.Paid.PDROC_DirectEntry_002

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native
open PaperProofs.Paid

namespace PDROC
universe u
section
variable {Seed : Type u} [MeasurableSpace Seed]

/-- The actual ORIGINAL current tape has the pure auxiliary marginal law. -/
theorem seededCurrentTape_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) :
    ((P.input fee hfee).seededWorldLaw ν).map
      (fun sample => worldTapes (P.input fee hfee) sample.2 stage) = auxiliaryTapeLaw P := by
  change ((P.input fee hfee).seededWorldLaw ν).map
    ((fun world => worldTapes (P.input fee hfee) world stage) ∘ Prod.snd) = _
  rw [← Measure.map_map (measurable_worldTape _ _) measurable_snd,
    StatisticalInput.seededWorldLaw_world, worldTape_map]
  change experimentTapeMixture P.binarySymmetric.experiment = auxiliaryTapeLaw P
  unfold experimentTapeMixture auxiliaryTapeLaw
  rw [P.binarySymmetric.priorMass_eq_half, P.binarySymmetric.priorMass_eq_half]
  exact add_comm _ _

/-- Direct (unrenumbered) original entry/tape product law. The complete old
private seed and public StartupOption are preserved, even off entry. -/
theorem sourceEntry_joint_directTape (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val mode accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) (start : ℕ) :
    ((P.input fee hfee).seededWorldLaw ν).map (fun sample =>
      (entrySeedStartupAt (P.input fee hfee) C.val mode accounting source.rule stage start sample,
        worldTapes (P.input fee hfee) sample.2 stage)) =
      (sourceEntrySeedLaw P fee hfee C mode accounting source ν stage start).prod (auxiliaryTapeLaw P) := by
  have hi := (entrySeedStartupAt_independent_next (P.input fee hfee) C.val mode accounting source ν stage start).comp
    measurable_id measurable_snd
  change ProbabilityTheory.IndepFun
    (entrySeedStartupAt (P.input fee hfee) C.val mode accounting source.rule stage start)
    (fun sample => worldTapes (P.input fee hfee) sample.2 stage) ((P.input fee hfee).seededWorldLaw ν) at hi
  have hm := measurable_entrySeedStartupAt (P.input fee hfee) C.val mode accounting source.rule source.measurable_rule stage start
  have ht : Measurable (fun sample : Seed × (P.input fee hfee).World =>
      worldTapes (P.input fee hfee) sample.2 stage) := (measurable_worldTape _ _).comp measurable_snd
  rw [hi.map_prod_eq_prod_map_map hm.aemeasurable ht.aemeasurable, seededCurrentTape_law]
  rfl

/-- A pure analysis wrapper: outside the original entry event it stops
blindly. At every actual source entry it is exactly the original rule. -/
def sourceForOptionalEntry (P : Parameters) (source : PolicyRule P.sharedInstance Seed) :
    PolicyRule P.sharedInstance (Seed × Option (Startup P.sharedInstance)) :=
  fun seed history => if seed.2.isSome = true then source seed.1 history else .stop

theorem measurable_sourceForOptionalEntry (P : Parameters) (source : PolicyRule P.sharedInstance Seed)
    (hm : MeasurableRule source) : MeasurableRule (sourceForOptionalEntry P source) := by
  have hsource : Measurable (fun pair : (Seed × Option (Startup P.sharedInstance)) × List (VisibleEvent P.sharedInstance) =>
      source pair.1.1 pair.2) := hm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hgate : MeasurableSet {pair : (Seed × Option (Startup P.sharedInstance)) × List (VisibleEvent P.sharedInstance) |
      pair.1.2.isSome = true} :=
    ((measurable_of_countable (fun startup : Option (Startup P.sharedInstance) => startup.isSome)).comp
      (measurable_snd.comp measurable_fst)) (measurableSet_singleton true)
  exact hsource.ite hgate measurable_const

def sourceEntryHistorySeed (P : Parameters) (seed : Seed × Option (Startup P.sharedInstance)) :
    (Seed × Option (Startup P.sharedInstance)) × List (VisibleEvent P.sharedInstance) :=
  (seed, (seed.2.map Startup.history).getD [])

theorem measurable_sourceEntryHistorySeed (P : Parameters) : Measurable (sourceEntryHistorySeed (Seed := Seed) P) :=
  measurable_id.prodMk ((measurable_of_countable (fun startup : Option (Startup P.sharedInstance) =>
    (startup.map Startup.history).getD [])).comp measurable_snd)

noncomputable def directOptionalEntryTest (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    P.binarySymmetric.experiment.AdmissibleRule (Seed × Option (Startup P.sharedInstance)) :=
  pullbackSeedTest P.binarySymmetric.experiment
    (simulatorLocalTest P fee hfee (sourceForOptionalEntry P source)
      (measurable_sourceForOptionalEntry P source hm) stage)
    (sourceEntryHistorySeed P) (measurable_sourceEntryHistorySeed P)

theorem directOptionalEntryTest_stop_some (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage)
    (seed : Seed) (startup : Startup P.sharedInstance) (tape : P.binarySymmetric.experiment.Tape) :
    (directOptionalEntryTest P fee hfee source hm stage).rule.stop (seed, some startup) tape =
      headExitStop (P.input fee hfee) stage (simulatorPrewriteRule P source) (seed, startup.history) tape := by
  simp only [directOptionalEntryTest, pullbackSeedTest, simulatorLocalTest, nativeHeadTest,
    sourceEntryHistorySeed, Option.map_some, Option.getD_some, headExitStop, simulatorPrewriteRule,
    sourceForOptionalEntry, Option.isSome_some, ↓reduceIte]

theorem directOptionalEntryTest_stop_none (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage)
    (seed : Seed) (tape : P.binarySymmetric.experiment.Tape) :
    (directOptionalEntryTest P fee hfee source hm stage).rule.stop (seed, none) tape = 0 := by
  change headExitStop (P.input fee hfee) stage (simulatorPrewriteRule P (sourceForOptionalEntry P source))
    ((seed, none), []) tape = 0
  apply le_antisymm
  · apply (headExitStop_le_iff (P.input fee hfee) stage _ _ _ 0).mpr
    refine ⟨0, le_rfl, ?_⟩
    simp only [simulatorPrewriteRule, sourceForOptionalEntry, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true]
  · exact zero_le

end
end PDROC

