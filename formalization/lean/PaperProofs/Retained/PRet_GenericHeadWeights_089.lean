module

public import PaperProofs.Common.NativeHeadTotalLower

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetGenericHeadWeights089

open Common Common.Native MeasureTheory
open scoped ENNReal

variable {I : Instance} {Seed : Type*}

noncomputable def decisionWeight (input : StatisticalInput I) (head : I.Stage)
    (source : PolicyRule I Seed) (good bad : ℝ) (sample : Seed × input.World) : ℝ≥0∞ :=
  if headExitDecision input head source sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head
    then ENNReal.ofReal good else ENNReal.ofReal bad

noncomputable def entryWeight (head : I.Stage) (startup : Startup I) (good bad : ℝ) : ℝ≥0∞ := by
  classical
  exact if HeadCorrectStartup head startup then ENNReal.ofReal good else ENNReal.ofReal bad

theorem decisionWeight_le (input : StatisticalInput I) (head : I.Stage) (source : PolicyRule I Seed)
    (good bad penalty : ℝ) (horder : good ≤ bad) (hbad : bad ≤ penalty) (sample : Seed × input.World) :
    decisionWeight input head source good bad sample ≤ ENNReal.ofReal penalty := by
  unfold decisionWeight
  split_ifs
  · exact ENNReal.ofReal_le_ofReal (horder.trans hbad)
  · exact ENNReal.ofReal_le_ofReal hbad

theorem decisionWeight_on_entry (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (source : PolicyRule I Seed) (hlegal : LegalRule input C .uncapped accounting source)
    (head : I.Stage) (hhead : head.val = 0) (sample : Seed × input.World) (n : ℕ)
    (hentry : FirstEntryAt input C .uncapped accounting source 1 n sample) (good bad : ℝ) :
    decisionWeight input head source good bad sample =
      entryWeight head (publicStartup (run input C .uncapped accounting source sample n)) good bad := by
  classical
  have hc := firstEntry_one_local_correct_iff input C hearly accounting source hlegal head hhead sample n hentry
  by_cases hp : HeadCorrectStartup head (publicStartup (run input C .uncapped accounting source sample n))
  · have hd := hc.mp hp
    simp only [decisionWeight, entryWeight, hp, hd, ↓reduceIte]
  · have hd : headExitDecision input head source sample.1 (worldTapes input sample.2 head) ≠ input.truthAt sample.2 head :=
      fun h => hp (hc.mpr h)
    simp only [decisionWeight, entryWeight, hp, hd, ↓reduceIte]

theorem measurable_decisionWeight [MeasurableSpace Seed] (input : StatisticalInput I) (head : I.Stage)
    (source : PolicyRule I Seed) (hm : MeasurableRule source) (good bad : ℝ) :
    Measurable (decisionWeight input head source good bad) := by
  have hlocal : Measurable (fun sample : Seed × input.World => (sample.1, worldTapes input sample.2 head)) :=
    measurable_fst.prodMk (((measurable_pi_apply head).comp measurable_snd).snd)
  have hd : Measurable (fun sample : Seed × input.World =>
      headExitDecision input head source sample.1 (worldTapes input sample.2 head)) :=
    (nativeHeadTest input head source hm).measurable_decision.comp hlocal
  have ht : Measurable (fun sample : Seed × input.World => input.truthAt sample.2 head) :=
    (input.measurable_truthAt head).comp measurable_snd
  exact Measurable.ite (measurableSet_eq_fun hd ht) measurable_const measurable_const

end PaperProofs.Retained.PRetGenericHeadWeights089
