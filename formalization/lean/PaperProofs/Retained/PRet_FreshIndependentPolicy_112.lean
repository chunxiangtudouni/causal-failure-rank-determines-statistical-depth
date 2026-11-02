module

public import PaperProofs.Retained.PRet_FreshActualCharge_110
public import PaperProofs.Retained.PRet_JointChargePullback_111

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshIndependentPolicy112

open Common Common.Native PRetAmbientComparator073 PRetJointCharges075 PRetFreshContinuationPolicy096
open PRetFreshActualCharge110 PRetFreshSeedPullback094 PRetJointChargePullback111 BellmanPrivateSeeds

variable {I Ambient : Instance} {Local Good Bad : Type*}
variable [MeasurableSpace Local] [MeasurableSpace Good] [MeasurableSpace Bad]

/-- Three genuinely independent private random sources, implemented by
existing product-seed pullbacks and the actual retained-aware full policy. -/
noncomputable def independentPolicy (input : StatisticalInput I) (head : I.Stage)
    (test : (input.experiment head).AdmissibleRule Local)
    (good : Policy (input.freshSuffix 1) (freshContract (I.freshSuffix 1)) .uncapped (zeroNormalAccounting (I.freshSuffix 1)) Good)
    (bad : Policy (input.freshSuffix 1) (freshContract (I.freshSuffix 1)) .uncapped (zeroNormalAccounting (I.freshSuffix 1)) Bad) :
    Policy input (freshContract I) .uncapped (zeroNormalAccounting I) (CombinedSeed Local Good Bad) :=
  let test' := pullbackTest (Large := CombinedSeed Local Good Bad) (input.experiment head) test localSeed measurable_localSeed
  let good' := pullbackFull (Large := CombinedSeed Local Good Bad) (input.freshSuffix 1) good goodSeed measurable_goodSeed
  let bad' := pullbackFull (Large := CombinedSeed Local Good Bad) (input.freshSuffix 1) bad badSeed measurable_badSeed
  twoContinuationPolicy input head test' good'.rule bad'.rule good'.measurable_rule bad'.measurable_rule

theorem charge_at_testStop (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Local)
    (good : Policy (input.freshSuffix 1) (freshContract (I.freshSuffix 1)) .uncapped (zeroNormalAccounting (I.freshSuffix 1)) Good)
    (bad : Policy (input.freshSuffix 1) (freshContract (I.freshSuffix 1)) .uncapped (zeroNormalAccounting (I.freshSuffix 1)) Bad)
    (embed : I.Stage → Ambient.Stage) (old : Finset Ambient.Stage)
    (sample : CombinedSeed Local Good Bad × input.World) (n : ℕ)
    (hstop : (pullbackTest (Large := CombinedSeed Local Good Bad) (input.experiment head) test localSeed measurable_localSeed).rule.stop sample.1
      (worldTapes input sample.2 head) = n) (penalty : ENNReal) :
    jointCharge input embed old (independentPolicy input head test good bad).rule penalty sample ≤
      (input.experiment head).observationCharge
        ((pullbackTest (Large := CombinedSeed Local Good Bad) (input.experiment head) test localSeed measurable_localSeed).rule.stop sample.1 (worldTapes input sample.2 head)) +
      if (pullbackTest (Large := CombinedSeed Local Good Bad) (input.experiment head) test localSeed measurable_localSeed).rule.decision sample.1
          (worldTapes input sample.2 head) = input.truthAt sample.2 head then
        jointCharge (input.freshSuffix 1) (fun stage => embed (I.freshStageLift 1 stage)) old good.rule penalty
          (goodSeed sample.1, referenceSuffixWorld input 1 sample.2)
      else jointCharge (input.freshSuffix 1) (fun stage => embed (I.freshStageLift 1 stage)) (insert (embed head) old) bad.rule penalty
          (badSeed sample.1, referenceSuffixWorld input 1 sample.2) := by
  classical
  let test' := pullbackTest (Large := CombinedSeed Local Good Bad) (input.experiment head) test localSeed measurable_localSeed
  let good' := pullbackFull (Large := CombinedSeed Local Good Bad) (input.freshSuffix 1) good goodSeed measurable_goodSeed
  let bad' := pullbackFull (Large := CombinedSeed Local Good Bad) (input.freshSuffix 1) bad badSeed measurable_badSeed
  have h := PRetFreshActualCharge110.charge_at_testStop input head hhead test' good' bad' embed old sample n hstop penalty
  change jointCharge input embed old (independentPolicy input head test good bad).rule penalty sample ≤ _ at h
  change jointCharge input embed old (independentPolicy input head test good bad).rule penalty sample ≤
    (input.experiment head).observationCharge (test'.rule.stop sample.1 (worldTapes input sample.2 head)) +
      if test'.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head then
        jointCharge (input.freshSuffix 1) (fun stage => embed (I.freshStageLift 1 stage)) old good.rule penalty
          (goodSeed sample.1, referenceSuffixWorld input 1 sample.2)
      else jointCharge (input.freshSuffix 1) (fun stage => embed (I.freshStageLift 1 stage)) (insert (embed head) old) bad.rule penalty
          (badSeed sample.1, referenceSuffixWorld input 1 sample.2)
  calc
    _ ≤ _ := h
    _ = _ := by
      by_cases hc : test'.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head
      · simp only [hc, ite_true, good', jointCharge_pullbackFull]
      · simp only [hc, ite_false, bad', jointCharge_pullbackFull]

end PaperProofs.Retained.PRetFreshIndependentPolicy112
