module

public import PaperProofs.Retained.PRet_FreshActualSuccess_109
public import PaperProofs.Retained.PRet_JointCharges_075

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshActualCharge110

open Common Common.Native PRetAmbientComparator073 PRetJointCharges075 PRetFreshContinuationPolicy096
open PRetFreshActualRun106 PRetFreshActualEntry103 PRetFreshActualChoice107 PRetFreshHeadBill108 PRetFreshActualSuccess109
open scoped ENNReal

variable {I Ambient : Instance} {Seed : Type*} [MeasurableSpace Seed]

/-- Every actual finite-test path, including failed/nonreturning child
paths and infinite observation bills, pays at most the original local test
plus its genuinely chosen full child charge and SINGLE old-H failure bill. -/
theorem charge_at_testStop (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed)
    (good bad : Policy (input.freshSuffix 1) (freshContract (I.freshSuffix 1)) .uncapped
      (zeroNormalAccounting (I.freshSuffix 1)) Seed)
    (embed : I.Stage → Ambient.Stage) (base : Finset Ambient.Stage)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n) (penalty : ℝ≥0∞) :
    jointCharge input embed base
      (twoContinuationPolicy input head test good.rule bad.rule good.measurable_rule bad.measurable_rule).rule penalty sample ≤
      (input.experiment head).observationCharge (test.rule.stop sample.1 (worldTapes input sample.2 head)) +
        jointCharge (input.freshSuffix 1) (fun stage => embed (I.freshStageLift 1 stage))
          (if test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head
            then base else insert (embed head) base)
          (if test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head
            then good else bad).rule penalty (sample.1, referenceSuffixWorld input 1 sample.2) := by
  classical
  let policy := twoContinuationPolicy input head test good.rule bad.rule good.measurable_rule bad.measurable_rule
  let before := (run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample (n + 1)).history ++ [.advanced head]
  let child := if test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head then good else bad
  let old := if test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head then base else insert (embed head) base
  obtain ⟨_, _, _, _, _, _, _, hobs, _⟩ := actual_entry_facts input head hhead test good bad sample n hstop
  have hchoice := choice_at_testStop input head hhead test good bad sample n hstop
  have hviews := run_view_at_testStop input head hhead test good bad sample n hstop
  change historyWritten before head = (historyReport before head).map Prod.fst ↔ _ at hchoice
  change ∀ k, ReferenceSuffixView I 1 before
    (run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample (n + 2 + k))
    (run (input.freshSuffix 1) (freshContract (I.freshSuffix 1)) .uncapped (zeroNormalAccounting (I.freshSuffix 1))
      (if historyWritten before head = (historyReport before head).map Prod.fst then good else bad).rule
      (sample.1, referenceSuffixWorld input 1 sample.2) k) at hviews
  simp only [hchoice] at hviews
  have hfuture := suffixRun_futureObservationBill_of_views input 1 (freshContract I) (zeroNormalAccounting I)
    policy.rule policy.legal (freshContract (I.freshSuffix 1)) (zeroNormalAccounting (I.freshSuffix 1))
    child.rule child.legal sample before (n + 2) hobs hviews
  have hwhole := runObservationBill_eq_prefix_add_future input (freshContract I) .uncapped (zeroNormalAccounting I)
    policy.rule policy.legal sample (n + 2)
  have hprefix := prefix_bill_at_testStop input head hhead test good bad sample n hstop
  rw [hfuture, hprefix] at hwhole
  have hfailure : (if jointSuccess input embed base policy.rule sample then (0 : ENNReal) else penalty) ≤
      (if jointSuccess (input.freshSuffix 1) (fun stage => embed (I.freshStageLift 1 stage)) old child.rule
        (sample.1, referenceSuffixWorld input 1 sample.2) then 0 else penalty) := by
    by_cases hs : jointSuccess (input.freshSuffix 1) (fun stage => embed (I.freshStageLift 1 stage)) old child.rule
        (sample.1, referenceSuffixWorld input 1 sample.2)
    · have hp : jointSuccess input embed base policy.rule sample :=
        jointSuccess_at_testStop input head hhead test good bad embed base sample n hstop hs
      simp only [hs, hp, ite_true, le_refl]
    · rw [ite_eq_right hs]
      split_ifs
      · exact bot_le
      · exact le_rfl
  change jointCharge input embed base policy.rule penalty sample ≤
    (input.experiment head).observationCharge (test.rule.stop sample.1 (worldTapes input sample.2 head)) +
      jointCharge (input.freshSuffix 1) (fun stage => embed (I.freshStageLift 1 stage)) old child.rule penalty
        (sample.1, referenceSuffixWorld input 1 sample.2)
  unfold jointCharge
  rw [hwhole, add_assoc]
  exact add_le_add (le_refl _) (add_le_add (le_refl _) hfailure)

end PaperProofs.Retained.PRetFreshActualCharge110
