module

public import PaperProofs.Retained.PRet_JointSuffixSuccess_105
public import PaperProofs.Retained.PRet_FreshHeadBill_108

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshActualSuccess109

open Common Common.Native PRetAmbientComparator073 PRetFreshContinuationPolicy096 PRetJointSuffixSuccess105
open PRetFreshActualRun106 PRetFreshActualEntry103 PRetFreshActualChoice107 PRetFreshHeadBill108

variable {I Ambient : Instance} {Seed : Type*} [MeasurableSpace Seed]

/-- The actual stitched policy preserves the ORIGINAL old-H success
predicate. A wrong head is inserted into the same ambient matching debt;
no available-only comparator or physical child success is substituted. -/
theorem jointSuccess_at_testStop (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed)
    (good bad : Policy (input.freshSuffix 1) (freshContract (I.freshSuffix 1)) .uncapped
      (zeroNormalAccounting (I.freshSuffix 1)) Seed)
    (embed : I.Stage → Ambient.Stage) (base : Finset Ambient.Stage)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hs : jointSuccess (input.freshSuffix 1) (fun stage => embed (I.freshStageLift 1 stage))
      (if test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head
        then base else insert (embed head) base)
      (if test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head
        then good else bad).rule (sample.1, referenceSuffixWorld input 1 sample.2)) :
    jointSuccess input embed base
      (twoContinuationPolicy input head test good.rule bad.rule good.measurable_rule bad.measurable_rule).rule sample := by
  classical
  let policy := twoContinuationPolicy input head test good.rule bad.rule good.measurable_rule bad.measurable_rule
  let before := (run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample (n + 1)).history ++ [.advanced head]
  let child := if test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head then good else bad
  let old := if test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head then base else insert (embed head) base
  obtain ⟨_, _, hw, hwrite, _, _, _, _, _⟩ := actual_entry_facts input head hhead test good bad sample n hstop
  have hchoice := choice_at_testStop input head hhead test good bad sample n hstop
  have hviews := run_view_at_testStop input head hhead test good bad sample n hstop
  change historyWritten before head = (historyReport before head).map Prod.fst ↔ _ at hchoice
  change ∀ k, ReferenceSuffixView I 1 before
    (run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample (n + 2 + k))
    (run (input.freshSuffix 1) (freshContract (I.freshSuffix 1)) .uncapped (zeroNormalAccounting (I.freshSuffix 1))
      (if historyWritten before head = (historyReport before head).map Prod.fst then good else bad).rule
      (sample.1, referenceSuffixWorld input 1 sample.2) k) at hviews
  simp only [hchoice] at hviews
  have hbase : base ⊆ old := by
    dsimp only [old]
    split_ifs
    · exact Finset.Subset.refl _
    · exact Finset.subset_insert _ _
  have hall (stage : I.Stage) (hlt : stage.val < 1) : historyWritten before stage ≠ none := by
    have heq : stage = head := Fin.ext (by omega)
    subst stage
    exact hw
  have hheadBit := written_at_testStop input head hhead test good bad sample n hstop
  have hold (stage : I.Stage) (bit : Bool) (hlt : stage.val < 1)
      (hbit : historyWritten before stage = some bit) (hne : bit ≠ input.truthAt sample.2 stage) : embed stage ∈ old := by
    have heq : stage = head := Fin.ext (by omega)
    subst stage
    have hb : bit = test.rule.decision sample.1 (worldTapes input sample.2 head) := Option.some.inj (hbit.symm.trans hheadBit)
    have hc : test.rule.decision sample.1 (worldTapes input sample.2 head) ≠ input.truthAt sample.2 head := fun heq => hne (hb.trans heq)
    dsimp only [old]
    rw [ite_eq_right hc]
    exact Finset.mem_insert_self _ _
  exact jointSuccess_of_views input 1 policy child sample before embed base old hbase hall hold hwrite (n + 2) hviews hs

end PaperProofs.Retained.PRetFreshActualSuccess109
