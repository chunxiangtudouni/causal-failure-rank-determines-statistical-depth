module

public import PaperProofs.Retained.PRet_NestedEntryRow_081
public import PaperProofs.Retained.PRet_HeadReportedSet_083
public import PaperProofs.Retained.PRet_FreshBranchValues_084

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshHeadEntry087

open Common Common.Native MeasureTheory PRetNestedEntryRow081 PRetHeadReportedSet083 PRetFreshBranchValues084
open PRetJointExtraction076
open scoped ENNReal

open scoped Classical

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

/-- Every actual post-head entry atom pays its TRUE good/bad retained
continuation value. Wrong-head insertion keeps old H; even immediate
unmatchability uses the same original infimum and its proved boundary. -/
theorem head_entry_lower (input : StatisticalInput I) (original : I.Stage) (old : Finset I.Stage)
    (source : Policy (input.freshSuffix original.val) (freshContract (I.freshSuffix original.val)) .uncapped
      (zeroNormalAccounting (I.freshSuffix original.val)) Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (next : (I.freshSuffix original.val).Stage) (hnext : next.val = 1)
    (n : ℕ) (startup : Startup (I.freshSuffix original.val)) (penalty : ℝ) (hp : 0 ≤ penalty) :
    ENNReal.ofReal (if HeadCorrectStartup (I.freshHead original) startup then goodPenaltyReal input original old penalty
      else badPenaltyReal input original old penalty) *
      (input.freshSuffix original.val).seededWorldLaw ν {sample |
        entryStartupAt (input.freshSuffix original.val) (freshContract (I.freshSuffix original.val)) .uncapped
          (zeroNormalAccounting (I.freshSuffix original.val)) source.rule next n sample = some startup} ≤
      ∫⁻ sample in {sample |
        entryStartupAt (input.freshSuffix original.val) (freshContract (I.freshSuffix original.val)) .uncapped
          (zeroNormalAccounting (I.freshSuffix original.val)) source.rule next n sample = some startup},
        futureJointCharge (input.freshSuffix original.val) (I.freshStageLift original.val) old source.rule 1 (ENNReal.ofReal penalty) sample
          ∂(input.freshSuffix original.val).seededWorldLaw ν := by
  classical
  let J := I.freshSuffix original.val
  let localInput := input.freshSuffix original.val
  let head := I.freshHead original
  let E := {sample : Seed × localInput.World |
    entryStartupAt localInput (freshContract J) .uncapped (zeroNormalAccounting J) source.rule next n sample = some startup}
  let newOld := if HeadCorrectStartup head startup then old else insert original old
  by_cases he : E.Nonempty
  · obtain ⟨sample, hs⟩ := he
    obtain ⟨hentry, hstartup⟩ := (entryStartupAt_some_iff localInput (freshContract J) .uncapped (zeroNormalAccounting J)
      source.rule next n sample startup).mp hs
    have hentryOne : FirstEntryAt localInput (freshContract J) .uncapped (zeroNormalAccounting J) source.rule 1 n sample := hnext ▸ hentry
    have hhead : head.val = 0 := rfl
    have hw := firstEntry_one_head_written localInput (freshContract J) .uncapped (zeroNormalAccounting J)
      source.rule source.legal head hhead sample n hentryOne
    obtain ⟨_, _, hpref⟩ := run_has_prefix localInput (freshContract J) .uncapped (zeroNormalAccounting J) source.rule source.legal sample n
    have herr := prefix_reportedErrors_one localInput (freshContract J) rfl .uncapped (zeroNormalAccounting J)
      source.rule sample.1 _ _ hpref head hhead hw
    change reportedErrors J (publicStartup (run localInput (freshContract J) .uncapped (zeroNormalAccounting J)
      source.rule sample n)).history 1 = _ at herr
    rw [hstartup] at herr
    have hold : newOld ⊆ old ∪ (reportedErrors J startup.history next.val).image (I.freshStageLift original.val) := by
      rw [hnext, herr]
      unfold newOld
      split_ifs
      · simp only [Finset.image_empty, Finset.union_empty, Finset.Subset.refl]
      · rw [Finset.image_singleton, Instance.freshStageLift_freshHead]
        exact Finset.insert_subset_iff.mpr ⟨Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self original)), Finset.subset_union_left⟩
    have hb := nested_entry_row_lower input original.val old newOld source ν next n startup hold Set.univ MeasurableSet.univ
      (ENNReal.ofReal penalty)
    simp only [Set.mem_univ, true_and] at hb
    have hvalue : freshPenalty input (original.val + next.val) newOld (ENNReal.ofReal penalty) =
        ENNReal.ofReal (if HeadCorrectStartup head startup then goodPenaltyReal input original old penalty
          else badPenaltyReal input original old penalty) := by
      rw [hnext]
      unfold newOld
      split_ifs
      · exact (ofReal_goodPenaltyReal input original old penalty).symm
      · exact (ofReal_badPenaltyReal input original old penalty hp).symm
    rw [hvalue, hnext, mul_comm] at hb
    exact hb
  · have hzero : E = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    change _ * (localInput.seededWorldLaw ν) E ≤ _
    rw [hzero, measure_empty, mul_zero]
    exact bot_le

end PaperProofs.Retained.PRetFreshHeadEntry087

