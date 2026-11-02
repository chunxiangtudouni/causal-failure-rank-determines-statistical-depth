module

public import PaperProofs.Retained.PRet_AmbientComparator_073
public import PaperProofs.Retained.PRet_OutputCompletion_049
public import PaperProofs.Common.NativeBellmanSuccessLift

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetJointSuffixSuccess104

open Common Common.Native PRetAmbientComparator073 PRetOutputCompletion049

variable {I Ambient : Instance}

/-- The fresh comparator needs joint matching, not physical repairs.
A completed child and its joint old-H matching yield genuine parent
completion with the old head mismatches kept in that same matching. -/
theorem completed_prefixes_joint {Seed : Type*} (input : StatisticalInput I) (first : ℕ)
    (parentRule : PolicyRule I Seed) (childRule : PolicyRule (I.freshSuffix first) Seed)
    (sample : Seed × input.World) (before : List (VisibleEvent I))
    (embed : I.Stage → Ambient.Stage) (base old : Finset Ambient.Stage)
    (hbase : base ⊆ old)
    (hallBefore : ∀ stage : I.Stage, stage.val < first → historyWritten before stage ≠ none)
    (hold : ∀ (stage : I.Stage) (bit : Bool), stage.val < first →
      historyWritten before stage = some bit → bit ≠ input.truthAt sample.2 stage → embed stage ∈ old)
    (hclean : ∀ stage, historyWrite before (I.freshStageLift first stage) = none)
    {m n : ℕ} {parent : State I} {child : State (I.freshSuffix first)}
    (hp : Prefix input (freshContract I) .uncapped (zeroNormalAccounting I) parentRule sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) m parent)
    (hc : Prefix (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) childRule sample.1
      ((input.freshSuffix first).truthAt (referenceSuffixWorld input first sample.2))
      (worldTapes (input.freshSuffix first) (referenceSuffixWorld input first sample.2)) n child)
    (view : ReferenceSuffixView I first before parent child)
    (hh : child.halted = true) (hf : child.ledger.finished = true) (ha : child.ledger.abandoned = false)
    (hm : Matchable Ambient (old ∪ (ordinaryMismatches child.ledger).image (fun stage => embed (I.freshStageLift first stage)))) :
    parent.halted = true ∧ parent.ledger.finished = true ∧ parent.ledger.abandoned = false ∧
      Matchable Ambient (base ∪ (ordinaryMismatches parent.ledger).image embed) := by
  classical
  have hpt := prefix_truth input (freshContract I) .uncapped (zeroNormalAccounting I) parentRule sample.1 _ _ hp
  have hct := prefix_truth (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
    (zeroNormalAccounting (I.freshSuffix first)) childRule sample.1 _ _ hc
  have hwrite (stage : (I.freshSuffix first).Stage) :
      parent.ledger.written (I.freshStageLift first stage) = child.ledger.written stage := by
    rw [← prefix_historyWritten input (freshContract I) .uncapped (zeroNormalAccounting I) parentRule sample.1 _ _ hp,
      view.history, historyWritten_referenceSuffixJoin_future I first before child.history stage (hclean stage)]
    exact prefix_historyWritten (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) childRule sample.1 _ _ hc stage
  have htruth (stage : (I.freshSuffix first).Stage) :
      parent.ledger.truth (I.freshStageLift first stage) = child.ledger.truth stage := by
    rw [hpt, hct]
    rfl
  have hchildAll := prefix_finished_allWritten (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
    (zeroNormalAccounting (I.freshSuffix first)) childRule sample.1 _ _ hc hf
  have hparentAll : allWritten parent.ledger := by
    intro stage
    by_cases hs : stage.val < first
    · rw [← prefix_historyWritten input (freshContract I) .uncapped (zeroNormalAccounting I) parentRule sample.1 _ _ hp,
        view.history, historyWritten_referenceSuffixJoin_old I first before child.history stage hs]
      exact hallBefore stage hs
    · have hge : first ≤ stage.val := Nat.le_of_not_gt hs
      let target := suffixStageOf first stage hge
      have heq : I.freshStageLift first target = stage := freshStageLift_suffixStageOf first stage hge
      rw [← heq, hwrite target]
      exact hchildAll target
  have hhParent := view.halted.trans hh
  have hlast := prefix_halted_not_abandoned_last_stopped (input.freshSuffix first)
    (freshContract (I.freshSuffix first)) .uncapped (zeroNormalAccounting (I.freshSuffix first)) childRule sample.1 _ _ hc hh ha
  have hpLast : parent.history.getLast? = some .stopped := by
    rw [view.history]
    exact last_stopped_referenceSuffixJoin I first before child.history hlast
  have haParent := prefix_last_stopped_not_abandoned input (freshContract I) rfl .uncapped
    (zeroNormalAccounting I) parentRule sample.1 _ _ hp hpLast
  refine ⟨hhParent, prefix_halted_allWritten_finished input (freshContract I) .uncapped (zeroNormalAccounting I)
    parentRule sample.1 _ _ hp hhParent hparentAll, haParent, hm.subset ?_⟩
  apply Finset.union_subset
  · exact hbase.trans Finset.subset_union_left
  · intro stage hstage
    obtain ⟨source, hsource, rfl⟩ := Finset.mem_image.mp hstage
    have hwrong := (mem_ordinaryMismatches parent.ledger source).mp hsource
    by_cases hs : source.val < first
    · apply Finset.mem_union_left
      apply hold source (!parent.ledger.truth source) hs
      · rw [← historyWritten_referenceSuffixJoin_old I first before child.history source hs, ← view.history,
          prefix_historyWritten input (freshContract I) .uncapped (zeroNormalAccounting I) parentRule sample.1 _ _ hp]
        exact hwrong
      · rw [hpt]
        cases input.truthAt sample.2 source <;> decide
    · have hge : first ≤ source.val := Nat.le_of_not_gt hs
      let target := suffixStageOf first source hge
      have heq : I.freshStageLift first target = source := freshStageLift_suffixStageOf first source hge
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨target, ?_, congrArg embed heq⟩
      apply (mem_ordinaryMismatches child.ledger target).mpr
      rw [← hwrite target, ← htruth target, heq]
      exact hwrong

end PaperProofs.Retained.PRetJointSuffixSuccess104
