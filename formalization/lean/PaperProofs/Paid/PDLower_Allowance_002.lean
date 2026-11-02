module

public import PaperProofs.Paid.PDLower_Allowance_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDLower

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

theorem markedError_pathwise_allowance (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (policy : Policy (P.input fee hf) C.val mode accounting Seed)
    (sample : Seed × (P.input fee hf).World) :
    (∑ stage : P.sharedInstance.Stage, (P.markedErrorEvent fee hf C mode accounting policy.rule stage).indicator
      (fun _ => (1 : ℝ≥0∞)) sample) ≤
      runRepairCount (P.input fee hf) C.val mode accounting policy.rule sample +
        {sample | ¬ runSuccess (P.input fee hf) C.val mode accounting policy.rule sample}.indicator
          (fun _ => (1 : ℝ≥0∞)) sample := by
  classical
  let errors : Finset P.sharedInstance.Stage := Finset.univ.filter
    (fun stage => sample ∈ P.markedErrorEvent fee hf C mode accounting policy.rule stage)
  let repairs := eventualExecutedStages (P.input fee hf) C.val mode accounting policy.rule sample
  have herror (stage : P.sharedInstance.Stage) (hm : stage ∈ errors) :
      sample ∈ P.markedErrorEvent fee hf C mode accounting policy.rule stage := (Finset.mem_filter.mp hm).2
  have hmissed : (errors \ repairs).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    obtain ⟨hie, hir⟩ := Finset.mem_sdiff.mp hi
    obtain ⟨hje, hjr⟩ := Finset.mem_sdiff.mp hj
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hij | hji
    · obtain ⟨n, hcorrect | ⟨e, he, hes⟩⟩ := survivingEntry_earlier_physically_resolved P fee hf C mode accounting
        policy.rule policy.legal sample j i (herror j hje).1 hij
      · exact markedError_not_correct_write P fee hf C mode accounting policy.rule policy.legal sample i (herror i hie) n hcorrect
      · apply hir
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨n, e, he, hes⟩⟩
    · obtain ⟨n, hcorrect | ⟨e, he, hes⟩⟩ := survivingEntry_earlier_physically_resolved P fee hf C mode accounting
        policy.rule policy.legal sample i j (herror i hie).1 hji
      · exact markedError_not_correct_write P fee hf C mode accounting policy.rule policy.legal sample j (herror j hje) n hcorrect
      · apply hjr
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨n, e, he, hes⟩⟩
  have hcount : errors.card ≤ repairs.card + 1 := by
    have hi := Finset.card_le_card (Finset.inter_subset_right (s₁ := errors) (s₂ := repairs))
    have hd := Finset.card_sdiff_add_card_inter errors repairs
    omega
  have hsum : (∑ stage : P.sharedInstance.Stage, (P.markedErrorEvent fee hf C mode accounting policy.rule stage).indicator
      (fun _ => (1 : ℝ≥0∞)) sample) = (errors.card : ℝ≥0∞) := by
    simp only [Set.indicator_apply]
    simp [errors, Finset.sum_boole]
  rw [hsum]
  have hr := eventualExecutedStages_card_le_runRepairCount (P.input fee hf) C.val mode accounting policy.rule sample
  change (repairs.card : ℝ≥0∞) ≤ _ at hr
  by_cases hs : runSuccess (P.input fee hf) C.val mode accounting policy.rule sample
  · have hsub : errors ⊆ repairs := by
      intro stage hm
      obtain ⟨n, _, hsucc⟩ := hs
      rcases hsucc.2.2.2 stage with hcorrect | ⟨e, he, hes⟩
      · have hc : (run (P.input fee hf) C.val mode accounting policy.rule sample n).ledger.written stage = some (sample.2 stage).1 := by
          simpa only [run_truth (P.input fee hf) C.val mode accounting policy.rule policy.legal, StatisticalInput.truthAt] using hcorrect
        exact (markedError_not_correct_write P fee hf C mode accounting policy.rule policy.legal sample stage (herror stage hm) n hc).elim
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨n, e, he, hes⟩⟩
    have he : (errors.card : ℝ≥0∞) ≤ repairs.card := by exact_mod_cast Finset.card_le_card hsub
    simpa only [Set.indicator_apply, Set.mem_ofPred_eq, hs, not_true_eq_false, ↓reduceIte, add_zero] using he.trans hr
  · have he : (errors.card : ℝ≥0∞) ≤ (repairs.card : ℝ≥0∞) + 1 := by exact_mod_cast hcount
    simpa only [Set.indicator_apply, Set.mem_ofPred_eq, hs, not_false_eq_true, ↓reduceIte] using
      he.trans (add_le_add hr le_rfl)

end PDLower
