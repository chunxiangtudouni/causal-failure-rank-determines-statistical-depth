module

public import PaperProofs.Paid.BridgeClaims

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Structure PaperProofs.Statistics PaperProofs.Paid

namespace PDLower

theorem sharedPool_bad_replicate {Tool : Type*} [Fintype Tool] [DecidableEq Tool]
    (n : ℕ) (remaining : Finset Tool) :
    badChildRank (Finset.univ : Finset Tool) (List.replicate n Finset.univ) remaining =
      if remaining.card = 0 then 0
      else if n ≤ remaining.card - 1 then ⊤ else (remaining.card : ℕ∞) := by
  by_cases hempty : remaining = ∅
  · subst remaining
    simp [badChildRank]
  · have hne : remaining.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    have hcard : 0 < remaining.card := Finset.card_pos.mpr hne
    have hcardone : remaining.card - 1 + 1 = remaining.card := by omega
    rw [ite_eq_right hcard.ne']
    have hchild (tool : Tool) (htool : tool ∈ remaining) :
        errorRank (List.replicate n (Finset.univ : Finset Tool)) (remaining.erase tool) =
          if n ≤ remaining.card - 1 then ⊤ else (remaining.card : ℕ∞) := by
      rw [PaperProofs.Paid.Parameters.sharedPool_rank_replicate n (remaining.erase tool),
        Finset.card_erase_of_mem htool, hcardone]
    apply le_antisymm
    · apply Finset.sup_le
      intro tool htool
      exact (hchild tool (Finset.mem_inter.mp htool).2).le
    · obtain ⟨tool, htool⟩ := hne
      have h := childRank_le_badChildRank (Finset.univ : Finset Tool)
        (List.replicate n Finset.univ) remaining (Finset.mem_inter.mpr ⟨Finset.mem_univ tool, htool⟩)
      rwa [hchild tool htool] at h

theorem paid_shared_rank (P : Parameters) :
    errorRank P.sharedInstance.compatibility P.sharedInstance.tools = ((P.tools + 1 : ℕ) : ℕ∞) := by
  change errorRank (List.replicate P.certificate.stages (Finset.univ : Finset (Fin P.tools))) Finset.univ = _
  rw [PaperProofs.Paid.Parameters.sharedPool_rank_replicate, Finset.card_univ, Fintype.card_fin,
    ite_eq_right (Nat.not_le_of_gt P.tools_lt_stages)]

theorem paid_shared_bad_child (P : Parameters) (stage : P.sharedInstance.Stage) :
    badChildRank (P.sharedInstance.eligible stage)
      (P.sharedInstance.compatibility.drop (stage.val + 1)) P.sharedInstance.tools =
      if P.tools = 0 then 0
      else if stage.val < P.certificate.stages - P.tools then (P.tools : ℕ∞) else ⊤ := by
  rw [P.eligible_eq_univ]
  change badChildRank (Finset.univ : Finset (Fin P.tools))
    ((List.replicate P.certificate.stages Finset.univ).drop (stage.val + 1)) Finset.univ = _
  rw [List.drop_replicate, sharedPool_bad_replicate, Finset.card_univ, Fintype.card_fin]
  by_cases hk : P.tools = 0
  · simp only [hk, ↓reduceIte]
  · simp only [hk, ↓reduceIte]
    have hi : stage.val < P.certificate.stages := by
      simpa only [Parameters.sharedInstance, List.length_replicate] using stage.isLt
    by_cases hs : stage.val < P.certificate.stages - P.tools
    · have hn : ¬ P.certificate.stages - (stage.val + 1) ≤ P.tools - 1 := by omega
      simp only [hs, hn, ↓reduceIte]
    · have hn : P.certificate.stages - (stage.val + 1) ≤ P.tools - 1 := by omega
      simp only [hs, hn, ↓reduceIte]

end PDLower
