module

public import PaperProofs.Paid.PDLower_RankCoefficient_002
public import PaperProofs.Paid.BSCAdapter

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Structure PaperProofs.Statistics PaperProofs.Paid

namespace PDLower

theorem paid_weightedSchedule_eq_replicate (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hf : 0 ≤ fee) :
    (P.input fee hf).weightedSchedule =
      List.replicate P.certificate.stages ((Finset.univ : Finset P.sharedInstance.Tool), P.a) := by
  unfold StatisticalInput.weightedSchedule
  have heq : (fun stage : P.sharedInstance.Stage =>
      (P.sharedInstance.eligible stage, ((P.input fee hf).experiment stage).coefficient)) =
      (fun _ : P.sharedInstance.Stage => ((Finset.univ : Finset P.sharedInstance.Tool), P.a)) := by
    funext stage
    apply Prod.ext
    · exact P.eligible_eq_univ stage
    · change P.experiment.coefficient = P.a
      rw [P.experiment_eq_binarySymmetric, P.binarySymmetric.coefficient_eq_a]
      exact P.priceCoefficient_eq.symm
  rw [heq, List.ofFn_const]
  have hlength : P.sharedInstance.compatibility.length = P.certificate.stages := P.stageCount_eq
  rw [hlength]

theorem paid_shared_coefficient (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hf : 0 ≤ fee) :
    (P.input fee hf).orderedCoefficient P.sharedInstance.tools =
      P.a * (P.certificate.stages - P.tools : ℕ) := by
  have hfinite : errorRank P.sharedInstance.compatibility P.sharedInstance.tools ≠ ⊤ := by
    rw [paid_shared_rank]
    exact ENat.natCast_ne_top _
  rw [(P.input fee hf).orderedCoefficient_head_formula P.sharedInstance.tools hfinite,
    paid_weightedSchedule_eq_replicate, paid_shared_rank]
  have hcard : P.sharedInstance.tools.card = P.tools := by
    change (Finset.univ : Finset (Fin P.tools)).card = _
    rw [Finset.card_univ, Fintype.card_fin]
  simpa only [hcard] using sharedPool_criticalHeadSum_replicate P.certificate.stages P.sharedInstance.tools P.a

theorem sharedPoolRankCoefficient (P : PaperProofs.Paid.Parameters) : P.SharedPoolRankCoefficient :=
  ⟨PaperProofs.Paid.Parameters.sharedPoolSubproblemRank, paid_shared_rank P,
    paid_shared_bad_child P, paid_shared_coefficient P⟩

end PDLower
