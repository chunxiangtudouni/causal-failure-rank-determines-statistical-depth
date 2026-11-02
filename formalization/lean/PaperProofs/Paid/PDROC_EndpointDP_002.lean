module

public import PaperProofs.Paid.PDROC_EndpointDP_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

open scoped BigOperators
open PaperProofs.Paid
open PaperProofs.Paid.Parameters

namespace PDROC

/-- Nonnegativity is proved in the original rational DP, before ofReal can
truncate anything. It is not inferred from a probability identity. -/
theorem endpointWalkDistribution_nonneg (P : Parameters) (level : ℕ) (truth : Bool) (steps : ℕ)
    (state : WalkCell level) : 0 ≤ P.walkDistribution level truth steps state := by
  induction steps generalizing state with
  | zero => rw [endpointWalkDistribution_zero]; split_ifs <;> norm_num
  | succ steps ih =>
    let channel : Fin 2 → ℚ := fun letter => P.experiment.channel truth letter
    rw [endpointWalkDistribution_succ]
    change 0 ≤ ∑ previous : WalkCell level, ∑ letter : Fin 2,
      if walkMove level previous letter = state then P.walkDistribution level truth steps previous * channel letter else 0
    apply Finset.sum_nonneg
    intro previous _hp
    apply Finset.sum_nonneg
    intro letter _hl
    split_ifs
    · exact mul_nonneg (ih previous) (P.experiment.channel_pos truth letter).le
    · exact le_rfl

/-- The actual finite array is a normalized rational conditional law for
either truth, including repeated absorbed-boundary updates. -/
theorem endpointWalkDistribution_sum (P : Parameters) (level : ℕ) (truth : Bool) (steps : ℕ) :
    (∑ state : WalkCell level, P.walkDistribution level truth steps state) = 1 := by
  induction steps with
  | zero =>
    let centre : WalkCell level := ⟨level, by omega⟩
    have hif (state : WalkCell level) : (if state.val = level then (1 : ℚ) else 0) =
        (if state = centre then 1 else 0) := by
      have he : state = centre ↔ state.val = level := Fin.ext_iff
      simp only [← he]
    simp_rw [endpointWalkDistribution_zero, hif]
    simp
  | succ steps ih =>
    let channel : Fin 2 → ℚ := fun letter => P.experiment.channel truth letter
    let weight := fun (state : WalkCell level) (letter : Fin 2) =>
      P.walkDistribution level truth steps state * channel letter
    simp_rw [endpointWalkDistribution_succ]
    change (∑ target : WalkCell level, ∑ state : WalkCell level, ∑ letter : Fin 2,
      if walkMove level state letter = target then weight state letter else 0) = 1
    calc
      (∑ target : WalkCell level, ∑ state : WalkCell level, ∑ letter : Fin 2,
          if walkMove level state letter = target then weight state letter else 0) =
        ∑ state : WalkCell level, ∑ letter : Fin 2, ∑ target : WalkCell level,
          if walkMove level state letter = target then weight state letter else 0 := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro state _hs
            rw [Finset.sum_comm]
      _ = ∑ state : WalkCell level, ∑ letter : Fin 2, weight state letter := by
        apply Finset.sum_congr rfl
        intro state _hs
        apply Finset.sum_congr rfl
        intro letter _hl
        simp
      _ = ∑ state : WalkCell level, P.walkDistribution level truth steps state := by
        apply Finset.sum_congr rfl
        intro state _hs
        change (∑ letter : Fin 2, P.walkDistribution level truth steps state * channel letter) = _
        have hchannel : (∑ letter : Fin 2, channel letter) = 1 := P.experiment.channel_sum truth
        rw [← Finset.mul_sum, hchannel, mul_one]
      _ = 1 := ih

/-- One original D23 conclusion is independent of the analytic tail chain:
the independently computed rational cappedError is nonnegative. -/
theorem endpointCappedError_nonneg (P : Parameters) (m : ℕ) : 0 ≤ P.cappedError m := by
  unfold PaperProofs.Paid.Parameters.cappedError
  apply Finset.sum_nonneg
  intro state _hs
  apply mul_nonneg (endpointWalkDistribution_nonneg P (m + 1) true P.certificate.Q state)
  split_ifs <;> norm_num

end PDROC
