module

public import Paid.PDLower_CalibrationCompute_RowBridge_044
public import PaperProofs.Paid.PDROC_DataBits_CalibrationFormal_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDLower.CalibrationCompute

def RowDenominator (row : Array ℚ) (D : ℕ) : Prop :=
  ∀ query<row.size,(row.getD query 0).den ∣ D

theorem zeroRow_denominator (width D : ℕ) : RowDenominator (Array.replicate width 0) D := by
  intro query inside
  have bound : query<width := by simpa only [Array.size_replicate] using inside
  simp [Array.getD_eq_getD_getElem?,bound]

/-- All partial sums retain the SAME common denominator. Generic
bit-length addition repeated once per cell would insert a forbidden M
factor in the original linear-Q operand envelope. -/
theorem bump_denominator (row : Array ℚ) (D index : ℕ) (amount : ℚ)
    (inside : index<row.size) (before : RowDenominator row D) (added : amount.den ∣ D) :
    RowDenominator (PDROC.endpointArrayBump row index amount) D := by
  intro query bound
  rw [PDROC.endpointArrayBump_size] at bound
  rw [PDROC.endpointArrayBump_getD row index query amount inside]
  have selected : (if index=query then amount else 0).den ∣ D := by
    by_cases same : index=query
    · simpa only [ite_eq_left same] using added
    · simp only [ite_eq_right same]
      simp
  exact (Rat.add_den_dvd_lcm _ _).trans (Nat.lcm_dvd (before query bound) selected)

theorem scatter_denominator {width : ℕ} (commands : List (Fin width × ℚ)) (initial : Array ℚ)
    (D : ℕ) (size : initial.size=width) (before : RowDenominator initial D)
    (masses : ∀ command∈commands,command.2.den ∣ D) :
    RowDenominator (PDROC.endpointArrayScatter commands initial) D := by
  induction commands generalizing initial with
  | nil => exact before
  | cons command rest ih =>
    have inside : command.1.val < initial.size := by rw [size]; exact command.1.isLt
    have one := bump_denominator initial D command.1.val command.2 inside before (masses command (by simp))
    change RowDenominator (PDROC.endpointArrayScatter rest (PDROC.endpointArrayBump initial command.1.val command.2)) D
    exact ih _ (by simpa only [PDROC.endpointArrayBump_size] using size) one
      (fun entry member => masses entry (by simp only [List.mem_cons]; exact Or.inr member))

/-- The actual write buffer after ANY state-prefix of one original row
update has denominator dividing D^(clock+1), independently of M/cursor. -/
theorem rowScatterPrefix_denominator (P : Parameters) (level clock cursor : ℕ) :
    RowDenominator (rowScatterPrefix P level (P.walkRow level true clock) cursor)
      (P.channelCommonDenominator^(clock+1)) := by
  apply scatter_denominator _ _ _ (Array.size_replicate ..)
    (zeroRow_denominator (2*level+1) (P.channelCommonDenominator^(clock+1)))
  intro command member
  obtain ⟨state,_stateMember,letterMember⟩ := List.mem_flatMap.mp member
  obtain ⟨letter,_letterMember,equation⟩ := List.mem_map.mp letterMember
  subst command
  have previous := PDROC.DataBits.endpointWalkDistribution_den_dvd P level true clock state
  have channel := PDROC.DataBits.channel_den_dvd P true letter
  have product := (Rat.mul_den_dvd _ _).trans (Nat.mul_dvd_mul previous channel)
  obtain ⟨factor,equation⟩ := product
  refine ⟨factor,?_⟩
  simpa only [walkDistribution,pow_succ] using equation

end PDLower.CalibrationCompute
