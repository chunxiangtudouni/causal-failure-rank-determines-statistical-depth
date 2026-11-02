module

public import Paid.PDLower_CalibrationCompute_IntermediateMass_054

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDLower.CalibrationCompute

def rowLeftPrefix (P : Parameters) (level clock cursor : ℕ) (inside : cursor<2*level+1) : Array ℚ :=
  PDROC.endpointArrayBump (rowScatterPrefix P level (P.walkRow level true clock) cursor)
    (walkMove level ⟨cursor,inside⟩ (0 : Fin 2)).val
    ((P.walkRow level true clock).getD cursor 0*(1/2-P.certificate.gamma))

theorem bump_getD_mono (row : Array ℚ) (index query : ℕ) (amount : ℚ)
    (inside : index<row.size) (nonnegative : 0≤amount) :
    row.getD query 0≤(PDROC.endpointArrayBump row index amount).getD query 0 := by
  rw [PDROC.endpointArrayBump_getD row index query amount inside]
  apply le_add_of_nonneg_right
  split_ifs
  · exact nonnegative
  · exact le_rfl

/-- The transient AFTER the first of the two outgoing letters is also
covered; absorbed equal targets cannot be treated as one store. -/
theorem rowLeftPrefix_bounds (P : Parameters) (level clock cursor : ℕ) (inside : cursor<2*level+1)
    (query : WalkCell level) :
    0≤(rowLeftPrefix P level clock cursor inside).getD query.val 0 ∧
      (rowLeftPrefix P level clock cursor inside).getD query.val 0≤1 := by
  let previous := P.walkRow level true clock
  let partialRow := rowScatterPrefix P level previous cursor
  let left := (walkMove level ⟨cursor,inside⟩ (0 : Fin 2)).val
  let right := (walkMove level ⟨cursor,inside⟩ (1 : Fin 2)).val
  have oldMass : 0≤previous.getD cursor 0 := PDROC.endpointWalkDistribution_nonneg P level true clock ⟨cursor,inside⟩
  have pa : 0≤(1/2-P.certificate.gamma : ℚ) := (P.experiment.channel_pos true (0 : Fin 2)).le
  have pb : 0≤(1/2+P.certificate.gamma : ℚ) := (P.experiment.channel_pos true (1 : Fin 2)).le
  have leftInside : left<partialRow.size := by
    simpa only [partialRow,rowScatterPrefix_size] using (walkMove level ⟨cursor,inside⟩ (0 : Fin 2)).isLt
  have earlier := bump_getD_mono partialRow left query.val (previous.getD cursor 0*(1/2-P.certificate.gamma))
    leftInside (mul_nonneg oldMass pa)
  have previousBounds := rowScatterPrefix_bounds P level clock cursor query
  have later := bump_getD_mono (rowLeftPrefix P level clock cursor inside) right query.val
    (previous.getD cursor 0*(1/2+P.certificate.gamma)) (by
      simpa only [rowLeftPrefix,PDROC.endpointArrayBump_size,rowScatterPrefix_size] using
        (walkMove level ⟨cursor,inside⟩ (1 : Fin 2)).isLt) (mul_nonneg oldMass pb)
  have nextBounds := rowScatterPrefix_bounds P level clock (cursor+1) query
  rw [rowScatterPrefix_succ P level previous cursor inside] at nextBounds
  exact ⟨previousBounds.1.trans earlier,later.trans nextBounds.2⟩

theorem rowLeftPrefix_denominator (P : Parameters) (level clock cursor : ℕ)
    (inside : cursor<2*level+1) :
    RowDenominator (rowLeftPrefix P level clock cursor inside) (P.channelCommonDenominator^(clock+1)) := by
  have previous := PDROC.DataBits.endpointWalkDistribution_den_dvd P level true clock ⟨cursor,inside⟩
  have channel := PDROC.DataBits.channel_den_dvd P true (0 : Fin 2)
  have product := (Rat.mul_den_dvd _ _).trans (Nat.mul_dvd_mul previous channel)
  have letterValue : P.experiment.channel true (0 : Fin 2)=(1/2-P.certificate.gamma) := rfl
  rw [letterValue] at product
  apply bump_denominator _ _ _ _
    (by simpa only [rowScatterPrefix_size] using (walkMove level ⟨cursor,inside⟩ (0 : Fin 2)).isLt)
    (rowScatterPrefix_denominator P level clock cursor)
  obtain ⟨factor,equation⟩ := product
  refine ⟨factor,?_⟩
  simpa only [walkDistribution,pow_succ] using equation

theorem rowLeftPrefix_numAbs_le_den (P : Parameters) (level clock cursor : ℕ) (inside : cursor<2*level+1)
    (query : WalkCell level) :
    ((rowLeftPrefix P level clock cursor inside).getD query.val 0).num.natAbs≤
      ((rowLeftPrefix P level clock cursor inside).getD query.val 0).den := by
  have bounded := rowLeftPrefix_bounds P level clock cursor inside query
  exact PDROC.DataBits.ratNumAbs_le_den _ bounded.1 bounded.2

end PDLower.CalibrationCompute
