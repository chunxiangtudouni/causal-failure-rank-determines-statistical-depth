module

public import Paid.PDROC_BitVM_VM_Phases_Original_014
public import Paid.PDROC_BitVM_VM_Backend_Polynomial_004
public import Paid.PDROC_BitVM_Size_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.VM.OriginalClaims

open Turing PaperProofs.Paid.Computation

/-- Original raw input and the established source length, with no new
runtime parameter. The extra degree allows the source degree to be0. -/
theorem source_sum_bound (sourceC sourceD I N S : ℕ) (positive : 1 ≤ S)
    (raw : I ≤ 24 * S) (sourceTime : N ≤ sourceC * S^sourceD) :
    I + N + 1 ≤ (sourceC + 25) * S^(sourceD + 1) := by
  have liftSource : S^sourceD ≤ S^(sourceD + 1) :=
    Nat.pow_le_pow_right positive (by omega)
  have liftSize : S ≤ S^(sourceD + 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right positive (by omega : 1 ≤ sourceD + 1)
  have liftOne : 1 ≤ S^(sourceD + 1) := positive.trans liftSize
  calc
    I + N + 1 ≤ 24 * S^(sourceD + 1) + sourceC * S^(sourceD + 1) + S^(sourceD + 1) :=
      Nat.add_le_add (Nat.add_le_add (raw.trans (Nat.mul_le_mul_left 24 liftSize))
        (sourceTime.trans (Nat.mul_le_mul_left sourceC liftSource))) liftOne
    _ = (sourceC + 25) * S^(sourceD + 1) := by ring

/-- ORIGINAL claim, as SOURCE ONLY pending parent Lean validation and
the final public/private-origin audit. The real eight-phase source
producer discharges all intermediate simulation premises. A single
fixed Bool machine and common constants precede every gamma/P/fee;
the same once-selected bit run supplies exact output, time and space. -/
theorem uniform_bit_implementation_claims : UniformBitImplementationClaims := by
  classical
  obtain ⟨prepareCode, coreCode, sourceC, sourceD, _sourcePositive, sourceRuns⟩ :=
    Phases.Original.original_source ISA.fixedRatBackend
  let source := Phases.program ISA.fixedRatBackend prepareCode coreCode
  have closed := Phases.supports ISA.fixedRatBackend prepareCode coreCode
  obtain ⟨states, machine, backendC, _backendPositive, compiled⟩ :=
    Backend.uniform_original_raw_backend_polynomial source closed
  let A := backendC * (sourceC + 25)^2
  let degree := (sourceD + 1) * 2
  apply PDROC.BitVM.Size.claims_of_variable states machine (2 * A + 25) degree (by omega)
  intro P fee nonnegative
  obtain ⟨sourceTrace, sourceFinal, first, chain, last, halt, output, sourceTime⟩ :=
    sourceRuns P fee nonnegative
  have nonempty : 0 < (sourceFinal.stk (0 : ISA.Stack)).length := by
    rw [output]
    exact List.length_pos_iff_ne_nil.mpr (Phases.encoded_nonempty _)
  obtain ⟨trace, final, actual, naked, clock, space, _prefixSpace⟩ :=
    compiled P fee sourceTrace sourceFinal first chain last halt nonempty
  let S := variableGammaSize P fee
  have sizePositive : 1 ≤ S := PDROC.BitVM.Size.variable_positive P fee
  have rawLength : (encodeBits (rawInput P fee)).length ≤ 24 * S :=
    PDROC.BitVM.Size.raw_input_length P fee
  have combined := source_sum_bound sourceC sourceD (encodeBits (rawInput P fee)).length
    sourceTrace.length S sizePositive rawLength sourceTime
  have backendTime : backendC * ((encodeBits (rawInput P fee)).length + sourceTrace.length + 1)^2 ≤
      A * S^degree := by
    simpa only [A, degree, mul_pow, ← pow_mul, Nat.mul_assoc] using
      Nat.mul_le_mul_left backendC (Nat.pow_le_pow_left combined 2)
  have liftSize : S ≤ S^degree := by
    have enough : 1 ≤ degree := by dsimp only [degree]; omega
    simpa only [pow_one] using Nat.pow_le_pow_right sizePositive enough
  have liftRaw : (encodeBits (rawInput P fee)).length ≤ 24 * S^degree :=
    rawLength.trans (Nat.mul_le_mul_left 24 liftSize)
  have liftOne : 1 ≤ S^degree := sizePositive.trans liftSize
  have coefficient : A ≤ 2 * A + 25 := by omega
  have clockBound : trace.length ≤ (2 * A + 25) * S^degree :=
    (clock.trans backendTime).trans (Nat.mul_le_mul_right _ coefficient)
  have spaceBound : visitedBitSpace machine (encodeBits (rawInput P fee)).length trace ≤
      (2 * A + 25) * S^degree := by
    apply space.trans
    calc
      _ ≤ 24 * S^degree + 2 * (A * S^degree) + S^degree :=
        Nat.add_le_add (Nat.add_le_add liftRaw (Nat.mul_le_mul_left 2 backendTime)) liftOne
      _ = (2 * A + 25) * S^degree := by ring
  have exactOutput : final.Tape.right₀ = ListBlank.mk (encodeBits (encodeArtifact (buildArtifact P fee))) := by
    rw [output] at naked
    exact naked
  exact ⟨trace, final, actual, exactOutput, clockBound, spaceBound⟩

end PDROC.BitVM.VM.OriginalClaims
