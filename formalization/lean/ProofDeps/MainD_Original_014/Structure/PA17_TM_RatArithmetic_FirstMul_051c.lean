module
public import Structure.PA17_TM_RatArithmetic_FirstMul_051b
public import Structure.PA17_TM_RatArithmetic_PairInput_050e
public import Structure.PA17_TM_RatArithmetic_MulFields_048b

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFirstMul051

open Turing PA17TMRatArithmeticWidth018 PA17TMRatArithmeticParse002
open PA17TMRatArithmeticPairInput050 PA17TMRatArithmeticFarLoad031
open PA17TMRatArithmeticBookmark014 PA17TMRatArithmeticSignRead021
open PA17TMRatArithmeticWideCache045 PA17TMRatArithmeticNativeCache030
open PA17TMRatArithmeticMulFields048

def firstCycleOutput (x y : Rat) (counter : List Bool) (newGap : Nat) : Tape Bool :=
  cycleOutput (sign x) counter (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail newGap (x.num.natAbs*y.num.natAbs)

def firstCycleFee (memory : Nat) (x y : Rat) (gap newGap : Nat) : Nat :=
  cycleFee .nx .ny memory (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail gap newGap x.num.natAbs y.num.natAbs

/-- This internal entry invariant is discharged by049's actual six-bit
observation. No width, native answer or allocation is an original input. -/
theorem firstCycle_contract (p : Nat) (memory : Fin (p+1)) (x y : Rat)
    (holds : memory.val%32=(mNx x y).val) (counter : List Bool) :
    ∃ newGap trace, 6≤newGap ∧ newGap≤2*allocationK*(fieldWidth x y)^2 ∧
      PSTRTMSeq005.RunsFrom (cycleMachine p .nx .ny)
        ⟨cycleEntry p memory,firstMInput x y counter (allocationK*(fieldWidth x y)^2)⟩ trace
        ⟨cyclePort p memory,firstCycleOutput x y counter newGap⟩ ∧
      trace.length≤firstCycleFee memory.val x y (allocationK*(fieldWidth x y)^2) newGap ∧
      ∀ prefixLength chargedL, visitedSpace (cycleMachine p .nx .ny) chargedL
        (trace.take prefixLength)≤chargedL+
          2*firstCycleFee memory.val x y (allocationK*(fieldWidth x y)^2) newGap+1 := by
  have ha : restoredDigits .nx memory.val (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail=PA17TMRatArithmeticPairEncode017.payload x.num.natAbs := by
    simpa only [originalDigits,numeratorDigits,PA17TMRatArithmeticPairEncode017.payload] using
      actual_restored_with_carry .nx memory.val x y holds
  have hb : restoredDigits .ny memory.val (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail=PA17TMRatArithmeticPairEncode017.payload y.num.natAbs := by
    simpa only [originalDigits,numeratorDigits,PA17TMRatArithmeticPairEncode017.payload] using
      actual_restored_with_carry .ny memory.val x y holds
  have hw : 1≤fieldWidth x y := by have h := fieldWidth_ge_four x y;omega
  have size := (five_scales x y).1
  obtain ⟨newGap,trace,lower,upper,run,time,space⟩ :=
    cycle_contract p .nx .ny memory (sign x) counter (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail (allocationK*(fieldWidth x y)^2)
      x.num.natAbs y.num.natAbs ha hb (allocated_room _ _ _ hw size)
  refine ⟨newGap,trace,lower,new_gap_bound _ _ _ _ hw size upper,?_,time,space⟩
  simpa only [firstMInput,ratHeaderTape,firstCycleOutput] using run

theorem firstCycleFee_polynomial (memory : Nat) (x y : Rat)
    (holds : memory%32=(mNx x y).val) (newGap : Nat)
    (actualGap : newGap≤2*allocationK*(fieldWidth x y)^2) :
    firstCycleFee memory x y (allocationK*(fieldWidth x y)^2) newGap≤
      8192*(allocationK+256)*((encode [.rational x,.rational y]).length+1)^3 := by
  let w := fieldWidth x y
  let n := (encode [.rational x,.rational y]).length+1
  have hw : 1≤w := by have h := fieldWidth_ge_four x y;dsimp [w];omega
  have wn : w≤n := by have h := original_width_le_input x y;dsimp [w,n];omega
  have nn : 1≤n := by dsimp [n];omega
  have ww : w^2≤n^3 := by
    have h2 := Nat.pow_le_pow_left wn 2
    have h3 : n^2≤n^3 := by
      change n^2≤n^2*n
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (n^2) nn
    exact h2.trans h3
  have w1 : w≤n^3 :=
    (by simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left w hw : w≤w^2).trans ww
  have one : 1≤n^3 := by simpa only [one_pow] using Nat.pow_le_pow_left nn 3
  have load := (firstMFee_uniform memory x y holds (allocationK*(fieldWidth x y)^2)).trans
    (Nat.mul_le_mul_left 4096 (allocated_uniform_polynomial allocationK x y))
  have s := (five_scales x y).1
  have sq := Nat.pow_le_pow_left s 2
  have native : 65536*(scale x.num.natAbs y.num.natAbs)^2≤1048576*n^3 := by
    dsimp [w] at ww
    nlinarith
  have magnitude := productMagnitude_bits x y
  have width := original_source_width x y
  change PA17TMRatArithmeticFarLoad031.bankWidth (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail=fieldWidth x y at width
  change firstMFee memory x y (allocationK*(fieldWidth x y)^2)+
    65536*(scale x.num.natAbs y.num.natAbs)^2+
    (newGap+2*natBits (x.num.natAbs*y.num.natAbs)+2*
      PA17TMRatArithmeticFarLoad031.bankWidth (numeratorDigits x).tail (denominatorDigits x).tail
        (numeratorDigits y).tail (denominatorDigits y).tail+49)≤_
  rw [width]
  change natBits (x.num.natAbs*y.num.natAbs)≤w at magnitude
  have home : newGap+2*natBits (x.num.natAbs*y.num.natAbs)+2*fieldWidth x y+49≤
      (2*allocationK+53)*n^3 := by
    change newGap≤2*allocationK*w^2 at actualGap
    have g := actualGap.trans (Nat.mul_le_mul_left (2*allocationK) ww)
    change newGap+2*natBits (x.num.natAbs*y.num.natAbs)+2*w+49≤_
    nlinarith
  change firstMFee memory x y (allocationK*(fieldWidth x y)^2)≤4096*((allocationK+2)*n^3) at load
  change _≤8192*(allocationK+256)*n^3
  nlinarith

/-- The SAME real first multiplication cycle, full opaque saved carry,
trueHALT, canonical stored M and every original visitedSpace prefix. -/
theorem firstCycle_polynomial_contract (p : Nat) (memory : Fin (p+1)) (x y : Rat)
    (holds : memory.val%32=(mNx x y).val) (counter : List Bool) :
    ∃ newGap trace, 6≤newGap ∧ newGap≤2*allocationK*(fieldWidth x y)^2 ∧
      PSTRTMSeq005.RunsFrom (cycleMachine p .nx .ny)
        ⟨cycleEntry p memory,firstMInput x y counter (allocationK*(fieldWidth x y)^2)⟩ trace
        ⟨cyclePort p memory,firstCycleOutput x y counter newGap⟩ ∧
      trace.length≤32768*(allocationK+256)*((encode [.rational x,.rational y]).length+1)^3 ∧
      ∀ prefixLength, visitedSpace (cycleMachine p .nx .ny) (encode [.rational x,.rational y]).length
        (trace.take prefixLength)≤32768*(allocationK+256)*((encode [.rational x,.rational y]).length+1)^3 := by
  obtain ⟨newGap,trace,lower,upper,run,time,space⟩ := firstCycle_contract p memory x y holds counter
  have fee := firstCycleFee_polynomial memory.val x y holds newGap upper
  have input : (encode [.rational x,.rational y]).length+1≤
      ((encode [.rational x,.rational y]).length+1)^3 := by
    have nn : 1≤(encode [.rational x,.rational y]).length+1 := by omega
    have square : 1≤((encode [.rational x,.rational y]).length+1)^2 := by
      simpa only [one_pow] using Nat.pow_le_pow_left nn 2
    simpa only [one_mul,pow_succ] using
      Nat.mul_le_mul_right ((encode [.rational x,.rational y]).length+1) square
  have padded : (encode [.rational x,.rational y]).length+
      2*firstCycleFee memory.val x y (allocationK*(fieldWidth x y)^2) newGap+1≤
      (2*(8192*(allocationK+256))+1)*((encode [.rational x,.rational y]).length+1)^3 := by
    nlinarith only [fee,input]
  have padded_final : (encode [.rational x,.rational y]).length+
      2*firstCycleFee memory.val x y (allocationK*(fieldWidth x y)^2) newGap+1≤
      32768*(allocationK+256)*((encode [.rational x,.rational y]).length+1)^3 :=
    padded.trans (Nat.mul_le_mul_right _ (by decide))
  refine ⟨newGap,trace,lower,upper,run,?_,?_⟩
  · exact time.trans (fee.trans (Nat.mul_le_mul_right _ (by decide)))
  · intro prefixLength
    exact (space prefixLength (encode [.rational x,.rational y]).length).trans padded_final

theorem firstCycle64_polynomial_contract (x y : Rat) (counter : List Bool) :
    ∃ newGap trace, 6≤newGap ∧ newGap≤2*allocationK*(fieldWidth x y)^2 ∧
      PSTRTMSeq005.RunsFrom (cycleMachine 63 .nx .ny)
        ⟨cycleEntry 63 (selectedMemory (mNx x y) (sign x)),
          firstMInput x y counter (allocationK*(fieldWidth x y)^2)⟩ trace
        ⟨cyclePort 63 (selectedMemory (mNx x y) (sign x)),firstCycleOutput x y counter newGap⟩ ∧
      trace.length≤32768*(allocationK+256)*((encode [.rational x,.rational y]).length+1)^3 ∧
      ∀ prefixLength, visitedSpace (cycleMachine 63 .nx .ny) (encode [.rational x,.rational y]).length
        (trace.take prefixLength)≤32768*(allocationK+256)*((encode [.rational x,.rational y]).length+1)^3 :=
  firstCycle_polynomial_contract 63 _ x y (selectedMemory_retains_old _ _) counter

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFirstMul051
