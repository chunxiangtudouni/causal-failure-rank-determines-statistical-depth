module
public import Structure.PA17_TM_RatArithmetic_DivZero_068a

/-! Original-input fourth-power bounds for the SAME real zero-branch code.
Record bounds are internal invariants of the two actual native producers;
they are not qualifications of an original rational input or an oracle. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticDivZero068

open Turing
open PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticParse002
open PA17TMRatArithmeticBookmark014
open PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticCachedOuter043
open PA17TMRatArithmeticWideCache045 (allocationK)
open PA17TMRatArithmeticAllocationBounds056

def localCoefficient : Nat := 128*(allocationK+256)
def timeBoundCoefficient : Nat := timeCoefficient allocationK+localCoefficient
def coefficient : Nat := 4*timeBoundCoefficient

theorem coefficient_pos : 0<coefficient := by
  unfold coefficient timeBoundCoefficient localCoefficient
  positivity

private theorem original_sourceWidth (x y : Rat) :
    sourceWidth (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail=fieldWidth x y := by
  exact originalWidth_eq x y

private theorem local_fee_le (first second : RecordSpec) (x y : Rat)
    (hg : ∀ r∈[first,second],r.gap≤2*allocationK*(fieldWidth x y)^2)
    (hv : ∀ r∈[first,second],r.digits.length≤fieldWidth x y) :
    localFee [first,second] (fieldWidth x y) (allocationK*(fieldWidth x y)^2)≤
      localCoefficient*((encode [.rational x,.rational y]).length+1)^4 := by
  let w := fieldWidth x y
  let n := (encode [.rational x,.rational y]).length+1
  obtain ⟨hgap,hwidth⟩ := cache_totals_le 2 [first,second] rfl (by decide) x y hg hv
  have hn : 1≤n := by dsimp only [n];omega
  have hw : w≤n := by
    have h := original_width_le_input x y
    dsimp only [w,n]
    omega
  have hn2 : n^2≤n^4 := Nat.pow_le_pow_right hn (by decide : (2 : Nat) ≤ 4)
  have hw2 : w^2≤n^4 := (Nat.pow_le_pow_left hw 2).trans hn2
  have hw1 : w≤n^4 := hw.trans (by
    simpa only [pow_one] using Nat.pow_le_pow_right hn (by decide : (1 : Nat) ≤ 4))
  have h1 : 1≤n^4 := by simpa only [one_pow] using Nat.pow_le_pow_left hn 4
  have base : localFee [first,second] w (allocationK*w^2)≤
      53*allocationK*w^2+92*w+281 := by
    have ht := Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left 5 hgap) (Nat.mul_le_mul_left 16 hwidth))
      (Nat.le_refl (12*w+3*(allocationK*w^2)+281))
    calc
      _ = (5*totalGap [first,second]+16*totalWidth [first,second])+
          (12*w+3*(allocationK*w^2)+281) := by unfold localFee;ring
      _ ≤ (5*(10*allocationK*w^2)+16*(5*w))+(12*w+3*(allocationK*w^2)+281) := ht
      _ = _ := by ring
  have terms := Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left (53*allocationK) hw2) (Nat.mul_le_mul_left 92 hw1))
    (Nat.mul_le_mul_left 281 h1)
  calc
    _ ≤ 53*allocationK*w^2+92*w+281 := base
    _ ≤ 53*allocationK*n^4+92*n^4+281*n^4 := terms
    _ = (53*allocationK+373)*n^4 := by ring
    _ ≤ localCoefficient*n^4 := Nat.mul_le_mul_right _ (by unfold localCoefficient;omega)

theorem original_zeroFee_le (first second : RecordSpec) (x y : Rat)
    (hg : ∀ r∈[first,second],r.gap≤2*allocationK*(fieldWidth x y)^2)
    (hv : ∀ r∈[first,second],r.digits.length≤fieldWidth x y) :
    zeroFee [first,second] (fieldWidth x y)≤
      timeBoundCoefficient*((encode [.rational x,.rational y]).length+1)^4 := by
  have ha := original_outerFee_le 2 [first,second] rfl (by decide) x y hg hv
  have hl := local_fee_le first second x y hg hv
  calc
    _ ≤ timeCoefficient allocationK*((encode [.rational x,.rational y]).length+1)^4+
        localCoefficient*((encode [.rational x,.rational y]).length+1)^4 := Nat.add_le_add ha hl
    _ = _ := by unfold timeBoundCoefficient;ring

theorem original_zero_bounded (first second : RecordSpec) (x y : Rat) :
    BoundedRun zeroMachine
      (Tape.mk₂ [false] (prefixRight (sign x) (originalBank x y (bankTail [first,second] []))))
      zeroPort (Tape.mk₁ (encode [.rational (0 : Rat)])) (zeroFee [first,second] (fieldWidth x y)) := by
  have h := zero_bounded (sign x) (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail first second
  rw [original_sourceWidth] at h
  exact h

/-- The global real058-observed Dzero branch enters numeric0. This theorem
does not replace that observation with a host test: it proves the physical
constant terminal branch after entry, for the actual two produced records. -/
theorem original_zero_contract (first second : RecordSpec) (x y : Rat)
    (hg : ∀ r∈[first,second],r.gap≤2*allocationK*(fieldWidth x y)^2)
    (hv : ∀ r∈[first,second],r.digits.length≤fieldWidth x y) :
    ∃ trace, PSTRTMSeq005.RunsFrom zeroMachine
        ⟨0,Tape.mk₂ [false] (prefixRight (sign x)
          (originalBank x y (bankTail [first,second] [])))⟩ trace
        ⟨zeroPort,Tape.mk₁ (encode [.rational (0 : Rat)])⟩ ∧
      trace.length≤coefficient*((encode [.rational x,.rational y]).length+1)^4 ∧
      ∀ prefixLength, visitedSpace zeroMachine (encode [.rational x,.rational y]).length
        (trace.take prefixLength)≤coefficient*((encode [.rational x,.rational y]).length+1)^4 := by
  obtain ⟨trace,hr,ht⟩ := original_zero_bounded first second x y
  let i := (encode [.rational x,.rational y]).length
  have hf := original_zeroFee_le first second x y hg hv
  have time : trace.length≤timeBoundCoefficient*(i+1)^4 := ht.trans hf
  have hi : i+1≤(i+1)^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (Nat.succ_le_succ (Nat.zero_le i)) (by decide : (1 : Nat) ≤ 4)
  have hc : 1≤timeBoundCoefficient := by
    unfold timeBoundCoefficient localCoefficient
    omega
  have compare : timeBoundCoefficient≤coefficient := by unfold coefficient;omega
  refine ⟨trace,hr,time.trans (Nat.mul_le_mul_right _ compare),?_⟩
  intro prefixLength
  have hs := PSTRTMTrace002.visitedSpace_le zeroMachine i (trace.take prefixLength)
  have hp : (trace.take prefixLength).length≤trace.length := by
    simp only [List.length_take]
    omega
  have space : visitedSpace zeroMachine i (trace.take prefixLength) ≤ i+2*trace.length+1 := by omega
  have hn : i+1≤timeBoundCoefficient*(i+1)^4 := hi.trans
    (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right ((i+1)^4) hc)
  change visitedSpace zeroMachine i (trace.take prefixLength)≤coefficient*(i+1)^4
  unfold coefficient
  calc
    _ ≤ i+2*(timeBoundCoefficient*(i+1)^4)+1 := by omega
    _ = (i+1)+2*(timeBoundCoefficient*(i+1)^4) := by omega
    _ ≤ timeBoundCoefficient*(i+1)^4+2*(timeBoundCoefficient*(i+1)^4) := Nat.add_le_add_right hn _
    _ = 3*(timeBoundCoefficient*(i+1)^4) := by ring
    _ ≤ 4*(timeBoundCoefficient*(i+1)^4) := Nat.mul_le_mul_right _ (by decide : (3 : Nat) ≤ 4)
    _ = _ := by ring

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticDivZero068
