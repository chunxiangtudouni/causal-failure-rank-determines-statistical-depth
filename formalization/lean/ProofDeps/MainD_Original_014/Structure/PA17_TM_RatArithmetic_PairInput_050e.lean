module
public import Structure.PA17_TM_RatArithmetic_PairInput_050d

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairInput050

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticFarLoad031
open PA17TMRatArithmeticMul047 PA17TMRatArithmeticParse002 PA17TMRatArithmeticBookmark014

theorem pairFee_uniform (fieldA fieldB : SourceField) (memory : Nat)
    (nxTail dxTail nyTail dyTail : List Bool) (gap a b : Nat)
    (ha : restoredDigits fieldA memory nxTail dxTail nyTail dyTail=PA17TMRatArithmeticPairEncode017.payload a)
    (hb : restoredDigits fieldB memory nxTail dxTail nyTail dyTail=PA17TMRatArithmeticPairEncode017.payload b) :
    pairFee fieldA fieldB memory nxTail dxTail nyTail dyTail gap a b≤
      4096*uniformBudget nxTail dxTail nyTail dyTail gap := by
  let w := bankWidth nxTail dxTail nyTail dyTail
  let budget := uniformBudget nxTail dxTail nyTail dyTail gap
  let m := (false::sourceTail fieldB nxTail dxTail nyTail dyTail).length
  let cost := sourceCost fieldB dxTail nyTail dyTail
  let first := (restoredDigits fieldA memory nxTail dxTail nyTail dyTail).length
  have hw : 4≤w := by
    change 4≤(false::nxTail).length+(false::dxTail).length+(false::nyTail).length+(false::dyTail).length
    simp only [List.length_cons]
    omega
  have hm : m≤w := source_length_le_width fieldB nxTail dxTail nyTail dyTail
  have hc : cost≤2*w+23 := source_cost_le_width fieldB nxTail dxTail nyTail dyTail
  have hn : navigationFee nxTail dxTail nyTail≤2*w+17 := navigation_fee_le_width nxTail dxTail nyTail dyTail
  have hfirst : first≤w := by
    simpa only [first,restoredDigits,List.length_cons] using
      source_length_le_width fieldA nxTail dxTail nyTail dyTail
  have hpa : (PA17TMRatArithmeticPairEncode017.payload a).length≤w := by rw [←ha];exact hfirst
  have hpb : (PA17TMRatArithmeticPairEncode017.payload b).length≤w := by
    rw [←hb]
    simpa only [m,restoredDigits,List.length_cons] using hm
  have load : navigationFee nxTail dxTail nyTail+
      copyFee (false::sourceTail fieldA nxTail dxTail nyTail dyTail)
        (sourceCost fieldA dxTail nyTail dyTail) gap+2≤128*budget :=
    loader_fee_le_uniform fieldA nxTail dxTail nyTail dyTail gap
  have home : gap+2*w+41≤64*budget := by
    change gap+2*w+41≤64*((w+1)*(w+gap+1))
    nlinarith [Nat.zero_le (w*gap),Nat.zero_le (w*w)]
  have mm := Nat.pow_le_pow_left hm 2
  have product : (2*cost+2*gap+4*first+51)*m≤(8*w+2*gap+97)*w :=
    Nat.mul_le_mul (by omega) hm
  have second : secondFee fieldB nxTail dxTail nyTail dyTail
      (restoredDigits fieldA memory nxTail dxTail nyTail dyTail) gap≤128*budget := by
    change navigationFee nxTail dxTail nyTail+
      (4*m^2+(2*cost+2*gap+4*first+51)*m+3*cost+3*gap+6*first+42)+2≤128*((w+1)*(w+gap+1))
    nlinarith [Nat.zero_le (w*gap),Nat.zero_le (w*w)]
  have hs : (PA17TMRatArithmeticPairEncode017.payload a).length+
      (PA17TMRatArithmeticPairEncode017.payload b).length+1≤2*w+1 := by omega
  have square := Nat.pow_le_pow_left hs 2
  have serialize : 64*((PA17TMRatArithmeticPairEncode017.payload a).length+
      (PA17TMRatArithmeticPairEncode017.payload b).length+1)^2≤256*budget := by
    change 64*((PA17TMRatArithmeticPairEncode017.payload a).length+
      (PA17TMRatArithmeticPairEncode017.payload b).length+1)^2≤256*((w+1)*(w+gap+1))
    nlinarith [Nat.zero_le (w*gap)]
  unfold pairFee firstFee
  omega

theorem original_source_width (x y : Rat) :
    bankWidth (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail=fieldWidth x y :=
  PA17TMRatArithmeticWidth018.originalWidth_eq x y

theorem firstMFee_uniform (memory : Nat) (x y : Rat) (holds : memory%32=(mNx x y).val) (gap : Nat) :
    firstMFee memory x y gap≤4096*((fieldWidth x y+1)*(fieldWidth x y+gap+1)) := by
  have ha : restoredDigits .nx memory (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail=PA17TMRatArithmeticPairEncode017.payload x.num.natAbs := by
    simpa only [originalDigits,numeratorDigits,PA17TMRatArithmeticPairEncode017.payload] using
      actual_restored_with_carry .nx memory x y holds
  have hb : restoredDigits .ny memory (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail=PA17TMRatArithmeticPairEncode017.payload y.num.natAbs := by
    simpa only [originalDigits,numeratorDigits,PA17TMRatArithmeticPairEncode017.payload] using
      actual_restored_with_carry .ny memory x y holds
  have h := pairFee_uniform .nx .ny memory (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail gap x.num.natAbs y.num.natAbs ha hb
  simpa only [firstMFee,uniformBudget,original_source_width] using h

theorem allocated_uniform_polynomial (k : Nat) (x y : Rat) :
    (fieldWidth x y+1)*(fieldWidth x y+k*(fieldWidth x y)^2+1)≤
      (k+2)*((encode [.rational x,.rational y]).length+1)^3 := by
  let w := fieldWidth x y
  have hbase : w+k*w^2+1≤(k+2)*(w+1)^2 := by
    nlinarith [Nat.zero_le (k*w),Nat.zero_le (w*w)]
  have hm := Nat.mul_le_mul_left (w+1) hbase
  have hnorm : (w+1)*((k+2)*(w+1)^2)=(k+2)*(w+1)^3 := by ring
  rw [hnorm] at hm
  have hp := Nat.pow_le_pow_left (Nat.add_le_add_right (PA17TMRatArithmeticWidth018.original_width_le_input x y) 1) 3
  exact hm.trans (Nat.mul_le_mul_left (k+2) hp)

/-- Charges this real parsed-header stage to ORIGINAL input length after
the earlier real allocator produces kW². This is no new raw-input run:
the genuine49 frontend/control transfer must still be composed by Root. -/
theorem firstM_polynomial_contract (p k : Nat) (memory : Fin (p+1)) (x y : Rat)
    (holds : memory.val%32=(mNx x y).val) (counter : List Bool) :
    ∃ trace, PSTRTMSeq005.RunsFrom (pairInputMachine p .nx .ny)
        ⟨pairEntry p memory,firstMInput x y counter (k*(fieldWidth x y)^2)⟩ trace
        ⟨pairPort p memory,firstMOutput x y counter (k*(fieldWidth x y)^2)⟩ ∧
      trace.length≤8192*(k+3)*((encode [.rational x,.rational y]).length+1)^3 ∧
      ∀ prefixLength, visitedSpace (pairInputMachine p .nx .ny) (encode [.rational x,.rational y]).length
        (trace.take prefixLength)≤8192*(k+3)*((encode [.rational x,.rational y]).length+1)^3 := by
  obtain ⟨trace,hr,hl,hs⟩ := firstM_contract p memory x y holds counter (k*(fieldWidth x y)^2)
  have hfee := firstMFee_uniform memory.val x y holds (k*(fieldWidth x y)^2)
  have hpoly := Nat.mul_le_mul_left 4096 (allocated_uniform_polynomial k x y)
  have ht : trace.length≤4096*(k+2)*((encode [.rational x,.rational y]).length+1)^3 := by
    calc
      _ ≤ _ := hl.trans (hfee.trans hpoly)
      _ = _ := by ring
  let i := (encode [.rational x,.rational y]).length
  let power := (i+1)^3
  have hi : i+1≤power := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : (1 : Nat) ≤ i + 1) (by decide : (1 : Nat)≤3)
  refine ⟨trace,hr,ht.trans (Nat.mul_le_mul_right _ (by omega)),?_⟩
  intro prefixLength
  have hspace := hs prefixLength i
  have hcost : firstMFee memory.val x y (k*(fieldWidth x y)^2)≤4096*(k+2)*power := by
    calc
      _ ≤ _ := hfee.trans hpoly
      _ = _ := by ring
  change visitedSpace (pairInputMachine p .nx .ny) i (trace.take prefixLength)≤8192*(k+3)*power
  calc
    _ ≤ (i+1)+8192*(k+2)*power := by nlinarith
    _ ≤ power+8192*(k+2)*power := Nat.add_le_add_right hi _
    _ = (8192*(k+2)+1)*power := by ring
    _ ≤ 8192*(k+3)*power := Nat.mul_le_mul_right power (by omega)

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairInput050
