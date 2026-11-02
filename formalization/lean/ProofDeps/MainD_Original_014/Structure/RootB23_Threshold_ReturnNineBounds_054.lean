module
public import Structure.RootB23_Threshold_ReturnNineActual_053

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnNineBounds
open PaperProofs.Common.Native.RationalControllerComputation
open ReturnNineLayout (Data)

theorem fields_width (v : Data) (memory : Fin 8) :
    ReturnNineDest.width (ReturnNineCopy.fields v memory)=ReturnNineRoute.width v := by
  simp [ReturnNineDest.width,ReturnNineCopy.fields,ReturnNineStep.output,ReturnNineRoute.width,ReturnNineOut.mask]
  omega

theorem width_append (xs ys : List (List Bool)) :
    ReturnNineDest.width (xs++ys)=ReturnNineDest.width xs+ReturnNineDest.width ys := by
  simp only [ReturnNineDest.width,List.map_append,List.sum_append]

theorem take_width (xs : List (List Bool)) (n : ℕ) : ReturnNineDest.width (xs.take n)≤ReturnNineDest.width xs := by
  have split:=congrArg ReturnNineDest.width (List.take_append_drop n xs)
  rw [width_append] at split
  omega

theorem field_length (v : Data) (memory : Fin 8) (index : Fin 9) :
    ((ReturnNineCopy.fields v memory).getD index.val []).length≤ReturnNineRoute.width v := by
  fin_cases index <;>
    simp [ReturnNineCopy.fields,ReturnNineStep.output,ReturnNineRoute.width,ReturnNineOut.mask] <;> omega

private theorem first_fee (n b w : ℕ) (small : n≤w) (bSmall : b≤w) :
    (2*b+18)+(4*n^2+(2*(2*w+128)+41)*n+3*(2*w+128)+29)+(60*n+144)≤4096*(w+1)^2 := by
  have square:=Nat.pow_le_pow_left small 2
  have product:=Nat.mul_le_mul_left w small
  nlinarith only [square,product,small,bSmall,Nat.zero_le w,Nat.zero_le n]

theorem start_fee (v : Data) : ReturnNineStart.fee v≤4096*(ReturnNineRoute.width v+1)^2 := by
  have bSmall : (ReturnNineOut.mask v).b.length≤ReturnNineRoute.width v := by dsimp only [ReturnNineRoute.width];omega
  have nSmall : v.c.length≤ReturnNineRoute.width v := by dsimp only [ReturnNineRoute.width,ReturnNineOut.mask];omega
  exact first_fee _ _ _ nSmall bSmall

private theorem next_fee (a n p w : ℕ) (ha : a≤w) (hn : n≤w) (hp : p≤w) :
    2*a+2*n+(2*w+128+2*p+128)+6≤512*(w+1)^2 := by
  nlinarith only [ha,hn,hp,Nat.zero_le (w^2),Nat.zero_le w]

theorem step_fee (v : Data) (slot : Fin 8) (previous : List (List Bool)) (last : List Bool)
    (lastSmall : last.length≤ReturnNineRoute.width v)
    (previousSmall : ReturnNineDest.width (previous++[last])≤ReturnNineRoute.width v) :
    ReturnNineCopy.stepFee v slot previous last≤16896*(ReturnNineRoute.width v+1)^2 := by
  have copied:=ReturnNineStep.copy_fee_le v slot (previous++[last])
  have widthBound : ReturnNineRoute.width v+ReturnNineDest.width (previous++[last])+1≤2*(ReturnNineRoute.width v+1) := by omega
  have square:=Nat.pow_le_pow_left widthBound 2
  simp only [Nat.mul_pow] at square
  have next:=next_fee _ _ _ _ lastSmall (ReturnNineStep.source_length v slot) previousSmall
  dsimp only [ReturnNineCopy.stepFee,ReturnNineRouted.cost,ReturnNineRoute.cost]
  nlinarith only [copied,square,next]

theorem copy_fee (v : Data) (memory : Fin 8) (n : ℕ) (small : n≤8) :
    ReturnNineCopy.fee v memory n≤(4096+16896*n)*(ReturnNineRoute.width v+1)^2 := by
  induction n with
  | zero=>exact start_fee v
  | succ n ih=>
    have bound : n<8 := by omega
    have slotEq:=ReturnNineCopy.slot_val n bound
    have lastSmall:=field_length v memory (⟨n,by omega⟩ : Fin 9)
    have previousSmall : ReturnNineDest.width
        ((ReturnNineCopy.fields v memory).take n++[(ReturnNineCopy.fields v memory).getD n []])≤ReturnNineRoute.width v := by
      have equal:=ReturnNineCopy.fields_take v memory (ReturnNineCopy.slot n)
      rw [slotEq] at equal
      rw [equal]
      exact (take_width _ _).trans_eq (fields_width v memory)
    have next:=step_fee v (ReturnNineCopy.slot n) ((ReturnNineCopy.fields v memory).take n)
      ((ReturnNineCopy.fields v memory).getD n []) lastSmall previousSmall
    have before:=ih (by omega)
    change ReturnNineCopy.fee v memory n+ReturnNineCopy.stepFee v (ReturnNineCopy.slot n)
      ((ReturnNineCopy.fields v memory).take n) ((ReturnNineCopy.fields v memory).getD n [])≤_
    calc
      _≤(4096+16896*n)*(ReturnNineRoute.width v+1)^2+16896*(ReturnNineRoute.width v+1)^2 := Nat.add_le_add before next
      _=(4096+16896*(n+1))*(ReturnNineRoute.width v+1)^2 := by ring

theorem marshal_fee (v : Data) (memory : Fin 8) :
    ReturnNineMarshal.fee v memory≤262144*(ReturnNineRoute.width v+1)^2 := by
  have copied:=copy_fee v memory 8 (by decide)
  have lastSmall : (ReturnNineStep.output v 7 memory).length≤ReturnNineRoute.width v := field_length v memory 8
  have previousSmall:=(take_width (ReturnNineCopy.fields v memory) 8).trans_eq (fields_width v memory)
  dsimp only [ReturnNineMarshal.fee]
  nlinarith only [copied,lastSmall,previousSmall,Nat.zero_le ((ReturnNineRoute.width v)^2),Nat.zero_le (ReturnNineRoute.width v)]

theorem book_fee (v : Data) : ReturnNineObserved.fee v≤128*(ReturnNineRoute.width v+1)^2 := by
  have total : v.a.length+v.b.length+v.c.length+v.d.length+v.e.length+v.f.length+v.g.length+v.h.length+v.i.length≤
      ReturnNineRoute.width v := by
    simp only [ReturnNineRoute.width,ReturnNineOut.mask,List.length_cons,List.length_tail]
    omega
  dsimp only [ReturnNineObserved.fee]
  nlinarith only [total,Nat.zero_le ((ReturnNineRoute.width v)^2),Nat.zero_le (ReturnNineRoute.width v)]

/-- Uniform resources for the entire single fixed observed nine-copy
producer. The bound uses only the actual nine digit SUM as proof data. -/
theorem fee_le (v : Data) : ReturnNineActual.fee v≤1048576*(ReturnNineRoute.width v+1)^2 := by
  have observed:=book_fee v
  have copied:=marshal_fee v (ReturnNineActual.observed v)
  dsimp only [ReturnNineActual.fee]
  nlinarith only [observed,copied,Nat.zero_le ((ReturnNineRoute.width v)^2),Nat.zero_le (ReturnNineRoute.width v)]

end RootB23.Threshold.ReturnNineBounds
