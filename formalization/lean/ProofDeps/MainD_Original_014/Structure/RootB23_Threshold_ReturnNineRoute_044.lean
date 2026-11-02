module
public import Structure.RootB23_Threshold_ReturnNineOut_043

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnNineRoute
open PaperProofs.Common.Native.RationalControllerComputation Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031
open ReturnNineLayout (Data)

def context (v : Data) (index : Fin 9) : List Bool := (ReturnNineBack.after (ReturnNineOut.mask v) index).tail

def finish (v : Data) (index : Fin 9) (left digits : List Bool) : List Bool :=
  ReturnNineBack.finish (ReturnNineOut.mask v) index left digits

def width (v : Data) : ℕ :=
  let m:=ReturnNineOut.mask v
  m.a.length+m.b.length+m.c.length+m.d.length+m.e.length+m.f.length+m.g.length+m.h.length+m.i.length

def cost (v : Data) : ℕ := 2*width v+128

theorem after_false (v : Data) (index : Fin 9) :
    ReturnNineBack.after (ReturnNineOut.mask v) index=false::(ReturnNineBack.after (ReturnNineOut.mask v) index).tail := by
  fin_cases index <;> rfl

theorem context_false (v : Data) (index : Fin 9) : (context v index).headD false=false := by
  fin_cases index <;> rfl

theorem fieldWord_eq (v : Data) (index : Fin 9) (digits suffix : List Bool) :
    RoutedCopy.fieldWord (context v index) digits suffix=
      PSTRTMIncrement009.blocks digits++(ReturnNineBack.after (ReturnNineOut.mask v) index++false::suffix) := by
  have shape:=congrArg (fun word=>PSTRTMIncrement009.blocks digits++(word++false::suffix)) (after_false v index)
  simpa only [RoutedCopy.fieldWord,context,List.cons_append] using shape.symm

theorem finish_cons (v : Data) (index : Fin 9) (left later : List Bool) (bit : Bool) :
    finish v index (true::bit::left) later=finish v index left (bit::later) := by
  fin_cases index <;>
    simp [finish,ReturnNineBack.finish,ReturnNineBack.finish0,ReturnNineBack.finish1,ReturnNineBack.finish2,
      ReturnNineBack.finish3,ReturnNineBack.finish4,ReturnNineBack.finish5,ReturnNineBack.finish6,
      ReturnNineBack.finish7,ReturnNineBack.finish8,ReturnNineLayout.gap13,PSTRTMRawNat010.leftBlocks,
      List.reverse_cons,List.flatMap_append,List.append_assoc]

theorem cap_out (index : Fin 9) : ReturnNineOut.cap index≤100 := by fin_cases index <;> decide

theorem cap_back (index : Fin 9) : ReturnNineBack.cap index≤100 := by fin_cases index <;> decide

def route (index : Fin 9) : RoutedCopy.Route :=
  ⟨padMachine (cap_out index) (ReturnNineOut.code index),
    padMachine (cap_back index) (ReturnNineBack.code index),
    padLabel (cap_out index) ⟨ReturnNineOut.cap index,Nat.lt_succ_self _⟩,
    padLabel (cap_back index) ⟨ReturnNineBack.cap index,Nat.lt_succ_self _⟩⟩

theorem out_fee (v : Data) (index : Fin 9) (digits : List Bool) :
    ReturnNineOut.fee v index digits≤2*digits.length+cost v := by
  fin_cases index <;>
    simp only [ReturnNineOut.fee,ReturnNineOut.fee0,ReturnNineOut.fee1,ReturnNineOut.fee2,
      ReturnNineOut.fee3,ReturnNineOut.fee4,ReturnNineOut.fee5,ReturnNineOut.fee6,ReturnNineOut.fee7,
      ReturnNineOut.fee8,cost,width] <;> omega

theorem back_fee (v : Data) (index : Fin 9) (digits : List Bool) :
    ReturnNineBack.fee (ReturnNineOut.mask v) index digits≤2*digits.length+cost v := by
  fin_cases index <;>
    simp only [ReturnNineBack.fee,ReturnNineBack.fee0,ReturnNineBack.fee1,ReturnNineBack.fee2,
      ReturnNineBack.fee3,ReturnNineBack.fee4,ReturnNineBack.fee5,ReturnNineBack.fee6,ReturnNineBack.fee7,
      ReturnNineBack.fee8,cost,width] <;> omega

/-- All nine fixed source routes bind the already frozen copy kernel.
The source's temporary FALSE flag remains the actual return target. -/
theorem correct (v : Data) (index : Fin 9) :
    RoutedCopy.RouteCorrect (route index) (context v index) (finish v index) (cost v) := by
  refine ⟨context_false v index,(fun left bit later=>finish_cons v index left later bit),?_,?_⟩
  · intro left digits suffix
    have actual:=ReturnNineOut.bounded v index left digits suffix
    rw [←fieldWord_eq] at actual
    exact (bounded_pad (cap_out index) actual).mono (out_fee v index digits)
  · intro archive digits suffix
    have actual:=ReturnNineBack.bounded (ReturnNineOut.mask v) index archive digits suffix
    rw [←fieldWord_eq] at actual
    exact (bounded_pad (cap_back index) actual).mono (back_fee v index digits)

end RootB23.Threshold.ReturnNineRoute
