module
public import Structure.RootB23_Threshold_ReturnNineDest_047

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnNineRouted
open PaperProofs.Common.Native.RationalControllerComputation Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031
open ReturnNineLayout (Data)

/-- The next eight sources after B, in final output order. -/
def index (slot : Fin 8) : Fin 9 := match slot.val with
  | 0=>3 | 1=>4 | 2=>0 | 3=>1 | 4=>5 | 5=>6 | 6=>7 | _=>8

def outEnterCap (slot : Fin 8) : ℕ := ReturnNineOut.cap (index slot)+12

def outCap (slot : Fin 8) : ℕ := outEnterCap slot+ReturnNineDest.skipCap slot.val+1

def outEnter (slot : Fin 8) : Machine (outEnterCap slot) :=
  PSTRTMSeq005.seqMachine (ReturnNineOut.code (index slot)) ReturnNineDest.homeRightCode

def outCode (slot : Fin 8) : Machine (outCap slot) :=
  PSTRTMSeq005.seqMachine (outEnter slot) (ReturnNineDest.skipCode slot.val)

def outPort (slot : Fin 8) : Fin (outCap slot+1) :=
  PSTRTMSeq005.rightLabel (a:=outEnterCap slot) (ReturnNineDest.skipPort slot.val)

def backExitCap (slot : Fin 8) : ℕ := ReturnNineDest.backCap slot.val+12

def backCap (slot : Fin 8) : ℕ := backExitCap slot+ReturnNineBack.cap (index slot)+1

def backExit (slot : Fin 8) : Machine (backExitCap slot) :=
  PSTRTMSeq005.seqMachine (ReturnNineDest.backCode slot.val) ReturnNineDest.homeLeftCode

def backCode (slot : Fin 8) : Machine (backCap slot) :=
  PSTRTMSeq005.seqMachine (backExit slot) (ReturnNineBack.code (index slot))

def backPort (slot : Fin 8) : Fin (backCap slot+1) :=
  PSTRTMSeq005.rightLabel (a:=backExitCap slot) ⟨ReturnNineBack.cap (index slot),Nat.lt_succ_self _⟩

theorem out_le (slot : Fin 8) : outCap slot≤100 := by fin_cases slot <;> decide

theorem back_le (slot : Fin 8) : backCap slot≤100 := by fin_cases slot <;> decide

def route (slot : Fin 8) : RoutedCopy.Route :=
  ⟨padMachine (out_le slot) (outCode slot),padMachine (back_le slot) (backCode slot),
    padLabel (out_le slot) (outPort slot),padLabel (back_le slot) (backPort slot)⟩

def context (v : Data) (slot : Fin 8) (previous : List (List Bool)) : List Bool :=
  ReturnNineRoute.context v (index slot)++false::true::(List.replicate 7 false++ReturnNineDest.core previous)

def finish (v : Data) (slot : Fin 8) (previous : List (List Bool)) (left digits : List Bool) : List Bool :=
  ReturnNineDest.finish (ReturnNineDest.home (ReturnNineRoute.finish v (index slot) left digits)) previous

def cost (v : Data) (previous : List (List Bool)) : ℕ := ReturnNineRoute.cost v+2*ReturnNineDest.width previous+128

/-- Every earlier destination field is actually crossed. The protected
near source bank, destination markers and seven paid prefix zeros remain
in the exact trace; no nearest-blank or supplied gap premise is added. -/
theorem correct (v : Data) (slot : Fin 8) (previous : List (List Bool))
    (lengthEq : previous.length=slot.val+1) :
    RoutedCopy.RouteCorrect (route slot) (context v slot previous) (finish v slot previous) (cost v previous) := by
  refine ⟨?_,?_,?_,?_⟩
  · cases h : ReturnNineRoute.context v (index slot) with
    | nil=>simp only [context,h,List.nil_append,List.headD_cons]
    | cons bit rest=>
      have bitFalse : bit=false := by
        have first:=ReturnNineRoute.context_false v (index slot)
        simpa only [h,List.headD_cons] using first
      subst bit
      simp only [context,h,List.cons_append,List.headD_cons]
  · intro left bit later
    unfold finish
    rw [ReturnNineRoute.finish_cons]
  · intro left digits suffix
    let old:=ReturnNineRoute.finish v (index slot) left digits
    let destination:=ReturnNineDest.core previous++false::suffix
    let saved:=true::(List.replicate 7 false++destination)
    have source:=ReturnNineOut.bounded v (index slot) left digits saved
    rw [←ReturnNineRoute.fieldWord_eq] at source
    have cross:=ReturnNineDest.homeRight_bounded old destination
    have scan:=ReturnNineDest.skip_bounded slot.val previous lengthEq (ReturnNineDest.home old) suffix
    have actual:=(source.seq cross).seq scan
    have padded:=bounded_pad (out_le slot) actual
    simpa only [route,outCode,outEnter,outCap,outEnterCap,outPort,context,finish,
      RoutedCopy.fieldWord,ReturnNineRoute.fieldWord_eq,cost,old,destination,saved,
      List.append_assoc,List.cons_append,List.nil_append]
      using padded.mono (by have bound:=slot.isLt;have sourceFee:=ReturnNineRoute.out_fee v (index slot) digits;dsimp only [cost];omega :
        ReturnNineOut.fee v (index slot) digits+12+(2*ReturnNineDest.width previous+8*(slot.val+1))≤
          2*digits.length+cost v previous)

  · intro archive digits suffix
    let old:=ReturnNineRoute.finish v (index slot) (false::archive) digits
    let destination:=ReturnNineDest.core previous++false::suffix
    let saved:=true::(List.replicate 7 false++destination)
    have scan:=ReturnNineDest.back_bounded slot.val previous lengthEq (ReturnNineDest.home old).tail suffix
    have cross:=ReturnNineDest.homeLeft_bounded old destination
    have source:=ReturnNineBack.bounded (ReturnNineOut.mask v) (index slot) archive digits saved
    rw [←ReturnNineRoute.fieldWord_eq] at source
    have actual:=(scan.seq cross).seq source
    have padded:=bounded_pad (back_le slot) actual
    simpa only [route,backCode,backExit,backCap,backExitCap,backPort,context,finish,
      RoutedCopy.fieldWord,cost,old,destination,saved,ReturnNineDest.home,List.replicate_succ,List.replicate_zero,List.tail_cons,
      List.append_assoc,List.cons_append,List.nil_append]
      using padded.mono (by have bound:=slot.isLt;have sourceFee:=ReturnNineRoute.back_fee v (index slot) digits;dsimp only [cost];omega :
        (2*ReturnNineDest.width previous+8*(slot.val+1))+12+ReturnNineBack.fee (ReturnNineOut.mask v) (index slot) digits≤
          2*digits.length+cost v previous)

end RootB23.Threshold.ReturnNineRouted
