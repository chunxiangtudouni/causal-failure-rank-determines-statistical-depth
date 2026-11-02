module

public import RootB234_PrepEntry_RawNative_021
public import RootB234_PrepBudgetArchive_Caller005

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.BudgetField

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM PSTRSymbolicLaneScan PSTRSymbolicLaneArchive PA17TMRatArithmeticParse002
open RootB234.PrepBudgetArchive
open scoped BigOperators

variable {C : Type*}

theorem occupied_eq (bank : RatInput.Stack → List Bool) :
    RatInput.occupied bank=VirtualReturn.occupiedSlots bank := by
  simp [RatInput.occupied,VirtualReturn.occupiedSlots,Fin.sum_univ_succ,Fin.succ]
  omega

/-- Internal exact current-state consumer. All digits, sign and the prior
Datum marker come from RawNative's actual finite prefix, not caller inputs. -/
theorem actual_current (caller : Statement C) (memory : Store C) (bank : Stack → List Bool) (budget : Rat)
    (physical : ∃ (boundary : Bool) (left : List Bool),bank 1=Raw.budgetPairBits budget++boundary::true::left) :
    ∃ (trace : List (State C)) (final : State C),
      trace.head?=some (⟨some 0,memory,bank⟩ : State C) ∧
      trace.IsChain (fun a b => TM2.step (program caller) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some 4 ∧ final.var.1=memory.1 ∧
      final.stk 15=RatInput.Encoder.packet budget (bank 15) ∧
      (∀ slot,slot≠1→slot≠15→final.stk slot=bank slot) ∧
      trace.length≤RatInput.occupied bank+7 := by
  rcases memory with ⟨context,bit,flag,pending⟩
  obtain ⟨boundary,left,shape⟩:=physical
  cases denShape : denominatorDigits budget with
  | nil => exact False.elim (PSTRSymbolicLaneArchive.rawPayload_nonempty budget.den denShape)
  | cons firstDen laterDen =>
    cases numShape : (numeratorDigits budget).reverse with
    | nil =>
      have empty:=congrArg List.reverse numShape
      simp only [List.reverse_reverse,List.reverse_nil] at empty
      exact False.elim (PSTRSymbolicLaneArchive.rawPayload_nonempty budget.num.natAbs empty)
    | cons near older =>
      have numEq : (near::older).reverse=numeratorDigits budget := by
        have reversed:=congrArg List.reverse numShape
        simpa only [List.reverse_reverse] using reversed.symm
      let later:=laterDen.reverse
      let rawInput:=(navigationCells (rationalPairs (sign budget) (near::older).reverse firstDen later.reverse)).reverse++boundary::true::left
      have rawShape : rawInput=bank 1 := by
        dsimp only [rawInput,later]
        rw [numEq,List.reverse_reverse]
        simpa only [Raw.budgetPairBits,datumPairs,denShape] using shape.symm
      obtain ⟨trace,first,chain,last,_traceEq,time,_sum⟩:=Public.actual_paired caller bank context bit flag pending
        later firstDen near older (sign budget) boundary left (bank 15)
      have rebuild : RootB234.PrepBudgetArchive.bank bank rawInput (bank 15)=bank := by
        rw [rawShape]
        funext slot
        fin_cases slot <;> rfl
      have initial : state bank 0 context bit flag pending rawInput (bank 15)=
          (⟨some 0,(context,bit,flag,pending),bank⟩ : State C) := by
        change (⟨some 0,(context,bit,flag,pending),_⟩ : State C)=_
        rw [rebuild]
      have packet : PSTRSymbolicRatExport.packet (sign budget) (near::older).reverse
          (firstDen::later.reverse) (bank 15)=RatInput.Encoder.packet budget (bank 15) := by
        dsimp only [later]
        rw [numEq,List.reverse_reverse,←denShape]
        rfl
      let final:=state bank 4 context boundary true (sign budget) (boundary::true::left)
        (RatInput.Encoder.packet budget (bank 15))
      have last' : trace.getLast?=some final := by simpa only [packet] using last
      have scaleEq : scale bank later firstDen near older (sign budget) boundary left (bank 15)=RatInput.occupied bank+7 := by
        change (∑ slot : Stack,(RootB234.PrepBudgetArchive.bank bank
          (true::true::denSource later firstDen near (sign budget) boundary older left) (bank 15) slot).length)+7=_
        rw [←paired_prefix later firstDen near older (sign budget) boundary left]
        change (∑ slot : Stack,(RootB234.PrepBudgetArchive.bank bank rawInput (bank 15) slot).length)+7=_
        rw [rebuild]
        rfl
      refine ⟨trace,final,first.trans (congrArg some initial),chain,last',rfl,rfl,rfl,?_,time.trans_eq scaleEq⟩
      intro slot n1 n15
      simp only [final,state,RootB234.PrepBudgetArchive.bank,n1,n15,ite_false]

end RootB234.PrepEntry.BudgetField
