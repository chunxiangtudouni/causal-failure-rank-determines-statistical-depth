module

public import B23_4_RatWordPrep_SeqCmp_HeaderRun_051

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.NatField

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM PSTRSymbolicNaturalExport PSTRTMRawNat010

variable {C : Type*}

def packet (number : Nat) (tail : List Bool) : List Bool :=
  leftBlocks (PSTRTMNatValue017.rawPayload number)++false::false::tail

theorem actual_current (memory : Store C) (bank : RatInput.Stack → List Bool) (number : Nat)
    (physical : ∃ left,bank 1=false::(leftBlocks (PSTRTMNatValue017.rawPayload number).reverse++false::left)) :
    ∃ (run : List (State C)) (final : State C),
      run.head?=some (⟨some 0,memory,bank⟩ : State C) ∧
      run.IsChain (fun before after => TM2.step (program .halt) before=some after) ∧
      run.getLast?=some final ∧ final.l=some 4 ∧ final.var.1=memory.1 ∧
      final.stk=Function.update bank 15 (packet number (bank 15)) ∧
      run.length=3*(PSTRTMNatValue017.rawPayload number).length+6 := by
  rcases memory with ⟨context,bit,flag,mode⟩
  obtain ⟨left,shape⟩:=physical
  obtain ⟨run,resultBit,first,chain,last,count⟩:=actual context bit flag mode
    (PSTRTMNatValue017.rawPayload number).reverse left (bank 7) (bank 15) bank
  let final:=state (some 4) (context,(resultBit,true,mode)) (bank 1) (bank 7) (packet number (bank 15)) bank
  have start : state (some 0) (context,(bit,flag,mode))
      (false::(leftBlocks (PSTRTMNatValue017.rawPayload number).reverse++false::left)) (bank 7) (bank 15) bank=
      (⟨some 0,(context,(bit,flag,mode)),bank⟩ : State C) := by
    rw [←shape]
    exact state_rebuild _ _ bank
  refine ⟨run,final,first.trans (congrArg some start),chain,?_,rfl,rfl,bank_target bank _,?_⟩
  · simpa only [final,packet,List.reverse_reverse,shape] using last
  · simpa only [List.length_reverse] using count

end B23_4_RatWordPrep.NatField
