module

public import Paid.PDROC_BitVM_Kernel_Numeric_001
public import Structure.PA17_TM_RatArithmetic_Sub_016f
public import Structure.PA17_TM_Division_Full_012c

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.Numeric

open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation PDROC.BitVM.Native

def subMachine : Unit → TM2.Stmt Alphabet Unit (BoolOnStacks.Store 596) :=
  workstackMachine work PA17TMRatArithmeticSub016.nativeSubMachine

/-- The actual saturating subtraction algorithm includes underflow; the
operator does not inspect unbounded values in finite control. -/
theorem sub_runs (a b : ℕ)
    (before : TM2.Cfg Alphabet Unit (BoolOnStacks.Store 596))
    (active : (Lift.cfg work before).l=some ())
    (represented : BoolOnStacks.representedState (Lift.cfg work before)=
      TM0.init (encodeNat a++encodeNat b)) :
    ∃ (run : List (TM2.Cfg Alphabet Unit (BoolOnStacks.Store 596)))
      (lastState : TM2.Cfg Alphabet Unit (BoolOnStacks.Store 596)),
      run.head?=some before ∧ run.IsChain (fun x y=>TM2.step subMachine x=some y) ∧
      run.getLast?=some lastState ∧ TM2.step subMachine lastState=none ∧
      (BoolOnStacks.representedState (Lift.cfg work lastState)).Tape=Tape.mk₁ (encodeNat (a-b)) ∧
      run.length≤4096*(natBits a+natBits b+1)^2+1 ∧
      ∀ other,(∀ index,other≠work index)→lastState.stk other=before.stk other := by
  have old := PA17TMRatArithmeticSub016.native_runs a b
  obtain ⟨run,lastState,head,chain,last,halt,resultEq,length,frame⟩ :=
    actual_workstack_traceFrom work PA17TMRatArithmeticSub016.nativeSubMachine before
      (PA17TMRatArithmeticSub016.nativeTrace a b)
      (TM0.init (encodeNat a++encodeNat b)) (PA17TMRatArithmeticSub016.nativeFinal a b)
      active represented old.1 old.2.1 old.2.2.1 old.2.2.2.1
  refine ⟨run,lastState,head,chain,last,halt,?_,?_,frame⟩
  · exact (congrArg (fun state : TM0.Cfg Bool (Fin (596+1))=>state.Tape) resultEq).trans
      (PA17TMRatArithmeticSub016.native_final_tape a b)
  · rw [length]
    exact Nat.add_le_add_right (PA17TMRatArithmeticSub016.native_length_le a b) 1

theorem sub_supports : TM2.Supports subMachine (Finset.univ : Finset Unit) :=
  workstack_supports work PA17TMRatArithmeticSub016.nativeSubMachine

def divMachine : Unit → TM2.Stmt Alphabet Unit (BoolOnStacks.Store 1136) :=
  workstackMachine work PA17TMDivisionFull012.quotientMachine

/-- Real binary long division on the same two native work stacks. The
frozen all-input theorem already includes divisor zero, parse, cleanup and
HALT. Its actual right result is sufficient for the physical Nat writer. -/
theorem div_runs (a b : ℕ)
    (before : TM2.Cfg Alphabet Unit (BoolOnStacks.Store 1136))
    (active : (Lift.cfg work before).l=some ())
    (represented : BoolOnStacks.representedState (Lift.cfg work before)=
      TM0.init (encodeNat a++encodeNat b)) :
    ∃ (run : List (TM2.Cfg Alphabet Unit (BoolOnStacks.Store 1136)))
      (lastState : TM2.Cfg Alphabet Unit (BoolOnStacks.Store 1136)),
      run.head?=some before ∧ run.IsChain (fun x y=>TM2.step divMachine x=some y) ∧
      run.getLast?=some lastState ∧ TM2.step divMachine lastState=none ∧
      (BoolOnStacks.representedState (Lift.cfg work lastState)).Tape.right₀=
        ListBlank.mk (encodeNat (a/b)) ∧
      run.length≤32768*(natBits a+natBits b+1)^2+1 ∧
      ∀ other,(∀ index,other≠work index)→lastState.stk other=before.stk other := by
  obtain ⟨oldRun,oldFinal,old,output,bound,_space⟩ :=
    (PA17TMDivisionFull012.quotient_remainder_computes a b).1
  obtain ⟨run,lastState,head,chain,last,halt,resultEq,length,frame⟩ :=
    actual_workstack_traceFrom work PA17TMDivisionFull012.quotientMachine before oldRun
      (TM0.init (encodeNat a++encodeNat b)) oldFinal
      active represented old.1 old.2.1 old.2.2.1 old.2.2.2.1
  refine ⟨run,lastState,head,chain,last,halt,?_,?_,frame⟩
  · exact (congrArg (fun state : TM0.Cfg Bool (Fin (1136+1))=>state.Tape.right₀) resultEq).trans output
  · rw [length]
    exact Nat.add_le_add_right bound 1

theorem div_supports : TM2.Supports divMachine (Finset.univ : Finset Unit) :=
  workstack_supports work PA17TMDivisionFull012.quotientMachine

def modMachine : Unit → TM2.Stmt Alphabet Unit (BoolOnStacks.Store 1113) :=
  workstackMachine work PA17TMDivisionFull012.remainderMachine

theorem mod_runs (a b : ℕ)
    (before : TM2.Cfg Alphabet Unit (BoolOnStacks.Store 1113))
    (active : (Lift.cfg work before).l=some ())
    (represented : BoolOnStacks.representedState (Lift.cfg work before)=
      TM0.init (encodeNat a++encodeNat b)) :
    ∃ (run : List (TM2.Cfg Alphabet Unit (BoolOnStacks.Store 1113)))
      (lastState : TM2.Cfg Alphabet Unit (BoolOnStacks.Store 1113)),
      run.head?=some before ∧ run.IsChain (fun x y=>TM2.step modMachine x=some y) ∧
      run.getLast?=some lastState ∧ TM2.step modMachine lastState=none ∧
      (BoolOnStacks.representedState (Lift.cfg work lastState)).Tape.right₀=
        ListBlank.mk (encodeNat (a%b)) ∧
      run.length≤32768*(natBits a+natBits b+1)^2+1 ∧
      ∀ other,(∀ index,other≠work index)→lastState.stk other=before.stk other := by
  obtain ⟨oldRun,oldFinal,old,output,bound,_space⟩ :=
    (PA17TMDivisionFull012.quotient_remainder_computes a b).2
  obtain ⟨run,lastState,head,chain,last,halt,resultEq,length,frame⟩ :=
    actual_workstack_traceFrom work PA17TMDivisionFull012.remainderMachine before oldRun
      (TM0.init (encodeNat a++encodeNat b)) oldFinal
      active represented old.1 old.2.1 old.2.2.1 old.2.2.2.1
  refine ⟨run,lastState,head,chain,last,halt,?_,?_,frame⟩
  · exact (congrArg (fun state : TM0.Cfg Bool (Fin (1113+1))=>state.Tape.right₀) resultEq).trans output
  · rw [length]
    exact Nat.add_le_add_right bound 1

theorem mod_supports : TM2.Supports modMachine (Finset.univ : Finset Unit) :=
  workstack_supports work PA17TMDivisionFull012.remainderMachine

end PDROC.BitVM.Kernel.Numeric
