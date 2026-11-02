module

public import Paid.PDROC_BitVM_Native_From_007
public import Common.PSTR_TM_NativeAdd_053
public import Common.PSTR_TM_NativeLe_060
public import Common.PSTR_TM_NativeMul_112
public import Common.ROOT_TM_GCD_Native_037

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.Numeric

open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation PDROC.BitVM.Native

abbrev Stack := Fin 32
abbrev Alphabet (_ : Stack) := Bool

def work : Fin 2 ↪ Stack where
  toFun := fun index=>if index=0 then 0 else 24
  inj' := by intro a b same;fin_cases a <;> fin_cases b <;> simp at same ⊢

/- These four fixed native machines are already frozen real binary
algorithms. Operands/results below are proof descriptions of actual Bool
work tapes. No Nat/Rat is read by a host function in a transition. -/

def addMachine : Unit → TM2.Stmt Alphabet Unit (BoolOnStacks.Store 469) :=
  workstackMachine work PSTRTMNativeAdd053.nativeAddMachine

/-- Actual fixed add path on caller work stacks, including real HALT,
whole canonical result Tape, exact old cost+1 and all outside-stack frame.
The operand tape must be produced by real marshalling, not supplied raw. -/
theorem add_runs (a b : ℕ)
    (before : TM2.Cfg Alphabet Unit (BoolOnStacks.Store 469))
    (active : (Lift.cfg work before).l=some ())
    (represented : BoolOnStacks.representedState (Lift.cfg work before)=
      TM0.init (encodeNat a++encodeNat b)) :
    ∃ (run : List (TM2.Cfg Alphabet Unit (BoolOnStacks.Store 469)))
      (lastState : TM2.Cfg Alphabet Unit (BoolOnStacks.Store 469)),
      run.head?=some before ∧ run.IsChain (fun x y=>TM2.step addMachine x=some y) ∧
      run.getLast?=some lastState ∧ TM2.step addMachine lastState=none ∧
      (BoolOnStacks.representedState (Lift.cfg work lastState)).Tape=Tape.mk₁ (encodeNat (a+b)) ∧
      run.length≤4096*(natBits a+natBits b+1)^2+1 ∧
      ∀ other,(∀ index,other≠work index)→lastState.stk other=before.stk other := by
  have old := PSTRTMNativeAdd053.native_runs a b
  obtain ⟨run,lastState,head,chain,last,halt,resultEq,length,frame⟩ :=
    actual_workstack_traceFrom work PSTRTMNativeAdd053.nativeAddMachine before (PSTRTMNativeAdd053.nativeTrace a b)
      (TM0.init (encodeNat a++encodeNat b)) (PSTRTMNativeAdd053.nativeFinal a b)
      active represented old.1 old.2.1 old.2.2.1 old.2.2.2.1
  refine ⟨run,lastState,head,chain,last,halt,?_,?_,frame⟩
  · exact (congrArg (fun state : TM0.Cfg Bool (Fin (469+1))=>state.Tape) resultEq).trans
      (PSTRTMNativeAdd053.native_final_tape_canonical a b)
  · rw [length]
    exact Nat.add_le_add_right (PSTRTMNativeAdd053.native_length_le a b) 1

theorem add_supports : TM2.Supports addMachine (Finset.univ : Finset Unit) :=
  workstack_supports work PSTRTMNativeAdd053.nativeAddMachine

def leMachine : Unit → TM2.Stmt Alphabet Unit (BoolOnStacks.Store 397) :=
  workstackMachine work PSTRTMNativeLe060.nativeLeMachine

/-- Actual fixed le path on caller work stacks, including real HALT,
whole canonical result Tape, exact old cost+1 and all outside-stack frame.
The operand tape must be produced by real marshalling, not supplied raw. -/
theorem le_runs (a b : ℕ)
    (before : TM2.Cfg Alphabet Unit (BoolOnStacks.Store 397))
    (active : (Lift.cfg work before).l=some ())
    (represented : BoolOnStacks.representedState (Lift.cfg work before)=
      TM0.init (encodeNat a++encodeNat b)) :
    ∃ (run : List (TM2.Cfg Alphabet Unit (BoolOnStacks.Store 397)))
      (lastState : TM2.Cfg Alphabet Unit (BoolOnStacks.Store 397)),
      run.head?=some before ∧ run.IsChain (fun x y=>TM2.step leMachine x=some y) ∧
      run.getLast?=some lastState ∧ TM2.step leMachine lastState=none ∧
      (BoolOnStacks.representedState (Lift.cfg work lastState)).Tape=Tape.mk₁ (encodeNat (if decide (a≤b) then 1 else 0)) ∧
      run.length≤4096*(natBits a+natBits b+1)^2+1 ∧
      ∀ other,(∀ index,other≠work index)→lastState.stk other=before.stk other := by
  have old := PSTRTMNativeLe060.native_runs a b
  obtain ⟨run,lastState,head,chain,last,halt,resultEq,length,frame⟩ :=
    actual_workstack_traceFrom work PSTRTMNativeLe060.nativeLeMachine before (PSTRTMNativeLe060.nativeTrace a b)
      (TM0.init (encodeNat a++encodeNat b)) (PSTRTMNativeLe060.nativeFinal a b)
      active represented old.1 old.2.1 old.2.2.1 old.2.2.2.1
  refine ⟨run,lastState,head,chain,last,halt,?_,?_,frame⟩
  · exact (congrArg (fun state : TM0.Cfg Bool (Fin (397+1))=>state.Tape) resultEq).trans
      (PSTRTMNativeLe060.native_final_tape_canonical a b)
  · rw [length]
    exact Nat.add_le_add_right (PSTRTMNativeLe060.native_length_le a b) 1

theorem le_supports : TM2.Supports leMachine (Finset.univ : Finset Unit) :=
  workstack_supports work PSTRTMNativeLe060.nativeLeMachine

def mulMachine : Unit → TM2.Stmt Alphabet Unit (BoolOnStacks.Store 982) :=
  workstackMachine work PSTRTMNativeMul112.nativeMulMachine

/-- Actual fixed mul path on caller work stacks, including real HALT,
whole canonical result Tape, exact old cost+1 and all outside-stack frame.
The operand tape must be produced by real marshalling, not supplied raw. -/
theorem mul_runs (a b : ℕ)
    (before : TM2.Cfg Alphabet Unit (BoolOnStacks.Store 982))
    (active : (Lift.cfg work before).l=some ())
    (represented : BoolOnStacks.representedState (Lift.cfg work before)=
      TM0.init (encodeNat a++encodeNat b)) :
    ∃ (run : List (TM2.Cfg Alphabet Unit (BoolOnStacks.Store 982)))
      (lastState : TM2.Cfg Alphabet Unit (BoolOnStacks.Store 982)),
      run.head?=some before ∧ run.IsChain (fun x y=>TM2.step mulMachine x=some y) ∧
      run.getLast?=some lastState ∧ TM2.step mulMachine lastState=none ∧
      (BoolOnStacks.representedState (Lift.cfg work lastState)).Tape=Tape.mk₁ (encodeNat (a*b)) ∧
      run.length≤16384*(natBits a+natBits b+1)^2+1 ∧
      ∀ other,(∀ index,other≠work index)→lastState.stk other=before.stk other := by
  have old := PSTRTMNativeMul112.native_runs a b
  obtain ⟨run,lastState,head,chain,last,halt,resultEq,length,frame⟩ :=
    actual_workstack_traceFrom work PSTRTMNativeMul112.nativeMulMachine before (PSTRTMNativeMul112.nativeTrace a b)
      (TM0.init (encodeNat a++encodeNat b)) (PSTRTMNativeMul112.nativeFinal a b)
      active represented old.1 old.2.1 old.2.2.1 old.2.2.2.1
  refine ⟨run,lastState,head,chain,last,halt,?_,?_,frame⟩
  · exact (congrArg (fun state : TM0.Cfg Bool (Fin (982+1))=>state.Tape) resultEq).trans
      (PSTRTMNativeMul112.native_final_tape_canonical a b)
  · rw [length]
    exact Nat.add_le_add_right (PSTRTMNativeMul112.native_length_le a b) 1

theorem mul_supports : TM2.Supports mulMachine (Finset.univ : Finset Unit) :=
  workstack_supports work PSTRTMNativeMul112.nativeMulMachine

def gcdMachine : Unit → TM2.Stmt Alphabet Unit (BoolOnStacks.Store 3564) :=
  workstackMachine work ROOTTMGCDDispatch018.nativeGcdMachine

/-- Actual fixed gcd path on caller work stacks, including real HALT,
whole canonical result Tape, exact old cost+1 and all outside-stack frame.
The operand tape must be produced by real marshalling, not supplied raw. -/
theorem gcd_runs (a b : ℕ)
    (before : TM2.Cfg Alphabet Unit (BoolOnStacks.Store 3564))
    (active : (Lift.cfg work before).l=some ())
    (represented : BoolOnStacks.representedState (Lift.cfg work before)=
      TM0.init (encodeNat a++encodeNat b)) :
    ∃ (run : List (TM2.Cfg Alphabet Unit (BoolOnStacks.Store 3564)))
      (lastState : TM2.Cfg Alphabet Unit (BoolOnStacks.Store 3564)),
      run.head?=some before ∧ run.IsChain (fun x y=>TM2.step gcdMachine x=some y) ∧
      run.getLast?=some lastState ∧ TM2.step gcdMachine lastState=none ∧
      (BoolOnStacks.representedState (Lift.cfg work lastState)).Tape=Tape.mk₁ (encodeNat (Nat.gcd a b)) ∧
      run.length≤16384*(natBits a+natBits b+1)^2+1 ∧
      ∀ other,(∀ index,other≠work index)→lastState.stk other=before.stk other := by
  have old := ROOTTMGCDNative037.native_runs a b
  obtain ⟨run,lastState,head,chain,last,halt,resultEq,length,frame⟩ :=
    actual_workstack_traceFrom work ROOTTMGCDDispatch018.nativeGcdMachine before (ROOTTMGCDNative037.nativeTrace a b)
      (TM0.init (encodeNat a++encodeNat b)) (ROOTTMGCDNative037.nativeFinal a b)
      active represented old.1 old.2.1 old.2.2.1 old.2.2.2.1
  refine ⟨run,lastState,head,chain,last,halt,?_,?_,frame⟩
  · exact (congrArg (fun state : TM0.Cfg Bool (Fin (3564+1))=>state.Tape) resultEq).trans
      (ROOTTMGCDNative037.native_final_tape a b)
  · rw [length]
    exact Nat.add_le_add_right (ROOTTMGCDNative037.native_length_le a b) 1

theorem gcd_supports : TM2.Supports gcdMachine (Finset.univ : Finset Unit) :=
  workstack_supports work ROOTTMGCDDispatch018.nativeGcdMachine

end PDROC.BitVM.Kernel.Numeric
