module

public import Paid.PDROC_BitVM_Kernel_Internal_018
public import Paid.PDROC_BitVM_Kernel_NatInstruction_013
public import Paid.PDROC_BitVM_Common_Occupancy_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Kernel.InternalInstruction

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal
open PaperProofs.Common.Native.RationalControllerComputation

open PDROC.BitVM.Kernel.NatInstruction (dataSize dataSize_each computeBudget)

def computePushCap (operation : Internal.Kind) (left right : Register) : ℕ :=
  PDROC.BitVM.Common.sourcePushCap (Internal.program operation left right) Finset.univ

/-- A whole computed internal native result and its physical workspace allowance
come from the SAME actual opcode path. This pays for FALSE padding before
the real Nat writer, instead of assuming a canonical empty work tape. -/
theorem compute_resources (operation : Internal.Kind)
    (logical : PaperProofs.Paid.Computation.State) (left right : Register) (a b : ℕ)
    (contents : Stack → List Bool) (store : Option Bool)
    (represented : ∀ reg,contents (registerSlot reg)=encodeCellBits (logical.register reg))
    (leftNat : logical.register left=.natural a) (rightNat : logical.register right=.natural b)
    (emptyRight : contents 0=[]) (emptyLeft : contents 24=[]) :
    ∃ (run : List (Internal.State operation)) (lastState : Internal.State operation),
      run.head?=some (Internal.before operation contents store) ∧ 
      run.IsChain (fun x y=>TM2.step (Internal.program operation left right) x=some y) ∧ 
      run.getLast?=some lastState ∧ TM2.step (Internal.program operation left right) lastState=none ∧ 
      RegistersRepresent logical lastState ∧ 
      ListBlank.mk (lastState.stk 0)=ListBlank.mk (encodeNat (Internal.value operation a b)) ∧ 
      run.length ≤ computeBudget a b ∧ 
      (∀ state ∈ run,∀ role,(state.stk role).length ≤ 
        dataSize contents+computePushCap operation left right*computeBudget a b) ∧ 
      ∀ other,(∀ index,other ≠ NatMarshalGlobal.embedding left index) → 
        (∀ index,other ≠ NatMarshalGlobal.embedding right index) → 
        (∀ index,other ≠ Numeric.work index) → lastState.stk other=contents other := by
  obtain ⟨run,lastState,head,chain,last,halt,regs,result,time,frame⟩ :=
    Internal.compute_runs operation logical left right a b contents store represented leftNat rightNat emptyRight emptyLeft
  refine ⟨run,lastState,head,chain,last,halt,regs,result,time,?_,frame⟩
  cases run with
  | nil => simp only [List.head?_nil,reduceCtorEq] at head
  | cons start rest =>
    have first : start=Internal.before operation contents store := Option.some.inj head
    have initial : ∀ role,(start.stk role).length ≤ dataSize contents := by
      rw [first]
      exact dataSize_each contents
    have supported : start.l ∈ Finset.insertNone (Finset.univ : Finset Internal.Label) := by
      rw [first]
      exact Finset.some_mem_insertNone.mpr (Finset.mem_univ _)
    have bounded := PDROC.BitVM.Common.source_path_occupancy (Internal.program operation left right)
      Finset.univ (Internal.supports operation left right) start rest (dataSize contents) supported initial chain
    have restBound : rest.length ≤ computeBudget a b := by
      change rest.length+1 ≤ computeBudget a b at time
      omega
    intro state member role
    exact ((bounded state member).2 role).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ restBound) _)

end PDROC.BitVM.Kernel.InternalInstruction
