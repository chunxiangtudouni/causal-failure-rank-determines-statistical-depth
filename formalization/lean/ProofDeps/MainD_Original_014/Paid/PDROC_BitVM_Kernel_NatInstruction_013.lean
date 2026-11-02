module

public import Paid.PDROC_BitVM_Kernel_NatOp_005
public import Paid.PDROC_BitVM_Common_Occupancy_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Kernel.NatInstruction

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal
open PaperProofs.Common.Native.RationalControllerComputation

def after (logical : PaperProofs.Paid.Computation.State) (target : Register) (result : ℕ) :=
  ({logical with pc:=logical.pc+1}).set target (.natural result)

theorem execute (input : List Cell) (logical : PaperProofs.Paid.Computation.State)
    (operation : PaperProofs.Paid.Computation.NatOp) (target left right : Register) (a b result : ℕ)
    (leftNat : logical.register left=.natural a) (rightNat : logical.register right=.natural b)
    (success : operation.eval a b=some result) :
    Instruction.execute input (.natOp operation target left right) logical=some (after logical target result) := by
  simp [Instruction.execute,leftNat,rightNat,Cell.nat?,success,after]

theorem write_represents {Λ σ : Type*} (logical : PaperProofs.Paid.Computation.State)
    (target : Register) (result : ℕ) (before final : TM2.Cfg Alphabet Λ σ)
    (represented : RegistersRepresent logical before)
    (written : final.stk (registerSlot target)=encodeCellBits (.natural result))
    (frame : ∀ reg,reg ≠ target → final.stk (registerSlot reg)=before.stk (registerSlot reg)) :
    RegistersRepresent (after logical target result) final := by
  intro reg
  by_cases same : reg=target
  · subst reg
    simpa only [after,PaperProofs.Paid.Computation.State.set,Function.update_self] using written
  · rw [frame reg same,represented reg]
    simp only [after,PaperProofs.Paid.Computation.State.set,Function.update_of_ne same]

def dataSize (contents : Stack → List Bool) : ℕ := ∑ role : Stack,(contents role).length

theorem dataSize_each (contents : Stack → List Bool) (role : Stack) : (contents role).length ≤ dataSize contents :=
  Finset.single_le_sum (s := (Finset.univ : Finset Stack)) (f := fun index : Stack=>(contents index).length)
    (a := role) (fun index _=>Nat.zero_le ((contents index).length)) (Finset.mem_univ role)

def computeBudget (a b : ℕ) : ℕ :=
  2*(encodeNatBits a).length+2*(encodeNatBits b).length+32768*(natBits a+natBits b+1)^2+12

def computePushCap (operation : PaperProofs.Paid.Computation.NatOp) (left right : Register) : ℕ :=
  PDROC.BitVM.Common.sourcePushCap (NatOp.program operation left right) Finset.univ

/-- A whole computed native result and its physical workspace allowance
come from the SAME actual opcode path. This pays for FALSE padding before
the real Nat writer, instead of assuming a canonical empty work tape. -/
theorem compute_resources (operation : PaperProofs.Paid.Computation.NatOp)
    (logical : PaperProofs.Paid.Computation.State) (left right : Register) (a b : ℕ)
    (contents : Stack → List Bool) (store : Option Bool)
    (represented : ∀ reg,contents (registerSlot reg)=encodeCellBits (logical.register reg))
    (leftNat : logical.register left=.natural a) (rightNat : logical.register right=.natural b)
    (emptyRight : contents 0=[]) (emptyLeft : contents 24=[]) :
    ∃ (run : List (NatOp.State operation)) (lastState : NatOp.State operation),
      run.head?=some (NatOp.before operation contents store) ∧ 
      run.IsChain (fun x y=>TM2.step (NatOp.program operation left right) x=some y) ∧ 
      run.getLast?=some lastState ∧ TM2.step (NatOp.program operation left right) lastState=none ∧ 
      RegistersRepresent logical lastState ∧ 
      ListBlank.mk (lastState.stk 0)=ListBlank.mk (encodeNat (NatOp.value operation a b)) ∧ 
      run.length ≤ computeBudget a b ∧ 
      (∀ state ∈ run,∀ role,(state.stk role).length ≤ 
        dataSize contents+computePushCap operation left right*computeBudget a b) ∧ 
      ∀ other,(∀ index,other ≠ NatMarshalGlobal.embedding left index) → 
        (∀ index,other ≠ NatMarshalGlobal.embedding right index) → 
        (∀ index,other ≠ Numeric.work index) → lastState.stk other=contents other := by
  obtain ⟨run,lastState,head,chain,last,halt,regs,result,time,frame⟩ :=
    NatOp.compute_runs operation logical left right a b contents store represented leftNat rightNat emptyRight emptyLeft
  refine ⟨run,lastState,head,chain,last,halt,regs,result,time,?_,frame⟩
  cases run with
  | nil => simp only [List.head?_nil,reduceCtorEq] at head
  | cons start rest =>
    have first : start=NatOp.before operation contents store := Option.some.inj head
    have initial : ∀ role,(start.stk role).length ≤ dataSize contents := by
      rw [first]
      exact dataSize_each contents
    have supported : start.l ∈ Finset.insertNone (Finset.univ : Finset NatOp.Label) := by
      rw [first]
      exact Finset.some_mem_insertNone.mpr (Finset.mem_univ _)
    have bounded := PDROC.BitVM.Common.source_path_occupancy (NatOp.program operation left right)
      Finset.univ (NatOp.program_supports operation left right) start rest (dataSize contents) supported initial chain
    have restBound : rest.length ≤ computeBudget a b := by
      change rest.length+1 ≤ computeBudget a b at time
      omega
    intro state member role
    exact ((bounded state member).2 role).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ restBound) _)

end PDROC.BitVM.Kernel.NatInstruction
