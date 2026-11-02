module

public import Paid.PDROC_BitVM_Kernel_RawFamily_045
public import Paid.PDROC_BitVM_Kernel_NatInstruction_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.RawInstruction

open Turing PDROC.BitVM.Native PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal
open PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

def computeBudget (logical : PaperProofs.Paid.Computation.State) (left right : Register)
    (x y : Rat) (c d : ℕ) : ℕ :=
  2*(encodeCellBits (logical.register left)).length+2*(encodeCellBits (logical.register right)).length+
    c*((encode [.rational x,.rational y]).length+1)^d+9

def pushCap {states : ℕ} (machine : Machine states) (left right : Register) : ℕ :=
  PDROC.BitVM.Common.sourcePushCap (RawOp.program machine left right) Finset.univ

/-- The physical native workspace allowance comes from the SAME actual
read/RAW computation trace. It includes all materialized FALSE cells and
arbitrary initially carried stacks; no source width or room is supplied. -/
theorem compute_resources {states : ℕ} (machine : Machine states) (resultFn : Rat → Rat → Rat) (c d : ℕ)
    (contract : RawOp.NativeContract machine resultFn c d)
    (logical : PaperProofs.Paid.Computation.State) (left right : Register) (x y : Rat)
    (contents : Stack → List Bool)
    (represented : ∀ reg,contents (registerSlot reg)=encodeCellBits (logical.register reg))
    (leftRat : logical.register left=.rational x) (rightRat : logical.register right=.rational y)
    (emptyRight : contents 0=[]) (emptyLeft : contents 24=[]) :
    ∃ (run : List (RawOp.State states)) (final : RawOp.State states),
      run.head?=some (RawOp.before contents none) ∧
      run.IsChain (fun a b=>TM2.step (RawOp.program machine left right) a=some b) ∧
      run.getLast?=some final ∧ TM2.step (RawOp.program machine left right) final=none ∧
      RegistersRepresent logical final ∧
      ListBlank.mk (final.stk 0)=ListBlank.mk (encode [.rational (resultFn x y)]) ∧
      run.length ≤ computeBudget logical left right x y c d ∧
      (∀ state ∈ run,∀ role,(state.stk role).length ≤ NatInstruction.dataSize contents+
        pushCap machine left right*computeBudget logical left right x y c d) ∧
      ∀ other,other ≠ 0 → other ≠ 24 → final.stk other=contents other := by
  obtain ⟨run,final,head,chain,last,halt,regs,result,time,frame⟩ :=
    RawOp.compute_runs machine resultFn c d contract logical left right x y contents none represented
      leftRat rightRat emptyRight emptyLeft
  refine ⟨run,final,head,chain,last,halt,regs,result,time,?_,frame⟩
  cases run with
  | nil => simp only [List.head?_nil,reduceCtorEq] at head
  | cons start rest =>
    have first : start=RawOp.before contents none := Option.some.inj head
    have initial : ∀ role,(start.stk role).length ≤ NatInstruction.dataSize contents := by
      rw [first]
      exact NatInstruction.dataSize_each contents
    have supported : start.l ∈ Finset.insertNone (Finset.univ : Finset RawOp.Label) := by
      rw [first]
      exact Finset.some_mem_insertNone.mpr (Finset.mem_univ _)
    have bounded := PDROC.BitVM.Common.source_path_occupancy (RawOp.program machine left right)
      Finset.univ (RawOp.supports machine left right) start rest (NatInstruction.dataSize contents)
      supported initial chain
    have restBound : rest.length ≤ computeBudget logical left right x y c d := by
      change rest.length+1 ≤ computeBudget logical left right x y c d at time
      omega
    intro state member role
    exact ((bounded state member).2 role).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ restBound) _)

end PDROC.BitVM.Kernel.RawInstruction
