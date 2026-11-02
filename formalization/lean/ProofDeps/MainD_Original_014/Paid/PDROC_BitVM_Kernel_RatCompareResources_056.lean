module

public import Paid.PDROC_BitVM_Kernel_RatCompareFamily_055
public import Paid.PDROC_BitVM_Kernel_RatBudget_052

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.RatCompare

open Turing PDROC.BitVM.Native PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal
open PaperProofs.Common.Native.RationalControllerComputation

def differenceCap {states : ℕ} (machine : Machine states) (target left right : Register) : ℕ :=
  PDROC.BitVM.Common.sourcePushCap (RawInstruction.program machine target left right) Finset.univ

def budget {states : ℕ} (machine : Machine states) (logical : PaperProofs.Paid.Computation.State)
    (target left right : Register) (x y : Rat) (c d : ℕ) (contents : Stack → List Bool) : ℕ :=
  let Q := RawInstruction.budget machine logical left right x y c d contents
  Q+64*(NatInstruction.dataSize contents+differenceCap machine target left right*Q+5)+8

/-- The real complete RAW difference calculation supplies both its
canonical target Cell and its actual workspace envelope on ONE path. -/
theorem difference_resources {states : ℕ} (machine : Machine states) (c d : ℕ)
    (contract : RawOp.NativeContract machine (fun x y=>x-y) c d)
    (logical : PaperProofs.Paid.Computation.State) (target left right : Register) (x y : Rat)
    (contents : Stack → List Bool)
    (represented : ∀ reg,contents (registerSlot reg)=encodeCellBits (logical.register reg))
    (leftRat : logical.register left=.rational x) (rightRat : logical.register right=.rational y)
    (empty0 : contents 0=[]) (empty24 : contents 24=[]) :
    ∃ (run : List (RawInstruction.State states)) (final : RawInstruction.State states),
      run.head?=some (RawInstruction.before states contents) ∧
      run.IsChain (fun a b=>TM2.step (RawInstruction.program machine target left right) a=some b) ∧
      run.getLast?=some final ∧ TM2.step (RawInstruction.program machine target left right) final=none ∧
      final.stk (registerSlot target)=encodeCellBits (.rational (x-y)) ∧
      final.stk 0=[] ∧ final.stk 24=[] ∧ final.stk 25=[] ∧ final.stk 29=[] ∧
      run.length ≤ RawInstruction.budget machine logical left right x y c d contents ∧
      (∀ state ∈ run,∀ role,(state.stk role).length ≤ NatInstruction.dataSize contents+
        differenceCap machine target left right*RawInstruction.budget machine logical left right x y c d contents) ∧
      ∀ role,role ≠ 0 → role ≠ 24 → role ≠ 25 → role ≠ 29 → role ≠ registerSlot target →
        final.stk role=contents role := by
  obtain ⟨run,final,head,chain,last,halt,word,work0,work24,work25,work29,time,frame⟩ :=
    RawInstruction.runs machine (fun x y=>x-y) c d contract logical target left right x y contents
      represented leftRat rightRat empty0 empty24
  refine ⟨run,final,head,chain,last,halt,word,work0,work24,work25,work29,time,?_,frame⟩
  cases run with
  | nil => simp only [List.head?_nil,reduceCtorEq] at head
  | cons start rest =>
    have initial : start=RawInstruction.before states contents := Option.some.inj head
    have occupied : ∀ role,(start.stk role).length ≤ NatInstruction.dataSize contents := by
      rw [initial]
      exact NatInstruction.dataSize_each contents
    have supported : start.l ∈ Finset.insertNone (Finset.univ : Finset RawInstruction.Label) := by
      rw [initial]
      exact Finset.some_mem_insertNone.mpr (Finset.mem_univ _)
    have actual := PDROC.BitVM.Common.source_path_occupancy (RawInstruction.program machine target left right)
      Finset.univ (RawInstruction.supports machine target left right) start rest
      (NatInstruction.dataSize contents) supported occupied chain
    have tailTime : rest.length ≤ RawInstruction.budget machine logical left right x y c d contents := by
      change rest.length+1 ≤ RawInstruction.budget machine logical left right x y c d contents at time
      omega
    intro state member role
    exact ((actual state member).2 role).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ tailTime) _)

end PDROC.BitVM.Kernel.RatCompare
