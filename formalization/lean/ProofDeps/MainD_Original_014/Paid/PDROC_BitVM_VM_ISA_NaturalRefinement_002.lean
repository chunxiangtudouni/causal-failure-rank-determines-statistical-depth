module

public import Paid.PDROC_BitVM_VM_ISA_NaturalRefinement_001
public import Paid.PDROC_BitVM_Log_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

namespace PDROC.BitVM.VM.ISA.NaturalRefinement

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters
open PDROC.BitVM.Kernel.RegisterGlobal

def base (input : List Cell) (contents : Stack → List Bool) :=
  Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1

/-- This depends only on the fixed old opcode syntax/register roles,
before every input/state/tape. It is not a runtime width qualification. -/
def coefficient (operation : PaperProofs.Paid.Computation.NatOp) (left right : Register) :=
  20000000 * (Kernel.NatInstruction.computePushCap operation left right + 1)

theorem whole_budget (input : List Cell) (logical : PaperProofs.Paid.Computation.State)
    (events : List Log.HeapEvent) (contents : Stack → List Bool) (ready : Source.Ready input logical events contents)
    (operation : PaperProofs.Paid.Computation.NatOp) (left right : Register) (a b : ℕ)
    (leftNat : logical.register left = .natural a) (rightNat : logical.register right = .natural b) :
    Kernel.NatInstruction.budget operation left right contents a b ≤
      coefficient operation left right * (base input contents)^2 := by
  have leftCell := Kernel.NatInstruction.dataSize_each contents (registerSlot left)
  have rightCell := Kernel.NatInstruction.dataSize_each contents (registerSlot right)
  rw [ready.registers left, leftNat] at leftCell
  rw [ready.registers right, rightNat] at rightCell
  simp only [encodeCellBits, List.length_cons] at leftCell rightCell
  have leftBits : natBits a ≤ Kernel.NatInstruction.dataSize contents := by
    rw [Log.nat_word_length] at leftCell
    omega
  have rightBits : natBits b ≤ Kernel.NatInstruction.dataSize contents := by
    rw [Log.nat_word_length] at rightCell
    omega
  have leftWord : (encodeNatBits a).length ≤ Kernel.NatInstruction.dataSize contents := by omega
  have rightWord : (encodeNatBits b).length ≤ Kernel.NatInstruction.dataSize contents := by omega
  have data : Kernel.NatInstruction.dataSize contents ≤ base input contents := by unfold base; omega
  have dataNext : Kernel.NatInstruction.dataSize contents+1 ≤ base input contents := by unfold base; omega
  have positive : 1 ≤ base input contents := by unfold base; omega
  have square : base input contents ≤ (base input contents)^2 := by
    simpa only [pow_two, Nat.mul_one] using Nat.mul_le_mul_left (base input contents) positive
  have sumBound : natBits a + natBits b + 1 ≤ 2 * base input contents := by omega
  have squareBound : (natBits a + natBits b + 1)^2 ≤ 4 * (base input contents)^2 := by
    have multiplied := Nat.mul_le_mul sumBound sumBound
    nlinarith
  have compute : Kernel.NatInstruction.computeBudget a b ≤ 132000 * (base input contents)^2 := by
    change 2*(encodeNatBits a).length+2*(encodeNatBits b).length+
      32768*(natBits a+natBits b+1)^2+12 ≤ 132000*(base input contents)^2
    nlinarith
  have scaled := Nat.mul_le_mul_left (Kernel.NatInstruction.computePushCap operation left right) compute
  have nonnegative : 0 ≤ Kernel.NatInstruction.computePushCap operation left right * (base input contents)^2 := Nat.zero_le _
  unfold Kernel.NatInstruction.budget coefficient
  nlinarith

theorem natural_resource (backend : RatBackend) (core : Bool)
    (operation : PaperProofs.Paid.Computation.NatOp) (target left right : Register) :
    ResourceRefinement backend core ⟨.natOp operation target left right, rfl⟩ := by
  refine ⟨coefficient operation left right, 2, ?_, by decide, ?_⟩
  · exact Nat.mul_pos (by decide) (Nat.succ_pos _)
  · intro input logical next events contents size ready success
    obtain ⟨a, b, result, leftNat, rightNat, evaluated, nextValue⟩ :=
      successful_operands input logical next operation target left right success
    obtain ⟨run, final, executed, head, chain, last, halt, registers, work0, work24, time, frame⟩ :=
      Kernel.NatInstruction.instruction_runs input logical operation target left right a b result contents none
        ready.registers leftNat rightNat evaluated
        (ready.workspace 0 (Or.inl rfl)) (ready.workspace 24 (Or.inr (by decide)))
    refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
    exact time.trans (whole_budget input logical events contents ready operation left right a b leftNat rightNat)

end PDROC.BitVM.VM.ISA.NaturalRefinement
