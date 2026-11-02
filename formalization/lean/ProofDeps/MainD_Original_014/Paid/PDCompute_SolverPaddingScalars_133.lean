module

public import Paid.PDCompute_SolverPaddingPairs_132

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDLower.CalibrationCompute (linearExecute)

def paddingConstantResult (before : State) (target : Register) (value : Cell) : State :=
  ({before with pc:=before.pc+1}).set target value

theorem paddingConstant_prefix_resources (input : List Cell) (before after : State) (budget count : ℕ)
    (target : Register) (value : Cell) (safe : RootD27.Bits.SafeBits before budget)
    (valueBits : value.bits ≤ budget) (pcBits : natBits (before.pc+1) ≤ budget) (bound : count ≤ 1)
    (executed : linearExecute input ([.constant target value].take count) before=some after) (region : Finset ℕ) :
    RegionMemory before after region ∧ RootD27.Bits.SafeBits after budget := by
  interval_cases count
  · have same : before=after := by simpa only [List.take_zero,linearExecute,Option.some.injEq] using executed
    subst after
    exact ⟨RegionMemory.refl before _,safe⟩
  · have same : paddingConstantResult before target value=after := by
      change (some (paddingConstantResult before target value) : Option State)=some after at executed
      exact Option.some.inj executed
    subst after
    exact ⟨RegionMemory.of_unchanged _ rfl rfl rfl,(safe.withPC (before.pc+1) pcBits).set target value valueBits⟩

def paddingDecrementCode : List Instruction := [.natOp .subtract .index .index .flag]

def paddingDecrementResult (before : State) (index : ℕ) : State :=
  ({before with pc:=before.pc+1}).set .index (.natural (index-1))

theorem paddingDecrement_execute (input : List Cell) (before : State) (index : ℕ)
    (current : before.register .index=.natural index) (one : before.register .flag=.natural 1) :
    linearExecute input paddingDecrementCode before=some (paddingDecrementResult before index) := by
  simp [paddingDecrementCode,paddingDecrementResult,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,current,one]

theorem paddingDecrement_prefix_resources (input : List Cell) (before after : State) (index budget count : ℕ)
    (current : before.register .index=.natural index) (one : before.register .flag=.natural 1)
    (safe : RootD27.Bits.SafeBits before budget) (pcBits : natBits (before.pc+1) ≤ budget) (bound : count ≤ 1)
    (executed : linearExecute input (paddingDecrementCode.take count) before=some after) (region : Finset ℕ) :
    RegionMemory before after region ∧ RootD27.Bits.SafeBits after budget := by
  interval_cases count
  · have same : before=after := by simpa only [List.take_zero,linearExecute,Option.some.injEq] using executed
    subst after
    exact ⟨RegionMemory.refl before _,safe⟩
  · change linearExecute input paddingDecrementCode before=some after at executed
    rw [paddingDecrement_execute input before index current one] at executed
    have same:=Option.some.inj executed
    subst after
    have oldBits : 1+natBits index ≤ budget := by simpa only [current,Cell.bits] using safe.register .index
    have newBits : (.natural (index-1) : Cell).bits ≤ budget := by
      have mono:=natBits_mono (Nat.sub_le index 1)
      change 1+natBits (index-1) ≤ budget
      omega
    exact ⟨RegionMemory.of_unchanged _ rfl rfl rfl,(safe.withPC (before.pc+1) pcBits).set .index (.natural (index-1)) newBits⟩

end PDCompute.Solver
