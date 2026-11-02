module

public import Paid.PDCompute_SolverPrimitiveMemory_055

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute loadSlot storeSlot)

theorem loadSlot_prefix_memory (input : List Cell) (before after : State) (base slot : ℕ) (target : Register)
    (hbase : before.register .fresh=.natural base) (hlive : base+slot ∈ before.live)
    (count : ℕ) (hcount : count ≤ 3)
    (hexec : linearExecute input ((loadSlot slot target).take count) before=some after) :
    after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  interval_cases count <;>
    simp [loadSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,hbase,hlive] at hexec <;>
    subst after <;> exact ⟨rfl,rfl,rfl⟩

theorem storeSlot_prefix_memory (input : List Cell) (before after : State) (base slot : ℕ) (source : Register)
    (values : ℕ → Cell) (header : Header before base values) (inside : slot < headerWords)
    (hbase : before.register .fresh=.natural base) (different : source ≠ .address)
    (count : ℕ) (hcount : count ≤ 3)
    (hexec : linearExecute input ((storeSlot slot source).take count) before=some after) :
    HeaderMemory before after base := by
  interval_cases count <;>
    simp [storeSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,hbase,different] at hexec <;>
    subst after
  all_goals first
    | exact HeaderMemory.of_unchanged base rfl rfl rfl
    | exact HeaderMemory.write header slot inside (before.register source) rfl rfl rfl

theorem endpointPairCode_prefix_memory (mode : ReaderMode) (input : List Cell) (before after : State)
    (address : ℕ) (error charge : ℚ) (haddress : before.register .address=.natural address)
    (herror : mode.HasCell input before address (.rational error))
    (hcharge : mode.HasCell input before (address+1) (.rational charge))
    (count : ℕ) (hcount : count ≤ 4)
    (hexec : linearExecute input ((endpointPairCode mode).take count) before=some after) :
    after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  cases mode with
  | inputROM =>
    change input[address]?=some (.rational error) at herror
    change input[address+1]?=some (.rational charge) at hcharge
    interval_cases count <;>
      simp [endpointPairCode,ReaderMode.read,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
        haddress,herror,hcharge] at hexec <;> subst after <;> exact ⟨rfl,rfl,rfl⟩
  | liveHeap =>
    interval_cases count <;>
      simp [endpointPairCode,ReaderMode.read,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
        haddress,herror.1,herror.2,hcharge.1,hcharge.2] at hexec <;> subst after <;> exact ⟨rfl,rfl,rfl⟩

end PDCompute.Solver
