module

public import Paid.PDCompute_SolverMinimumUpdate_031

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute loadSlot storeSlot)
open PDMenu.ComputeFrame

def addNatSlot (slot amount : ℕ) : List Instruction :=
  loadSlot slot .index++[.constant .flag (.natural amount),.natOp .add .index .index .flag]++storeSlot slot .index

def addNatSlotResult (before : State) (base slot value amount : ℕ) : State :=
  {before with
    register:=Function.update (Function.update (Function.update before.register .address (.natural (base+slot)))
      .flag (.natural amount)) .index (.natural (value+amount))
    heap:=Function.update before.heap (base+slot) (.natural (value+amount))
    live:=insert (base+slot) before.live
    pc:=before.pc+8}

theorem addNatSlot_length (slot amount : ℕ) : (addNatSlot slot amount).length=8 := rfl

theorem addNatSlot_straight (slot amount : ℕ) : StraightCode (addNatSlot slot amount) := by
  intro instruction member
  simp only [addNatSlot,loadSlot,storeSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ((h|h|h)|(h|h))|(h|h|h) <;> subst instruction <;> trivial

theorem addNatSlot_execute (input : List Cell) (before : State) (base slot value amount : ℕ)
    (hbase : before.register .fresh=.natural base) (hlive : base+slot ∈ before.live)
    (hvalue : before.heap (base+slot)=.natural value) :
    linearExecute input (addNatSlot slot amount) before=some (addNatSlotResult before base slot value amount) := by
  simp [addNatSlot,loadSlot,storeSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
    hbase,hlive,hvalue,addNatSlotResult,Nat.add_assoc]
  funext register
  cases register <;> simp

theorem addNatSlotResult_fields (before : State) (base slot value amount : ℕ) :
    (addNatSlotResult before base slot value amount).heap=Function.update before.heap (base+slot) (.natural (value+amount)) ∧
    (addNatSlotResult before base slot value amount).live=insert (base+slot) before.live ∧
    (addNatSlotResult before base slot value amount).register .fresh=before.register .fresh ∧
    (addNatSlotResult before base slot value amount).pc=before.pc+8 ∧
    (addNatSlotResult before base slot value amount).output=before.output := by
  simp [addNatSlotResult]

theorem Header.addNatSlot {before : State} {base : ℕ} {values : ℕ → Cell}
    (header : Header before base values) (slot value amount : ℕ) :
    Header (addNatSlotResult before base slot value amount) base (Function.update values slot (.natural (value+amount))) := by
  apply Header.update header slot (.natural (value+amount)) (addNatSlotResult_fields ..).1
  rw [(addNatSlotResult_fields before base slot value amount).2.1]
  exact Finset.subset_insert _ _

theorem addNatSlot_prefix_memory (input : List Cell) (before after : State) (base slot value amount : ℕ)
    (hbase : before.register .fresh=.natural base) (hlive : base+slot ∈ before.live)
    (hvalue : before.heap (base+slot)=.natural value) (count : ℕ) (hcount : count < 8)
    (hexec : linearExecute input ((addNatSlot slot amount).take count) before=some after) :
    after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  interval_cases count <;>
    simp [addNatSlot,loadSlot,storeSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
      hbase,hlive,hvalue] at hexec <;> subst after <;> exact ⟨rfl,rfl,rfl⟩

end PDCompute.Solver
