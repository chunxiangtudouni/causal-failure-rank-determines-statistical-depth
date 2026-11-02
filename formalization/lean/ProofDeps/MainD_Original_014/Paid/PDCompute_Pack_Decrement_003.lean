module
public import Paid.PDCompute_Pack_Code_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute loadSlot storeSlot)

def decrementResult (before : State) (base slot value : ℕ) : State :=
  {before with
    register:=Function.update (Function.update (Function.update before.register .address (.natural (base+slot)))
      .flag (.natural 1)) .index (.natural (value-1))
    heap:=Function.update before.heap (base+slot) (.natural (value-1))
    live:=insert (base+slot) before.live
    pc:=before.pc+8}

theorem decrementSlot_straight (slot : ℕ) : StraightCode (decrementSlot slot) := by
  intro instruction member
  simp only [decrementSlot,loadSlot,storeSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ((h|h|h)|(h|h))|(h|h|h) <;> subst instruction <;> trivial

theorem decrement_execute (input : List Cell) (before : State) (base slot value : ℕ)
    (hbase : before.register .fresh=.natural base) (hlive : base+slot∈before.live)
    (hvalue : before.heap (base+slot)=.natural value) :
    linearExecute input (decrementSlot slot) before=some (decrementResult before base slot value) := by
  simp [decrementSlot,loadSlot,storeSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
    hbase,hlive,hvalue,decrementResult,Nat.add_assoc]
  funext register
  cases register <;> simp

theorem decrement_fields (before : State) (base slot value : ℕ) :
    (decrementResult before base slot value).heap=Function.update before.heap (base+slot) (.natural (value-1)) ∧
    (decrementResult before base slot value).live=insert (base+slot) before.live ∧
    (decrementResult before base slot value).register .fresh=before.register .fresh ∧
    (decrementResult before base slot value).pc=before.pc+8 ∧
    (decrementResult before base slot value).output=before.output := by
  simp [decrementResult]

theorem decrement_header (before : State) (base slot value : ℕ) (values : ℕ → Cell)
    (header : Header before base values) :
    Header (decrementResult before base slot value) base (Function.update values slot (.natural (value-1))) := by
  apply Header.update header slot (.natural (value-1)) (decrement_fields ..).1
  rw [(decrement_fields before base slot value).2.1]
  exact Finset.subset_insert _ _

/-- Every successful literal prefix, including the store, has exactly the
existing Header48 footprint. Existing live cells in that region are allowed. -/
theorem decrement_prefix_memory (input : List Cell) (before after : State) (base slot value : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (inside : slot<headerWords)
    (hbase : before.register .fresh=.natural base) (hvalue : values slot=.natural value)
    (count : ℕ) (hcount : count≤8)
    (execute : linearExecute input ((decrementSlot slot).take count) before=some after) :
    HeaderMemory before after base := by
  have live:=header.live slot inside
  have valueAt:=(header.value slot inside).trans hvalue
  by_cases short : count<8
  · have unchanged : after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
      interval_cases count <;>
        simp [decrementSlot,loadSlot,storeSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
          hbase,live,valueAt] at execute <;> subst after <;> exact ⟨rfl,rfl,rfl⟩
    exact HeaderMemory.of_unchanged base unchanged.1 unchanged.2.1 unchanged.2.2
  · have same : count=8 := by omega
    subst count
    have run : linearExecute input (decrementSlot slot) before=some after := execute
    rw [decrement_execute input before base slot value hbase live valueAt] at run
    have eq:=Option.some.inj run
    subst after
    have fields:=decrement_fields before base slot value
    exact HeaderMemory.write header slot inside (.natural (value-1)) fields.1 fields.2.1 fields.2.2.2.2

end PDCompute.Pack
