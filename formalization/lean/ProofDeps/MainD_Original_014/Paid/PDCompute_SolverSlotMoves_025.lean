module

public import Paid.PDCompute_SolverHeader_024

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult storeSlot storeSlotResult)
open PDMenu.ComputeFrame

def constantSlot (target : ℕ) (value : Cell) : List Instruction :=
  [.constant .total value]++storeSlot target .total

def constantSlotResult (before : State) (base target : ℕ) (value : Cell) : State :=
  storeSlotResult (({before with pc:=before.pc+1}).set .total value) base target .total

def copySlot (source target : ℕ) : List Instruction := loadSlot source .total++storeSlot target .total

def copySlotResult (before : State) (base source target : ℕ) : State :=
  storeSlotResult (loadSlotResult before base source .total) base target .total

theorem constantSlot_length (target : ℕ) (value : Cell) : (constantSlot target value).length=4 := rfl
theorem copySlot_length (source target : ℕ) : (copySlot source target).length=6 := rfl

theorem constantSlot_execute (input : List Cell) (before : State) (base target : ℕ) (value : Cell)
    (hbase : before.register .fresh=.natural base) :
    linearExecute input (constantSlot target value) before=some (constantSlotResult before base target value) := by
  simp [constantSlot,storeSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,hbase,
    constantSlotResult,storeSlotResult,Nat.add_assoc]

theorem copySlot_execute (input : List Cell) (before : State) (base source target : ℕ)
    (hbase : before.register .fresh=.natural base) (hlive : base+source ∈ before.live) :
    linearExecute input (copySlot source target) before=some (copySlotResult before base source target) := by
  simp [copySlot,loadSlot,storeSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,hbase,hlive,
    copySlotResult,loadSlotResult,storeSlotResult,Nat.add_assoc]

theorem constantSlot_straight (target : ℕ) (value : Cell) : StraightCode (constantSlot target value) := by
  intro instruction member
  simp only [constantSlot,storeSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h <;> subst instruction <;> trivial

theorem copySlot_straight (source target : ℕ) : StraightCode (copySlot source target) := by
  intro instruction member
  simp only [copySlot,loadSlot,storeSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (h|h|h)|(h|h|h) <;> subst instruction <;> trivial

theorem constantSlotResult_fields (before : State) (base target : ℕ) (value : Cell) :
    (constantSlotResult before base target value).heap=Function.update before.heap (base+target) value ∧
    (constantSlotResult before base target value).live=insert (base+target) before.live ∧
    (constantSlotResult before base target value).register .fresh=before.register .fresh ∧
    (constantSlotResult before base target value).pc=before.pc+4 ∧
    (constantSlotResult before base target value).output=before.output := by
  simp [constantSlotResult,storeSlotResult,State.set]

theorem copySlotResult_fields (before : State) (base source target : ℕ) :
    (copySlotResult before base source target).heap=Function.update before.heap (base+target) (before.heap (base+source)) ∧
    (copySlotResult before base source target).live=insert (base+target) before.live ∧
    (copySlotResult before base source target).register .fresh=before.register .fresh ∧
    (copySlotResult before base source target).pc=before.pc+6 ∧
    (copySlotResult before base source target).output=before.output := by
  simp [copySlotResult,loadSlotResult,storeSlotResult]

theorem Header.constantSlot {before : State} {base : ℕ} {values : ℕ → Cell}
    (header : Header before base values) (target : ℕ) (value : Cell) :
    Header (constantSlotResult before base target value) base (Function.update values target value) := by
  apply Header.update header target value (constantSlotResult_fields ..).1
  rw [(constantSlotResult_fields before base target value).2.1]
  exact Finset.subset_insert _ _

theorem Header.copySlot {before : State} {base : ℕ} {values : ℕ → Cell}
    (header : Header before base values) (source target : ℕ) (hsource : source < headerWords) :
    Header (copySlotResult before base source target) base (Function.update values target (values source)) := by
  apply Header.update header target (values source)
  · rw [(copySlotResult_fields before base source target).1,header.value source hsource]
  · rw [(copySlotResult_fields before base source target).2.1]
    exact Finset.subset_insert _ _

theorem slotWrite_frame (before after : State) (base target n k : ℕ) (value : Cell)
    (htarget : target < headerWords) (hheap : after.heap=Function.update before.heap (base+target) value)
    (hlive : after.live=insert (base+target) before.live) : Frame before after base n k := by
  have hin : base+target ∈ workspace base n k := by
    apply Finset.mem_image.mpr
    refine ⟨target,Finset.mem_range.mpr ?_,rfl⟩
    unfold workspaceSize
    omega
  have hne (address : ℕ) (hout : address ∉ workspace base n k) : address ≠ base+target := by
    intro he
    exact hout (he.symm ▸ hin)
  constructor
  · intro address hout
    rw [hheap]
    exact Function.update_of_ne (hne address hout) _ _
  · intro address hout
    rw [hlive]
    simp only [Finset.mem_insert,hne address hout,false_or]

end PDCompute.Solver
