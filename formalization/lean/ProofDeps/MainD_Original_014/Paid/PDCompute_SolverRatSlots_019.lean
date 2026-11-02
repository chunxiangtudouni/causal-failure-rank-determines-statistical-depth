module

public import Paid.PDCompute_SolverReader_018

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult storeSlot storeSlotResult)
open PDMenu.ComputeFrame

/-- A literal ten-instruction scalar operation on live solver-header
slots. Its two reads occur before its write, so aliasing is permitted.
In particular this is not a table/argmin/arithmetic-expression oracle. -/
def ratBinarySlots (operation : RatOp) (left right target : ℕ) : List Instruction :=
  loadSlot left .total ++ loadSlot right .value ++
    [.ratOp operation .total .total .value] ++ storeSlot target .total

def ratBinarySlotsResult (before : State) (base left right target : ℕ) (value : ℚ) : State :=
  let loaded := loadSlotResult (loadSlotResult before base left .total) base right .value
  let computed := ({loaded with pc:=loaded.pc+1}).set .total (.rational value)
  storeSlotResult computed base target .total

theorem ratBinarySlots_length (operation : RatOp) (left right target : ℕ) :
    (ratBinarySlots operation left right target).length=10 := rfl

theorem ratBinarySlots_straight (operation : RatOp) (left right target : ℕ) :
    StraightCode (ratBinarySlots operation left right target) := by
  intro instruction member
  simp only [ratBinarySlots,loadSlot,storeSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (((h|h|h)|(h|h|h))|h)|(h|h|h) <;> subst instruction <;> trivial

theorem ratBinarySlots_execute (input : List Cell) (before : State)
    (base left right target : ℕ) (operation : RatOp) (x y value : ℚ)
    (hbase : before.register .fresh=.natural base)
    (hleftLive : base+left ∈ before.live) (hrightLive : base+right ∈ before.live)
    (hleft : before.heap (base+left)=.rational x) (hright : before.heap (base+right)=.rational y)
    (hoperation : operation.eval x y=some value) :
    linearExecute input (ratBinarySlots operation left right target) before=
      some (ratBinarySlotsResult before base left right target value) := by
  simp [ratBinarySlots,loadSlot,storeSlot,linearExecute,Instruction.execute,State.set,
    NatOp.eval,Cell.nat?,Cell.rat?,hbase,hleftLive,hrightLive,hleft,hright,hoperation,
    ratBinarySlotsResult,loadSlotResult,storeSlotResult,Nat.add_assoc]

theorem ratBinarySlotsResult_pc (before : State) (base left right target : ℕ) (value : ℚ) :
    (ratBinarySlotsResult before base left right target value).pc=before.pc+10 := by
  simp [ratBinarySlotsResult,loadSlotResult,storeSlotResult,State.set]

theorem ratBinarySlotsResult_heap (before : State) (base left right target : ℕ) (value : ℚ) :
    (ratBinarySlotsResult before base left right target value).heap=
      Function.update before.heap (base+target) (.rational value) := by
  simp [ratBinarySlotsResult,loadSlotResult,storeSlotResult,State.set]

theorem ratBinarySlotsResult_live (before : State) (base left right target : ℕ) (value : ℚ) :
    (ratBinarySlotsResult before base left right target value).live=insert (base+target) before.live := rfl

theorem ratBinarySlotsResult_base (before : State) (base left right target : ℕ) (value : ℚ) :
    (ratBinarySlotsResult before base left right target value).register .fresh=before.register .fresh := by
  simp [ratBinarySlotsResult,loadSlotResult,storeSlotResult,State.set]

theorem ratBinarySlotsResult_output (before : State) (base left right target : ℕ) (value : ℚ) :
    (ratBinarySlotsResult before base left right target value).output=before.output := rfl

theorem ratBinarySlotsResult_frame (before : State) (base left right target : ℕ) (value : ℚ)
    (n k : ℕ) (htarget : target < headerWords) :
    Frame before (ratBinarySlotsResult before base left right target value) base n k := by
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
    rw [ratBinarySlotsResult_heap]
    exact Function.update_of_ne (hne address hout) _ _
  · intro address hout
    rw [ratBinarySlotsResult_live]
    simp only [Finset.mem_insert,hne address hout,false_or]

/-- The scalar macro has a real fetched trace and retains strict-prefix
execution witnesses for subsequent whole-algorithm peak bounds. -/
theorem ratBinarySlots_trace (program : Program) (input : List Cell) (before : State)
    (base left right target : ℕ) (operation : RatOp) (x y value : ℚ)
    (hbase : before.register .fresh=.natural base)
    (hleftLive : base+left ∈ before.live) (hrightLive : base+right ∈ before.live)
    (hleft : before.heap (base+left)=.rational x) (hright : before.heap (base+right)=.rational y)
    (hoperation : operation.eval x y=some value)
    (hfetch : FetchesCode program before.pc (ratBinarySlots operation left right target)) :
    ∃ trace : List State, trace.head?=some before ∧
      trace.getLast?=some (ratBinarySlotsResult before base left right target value) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 165 ∧
      ∀ state ∈ trace.dropLast, ∃ count < 10,
        linearExecute input ((ratBinarySlots operation left right target).take count) before=some state := by
  simpa only [ratBinarySlots_length] using linearExecute_trace_time program input
    (ratBinarySlots operation left right target) (ratBinarySlots_straight operation left right target)
    before (ratBinarySlotsResult before base left right target value) hfetch
    (ratBinarySlots_execute input before base left right target operation x y value
      hbase hleftLive hrightLive hleft hright hoperation)

end PDCompute.Solver
