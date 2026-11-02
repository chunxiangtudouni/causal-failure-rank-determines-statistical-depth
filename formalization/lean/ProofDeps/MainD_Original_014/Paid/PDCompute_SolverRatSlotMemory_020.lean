module

public import Paid.PDCompute_SolverRatSlots_019

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute loadSlot storeSlot)

theorem ratBinarySlotsResult_value (before : State) (base left right target : ℕ) (value : ℚ) :
    (ratBinarySlotsResult before base left right target value).heap (base+target)=.rational value := by
  rw [ratBinarySlotsResult_heap]
  exact Function.update_self _ _ _

theorem ratBinarySlotsResult_other (before : State) (base left right target query : ℕ) (value : ℚ)
    (hne : query ≠ target) :
    (ratBinarySlotsResult before base left right target value).heap (base+query)=before.heap (base+query) := by
  rw [ratBinarySlotsResult_heap]
  exact Function.update_of_ne (fun he => hne (Nat.add_left_cancel he)) _ _

theorem ratBinarySlotsResult_live_mono (before : State) (base left right target : ℕ) (value : ℚ) :
    before.live ⊆ (ratBinarySlotsResult before base left right target value).live := by
  rw [ratBinarySlotsResult_live]
  exact Finset.subset_insert _ _

theorem ratBinarySlotsResult_target_live (before : State) (base left right target : ℕ) (value : ℚ) :
    base+target ∈ (ratBinarySlotsResult before base left right target value).live := by
  rw [ratBinarySlotsResult_live]
  exact Finset.mem_insert_self _ _

/-- The only store is the tenth actual instruction. Thus every earlier
state, including both typed heap reads and the rational arithmetic, has
exactly the old live heap and output. This is an intermediate-state fact,
not an inference from the final state's frame. -/
theorem ratBinarySlots_prefix_memory (input : List Cell) (before after : State)
    (base left right target : ℕ) (operation : RatOp) (x y value : ℚ)
    (hbase : before.register .fresh=.natural base)
    (hleftLive : base+left ∈ before.live) (hrightLive : base+right ∈ before.live)
    (hleft : before.heap (base+left)=.rational x) (hright : before.heap (base+right)=.rational y)
    (hoperation : operation.eval x y=some value)
    (count : ℕ) (hcount : count < 10)
    (hexec : linearExecute input ((ratBinarySlots operation left right target).take count) before=some after) :
    after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  interval_cases count <;>
    simp [ratBinarySlots,loadSlot,storeSlot,linearExecute,Instruction.execute,State.set,
      NatOp.eval,Cell.nat?,Cell.rat?,hbase,hleftLive,hrightLive,hleft,hright,hoperation] at hexec <;>
    subst after <;> exact ⟨rfl,rfl,rfl⟩

end PDCompute.Solver
