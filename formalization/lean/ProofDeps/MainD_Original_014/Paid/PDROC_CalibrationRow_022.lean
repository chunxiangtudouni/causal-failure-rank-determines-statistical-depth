module

public import Paid.PDROC_CalibrationRow_019

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid.Computation PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- All proper prefixes of an atomic final-store macro have precisely
the incoming heap and live cells. The only alternative is its actual
fully executed result. This exports each clock/cursor and partial row,
rather than merely bounding the final mutable workspace. -/
theorem single_last_prefix_memory (input : List Cell) (prelude : List Instruction) (last : Instruction)
    (before after : State)
    (safe : ∀ instruction ∈ prelude,∀ state,WritesWithin ∅ instruction state)
    (executed : linearExecute input (prelude++[last]) before=some after)
    (count : ℕ) (state : State)
    (run : linearExecute input ((prelude++[last]).take count) before=some state) :
    MemoryFrame ∅ before state ∨ state=after := by
  by_cases short : count≤prelude.length
  · left
    rw [List.take_append_of_le_length short] at run
    exact LinearFrames.of_static ∅ input prelude safe before count state run
  · right
    have whole : (prelude++[last]).length≤count := by
      simp only [List.length_append,List.length_singleton]
      omega
    rw [List.take_of_length_le whole,executed] at run
    exact (Option.some.inj run).symm

theorem empty_frame_row (before after : State) (rowBase : ℕ) (row : Array ℚ)
    (represented : RowAt before rowBase row) (frame : MemoryFrame ∅ before after) : RowAt after rowBase row := by
  constructor
  · intro i inside
    exact (frame.2 (rowBase+i) (by simp)).mpr (represented.live i inside)
  · intro i inside
    exact (frame.1 (rowBase+i) (by simp)).trans (represented.value i inside)

theorem empty_frame_slot (before after : State) (address : ℕ) (frame : MemoryFrame ∅ before after) :
    after.heap address=before.heap address := frame.1 address (by simp)

/-- Before the literal store, the write buffer is the preceding partial
scatter. At and after the store it is the genuine one-letter bump.
This covers the transient first letter when both targets coincide. -/
theorem scatterStore_prefix_rows (input : List Cell) (before : State)
    (base rowBase target : ℕ) (row : Array ℚ) (amount : ℚ)
    (represented : RowAt before rowBase row) (targetBound : target<row.size)
    (fresh : before.register .fresh=.natural base)
    (pointerLive : base+10 ∈ before.live) (pointer : before.heap (base+10)=.natural rowBase)
    (index : before.register .index=.natural target) (value : before.register .value=.rational amount)
    (count : ℕ) (state : State)
    (run : linearExecute input (scatterStoreCode.take count) before=some state) :
    (MemoryFrame ∅ before state ∧ RowAt state rowBase row) ∨
      (state=scatterStoreResult before base rowBase target (row.getD target 0) amount ∧
        RowAt state rowBase (PDROC.endpointArrayBump row target amount)) := by
  have actual := scatterStore_execute input before base rowBase target (row.getD target 0) amount fresh pointerLive
    pointer index value (represented.live target targetBound) (represented.value target targetBound)
  rw [scatterStore_decompose] at actual run
  have memory := single_last_prefix_memory input scatterStorePrefixCode (.store .address .value) before
    (scatterStoreResult before base rowBase target (row.getD target 0) amount) (by
      intro instruction member state
      simp only [scatterStorePrefixCode,loadSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with (h|h|h)|(h|h|h) <;> subst instruction <;> trivial) actual count state run
  rcases memory with unchanged|equal
  · exact Or.inl ⟨unchanged,empty_frame_row before state rowBase row represented unchanged⟩
  · subst state
    exact Or.inr ⟨rfl,scatterStore_bump before base rowBase target row amount represented targetBound⟩

end PDROC.CalibrationRow
