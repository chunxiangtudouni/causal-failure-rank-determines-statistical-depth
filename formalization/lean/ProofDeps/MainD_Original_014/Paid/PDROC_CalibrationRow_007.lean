module

public import Paid.PDROC_CalibrationRow_005
public import Paid.PDLower_CalibrationCompute_Constants_021
public import Paid.PDLower_CalibrationCompute_RowBridge_044

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid.Computation PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- A non-storing prefix leaves no unverified intermediate write. The
last instruction's frame is discharged from its actual typed store. -/
theorem single_last_frames (region : Finset ℕ) (input : List Cell) (prelude : List Instruction)
    (last : Instruction) (before after : State)
    (safe : ∀ instruction ∈ prelude,∀ state,WritesWithin region instruction state)
    (executed : linearExecute input (prelude++[last]) before=some after)
    (lastFrame : MemoryFrame region before after) : LinearFrames region input (prelude++[last]) before := by
  intro count state run
  by_cases short : count ≤ prelude.length
  · rw [List.take_append_of_le_length short] at run
    exact LinearFrames.of_static region input prelude safe before count state run
  · have all : (prelude++[last]).length ≤ count := by simp only [List.length_append,List.length_singleton]; omega
    rw [List.take_of_length_le all,executed] at run
    have same : after=state := Option.some.inj run
    simpa only [same] using lastFrame

theorem frame_of_one_update (region : Finset ℕ) (before after : State) (address : ℕ) (value : Cell)
    (inside : address ∈ region)
    (heap : after.heap=Function.update before.heap address value)
    (live : after.live=insert address before.live) : MemoryFrame region before after := by
  have different (query : ℕ) (outside : query ∉ region) : query ≠ address := by
    intro equal
    exact outside (equal.symm ▸ inside)
  constructor
  · intro query outside
    rw [heap]
    exact Function.update_of_ne (different query outside) _ _
  · intro query outside
    rw [live]
    simp only [Finset.mem_insert,different query outside,false_or]

def constantPrefixCode (offset : ℕ) (value : Cell) : List Instruction :=
  [.constant .value value,.constant .address (.natural offset),.natOp .add .address .fresh .address]

theorem constantCode_decompose (offset : ℕ) (value : Cell) :
    constantSlot offset value=constantPrefixCode offset value++[.store .address .value] := rfl

theorem constantPrefix_static (region : Finset ℕ) (offset : ℕ) (value : Cell) :
    ∀ instruction ∈ constantPrefixCode offset value,∀ state,WritesWithin region instruction state := by
  intro instruction member state
  simp only [constantPrefixCode,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h <;> subst instruction <;> trivial

/-- Reuses the frozen original .value-register constant macro. It is not
the similarly named solver macro, which stores through .total. -/
theorem constant_prefix_frames (region : Finset ℕ) (input : List Cell) (before : State)
    (base offset : ℕ) (value : Cell) (fresh : before.register .fresh=.natural base)
    (inside : base+offset ∈ region) : LinearFrames region input (constantSlot offset value) before := by
  rw [constantCode_decompose]
  apply single_last_frames region input (constantPrefixCode offset value) (.store .address .value)
    before (constantSlotResult before base offset value) (constantPrefix_static region offset value)
  · rw [←constantCode_decompose]
    exact constantSlot_execute input before base offset value fresh
  · exact frame_of_one_update region before _ (base+offset) value inside
      (constantSlot_heap before base offset value) (constantSlot_live before base offset value)

/-- The reused frozen array bridge keeps both original absorbed-letter
additions; no row or successful update is provided as an input oracle. -/
theorem scatter_prefix_exact (P : PaperProofs.Paid.Parameters) (level : ℕ) (previous : Array ℚ) :
    rowScatterPrefix P level previous (2*level+1)=P.walkUpdate level true previous :=
  rowScatterPrefix_complete P level previous

end PDROC.CalibrationRow
