module

public import Paid.PDROC_CalibrationRow_039
public import Paid.PDROC_CalibrationRow_Init_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid.Computation PDLower.CalibrationCompute PDMenu.ComputeFrame

def headerStorePrefixCode (offset : ℕ) : List Instruction :=
  [.constant .address (.natural offset),.natOp .add .address .fresh .address]

theorem headerStore_decompose (offset : ℕ) (source : Register) :
    storeSlot offset source=headerStorePrefixCode offset++[.store .address source] := rfl

theorem headerStore_prefix_frames (region : Finset ℕ) (input : List Cell) (before : State)
    (base offset : ℕ) (source : Register) (fresh : before.register .fresh=.natural base)
    (safe : source≠.address) (inside : base+offset ∈ region) :
    LinearFrames region input (storeSlot offset source) before := by
  rw [headerStore_decompose]
  apply single_last_frames region input (headerStorePrefixCode offset) (.store .address source)
    before (storeSlotResult before base offset source)
  · intro instruction member state
    simp only [headerStorePrefixCode,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h <;> subst instruction <;> trivial
  · rw [←headerStore_decompose]
    exact storeSlot_execute input before base offset source fresh safe
  · exact frame_of_one_update region before _ (base+offset) (before.register source) inside rfl rfl

theorem loadSlot_prefix_frames (region : Finset ℕ) (input : List Cell) (before : State)
    (offset : ℕ) (target : Register) : LinearFrames region input (loadSlot offset target) before := by
  apply LinearFrames.of_static
  intro instruction member state
  simp only [loadSlot,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h <;> subst instruction <;> trivial

/-- The body really writes only header6,9,10. Header7 and BOTH fixed
physical row regions remain unchanged at EVERY actual prefix, including
the interval with coinciding header pointers between the two stores. -/
theorem stepNext_prefix_frames (region : Finset ℕ) (input : List Cell) (before : State) (base clock : ℕ)
    (fresh : before.register .fresh=.natural base)
    (clockLive : base+6 ∈ before.live) (clockValue : before.heap (base+6)=.natural clock)
    (readLive : base+9 ∈ before.live) (writeLive : base+10 ∈ before.live)
    (clockInside : base+6 ∈ region) (readInside : base+9 ∈ region) (writeInside : base+10 ∈ region) :
    LinearFrames region input (basicBlock .stepNext).body before := by
  let incremented := incrementSlotResult before base 6 clock
  let readLoaded := loadSlotResult incremented base 9 .old
  let writeLoaded := loadSlotResult readLoaded base 10 .total
  let readStored := storeSlotResult writeLoaded base 9 .total
  have incFresh := (incrementSlot_fresh before base 6 clock).trans fresh
  have readFresh : readLoaded.register .fresh=.natural base := by
    simpa [readLoaded,loadSlotResult] using incFresh
  have writeFresh : writeLoaded.register .fresh=.natural base := by
    simpa [writeLoaded,loadSlotResult] using readFresh
  have storedFresh : readStored.register .fresh=.natural base := by
    simpa [readStored,storeSlotResult] using writeFresh
  have readRun := loadSlot_execute input incremented base 9 .old incFresh
    (show base+9 ∈ incremented.live from Finset.mem_insert_of_mem readLive)
  have writeRun := loadSlot_execute input readLoaded base 10 .total readFresh
    (show base+10 ∈ readLoaded.live from Finset.mem_insert_of_mem writeLive)
  have storeRun := storeSlot_execute input writeLoaded base 9 .total writeFresh (by decide)
  have tail3 := LinearFrames.append region input (storeSlot 9 .total) (storeSlot 10 .old)
    writeLoaded readStored storeRun
    (headerStore_prefix_frames region input writeLoaded base 9 .total writeFresh (by decide) readInside)
    (headerStore_prefix_frames region input readStored base 10 .old storedFresh (by decide) writeInside)
  have tail2 := LinearFrames.append region input (loadSlot 10 .total) (storeSlot 9 .total++storeSlot 10 .old)
    readLoaded writeLoaded writeRun (loadSlot_prefix_frames region input readLoaded 10 .total) tail3
  have tail1 := LinearFrames.append region input (loadSlot 9 .old)
    (loadSlot 10 .total++(storeSlot 9 .total++storeSlot 10 .old)) incremented readLoaded readRun
    (loadSlot_prefix_frames region input incremented 9 .old) tail2
  have whole := LinearFrames.append region input (incrementSlot 6)
    (loadSlot 9 .old++(loadSlot 10 .total++(storeSlot 9 .total++storeSlot 10 .old))) before incremented
    (incrementSlot_execute input before base 6 clock fresh clockLive clockValue)
    (incrementSlot_prefix_frames region input before base 6 clock fresh clockLive clockValue clockInside) tail1
  simpa only [stepNext_body,List.append_assoc] using whole

theorem stepNext_prefix_row (input : List Cell) (before : State) (base clock rowBase : ℕ)
    (fresh : before.register .fresh=.natural base)
    (clockLive : base+6 ∈ before.live) (clockValue : before.heap (base+6)=.natural clock)
    (readLive : base+9 ∈ before.live) (writeLive : base+10 ∈ before.live)
    (row : Array ℚ) (represented : RowAt before rowBase row) (rowLower : base+16≤rowBase)
    (count : ℕ) (state : State)
    (run : linearExecute input ((basicBlock .stepNext).body.take count) before=some state) :
    RowAt state rowBase row := by
  let onlyHeader : Finset ℕ := {base+6,base+9,base+10}
  have frame := stepNext_prefix_frames onlyHeader input before base clock fresh clockLive clockValue readLive writeLive
    (by simp [onlyHeader]) (by simp [onlyHeader]) (by simp [onlyHeader]) count state run
  have outside (i : ℕ) : rowBase+i ∉ onlyHeader := by
    simp only [onlyHeader,Finset.mem_insert,Finset.mem_singleton]
    omega
  exact ⟨fun i inside => (frame.2 (rowBase+i) (outside i)).mpr (represented.live i inside),
    fun i inside => (frame.1 (rowBase+i) (outside i)).trans (represented.value i inside)⟩

end PDROC.CalibrationRow
