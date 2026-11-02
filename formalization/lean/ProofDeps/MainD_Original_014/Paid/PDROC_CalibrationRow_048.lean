module

public import Paid.PDROC_CalibrationRow_045
public import Paid.PDROC_CalibrationRow_042

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- A reset writes its target header only at prefix4. Before that, in
particular during stepStart, the old clock remains the caller's Cell. -/
theorem constantSlot_heap_live_prefix (input : List Cell) (before state : State)
    (base offset count : ℕ) (value : Cell) (fresh : before.register .fresh=.natural base)
    (bound : count≤4)
    (run : linearExecute input ((constantSlot offset value).take count) before=some state) :
    state.heap=(if count<4 then before.heap else Function.update before.heap (base+offset) value) ∧
    state.live=(if count<4 then before.live else insert (base+offset) before.live) := by
  by_cases early : count<4
  · rw [constantCode_decompose,List.take_append_of_le_length (by change count≤3; omega)] at run
    simpa only [early,ite_true] using static_prefix_heap_live input _ before state
      (constantPrefix_static ∅ offset value) count run
  · have equal : count=4 := by omega
    subst count
    change linearExecute input (constantSlot offset value) before=some state at run
    have same := Option.some.inj ((constantSlot_execute input before base offset value fresh).symm.trans run)
    subst state
    simpa only [show ¬(4 : ℕ)<4 from by decide,ite_false] using
      And.intro (constantSlot_heap before base offset value) (constantSlot_live before base offset value)

theorem gate_heap_live_prefix (input : List Cell) (before state : State) (a b count : ℕ)
    (run : linearExecute input ((gateCode a b).take count) before=some state) :
    state.heap=before.heap ∧ state.live=before.live := by
  have frame := gate_prefix_frames ∅ input before a b count state run
  exact ⟨funext (fun address => frame.1 address (by simp)),
    Finset.ext (fun address => frame.2 address (by simp))⟩

/-- Actual natural clock/cursor/pointers at each successful stepNext
prefix. The old clock is retained separately from the header clock;
between prefixes17 and19 both pointer headers really equal old write. -/
theorem stepNext_prefix_slots (input : List Cell) (P : Parameters) (base level clock read write count : ℕ)
    (before state : State) (data : RowControl P base level clock (2*level+1) read write before)
    (bound : count≤20)
    (run : linearExecute input ((basicBlock .stepNext).body.take count) before=some state) :
    state.heap (base+6)=.natural (if count<8 then clock else clock+1) ∧
    state.heap (base+7)=.natural (2*level+1) ∧ state.heap (base+8)=.natural (2*level+1) ∧
    state.heap (base+9)=.natural (if count<17 then read else write) ∧
    state.heap (base+10)=.natural (if count<20 then write else read) := by
  have heap := (stepNext_heap_live_prefix input before state base clock read write count data.header.fresh
    (data.header.live 6 (by decide)) data.clockValue (data.header.live 9 (by decide))
    (data.header.live 10 (by decide)) data.read data.write bound run).1
  rw [heap]
  by_cases early : count<8
  · have middle : count<17 := by omega
    have late : count<20 := by omega
    simp only [early,middle,late,ite_true,data.clockValue,data.cursorValue,data.width,data.read,data.write,true_and]
  · by_cases middle : count<17
    · have late : count<20 := by omega
      simp [early,middle,late,data.cursorValue,data.width,data.read,data.write]
    · by_cases late : count<20
      · simp [early,middle,late,data.cursorValue,data.width,data.write]
      · simp [early,middle,late,data.cursorValue,data.width]

theorem stepNext_prefix_both_rows (input : List Cell) (P : Parameters) (base level clock read write count : ℕ)
    (before state : State) (data : ScatterData P base level clock (2*level+1) read write before)
    (newRow : RowAt before write (P.walkRow level true (clock+1)))
    (run : linearExecute input ((basicBlock .stepNext).body.take count) before=some state) :
    RowAt state read (P.walkRow level true clock) ∧ RowAt state write (P.walkRow level true (clock+1)) := by
  have lower := Buffers.lower base P.certificate.M read write data.control.buffers
  exact ⟨stepNext_prefix_row input before base clock read data.control.header.fresh
      (data.control.header.live 6 (by decide)) data.control.clockValue
      (data.control.header.live 9 (by decide)) (data.control.header.live 10 (by decide))
      _ data.readRow lower.1 count state run,
    stepNext_prefix_row input before base clock write data.control.header.fresh
      (data.control.header.live 6 (by decide)) data.control.clockValue
      (data.control.header.live 9 (by decide)) (data.control.header.live 10 (by decide))
      _ newRow lower.2 count state run⟩

end PDROC.CalibrationRow
