module

public import Paid.PDROC_CalibrationRow_028
public import Paid.PDROC_CalibrationRow_Init_SafeSegment_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CalibrationRow.ZeroRuntime

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

theorem zeroPrelude_static (region : Finset ℕ) :
    ∀ instruction∈zeroWritePrefixCode,∀ state,WritesWithin region instruction state := by
  intro instruction member state
  simp only [zeroWritePrefixCode,loadSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (h|h|h)|(h|h) <;> subst instruction <;> trivial

theorem incrementPrelude_static (region : Finset ℕ) :
    ∀ instruction∈initIncrementPrefixCode 7,∀ state,WritesWithin region instruction state := by
  intro instruction member state
  simp only [initIncrementPrefixCode,loadSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (h|h|h)|(h|h|h|h) <;> subst instruction <;> trivial

/-- Exact heap/live snapshots at EVERY literal zeroCell prefix. Prefix6
has written the new zero row cell, while header7 remains the old cursor
through prefix13. Only prefix14 stores cursor+1. No old suffix contents
or liveness are provided as an input assumption. -/
theorem zeroCell_heap_live_prefix (input : List Cell) (P : Parameters)
    (base level clock cursor read write : ℕ) (previous : Array ℚ) (before state : State)
    (data : ZeroData P base level clock cursor read write previous before)
    (index : before.register .index=.natural cursor) (count : ℕ) (bound : count≤14)
    (run : linearExecute input ((basicBlock .zeroCell).body.take count) before=some state) :
    state.heap=(if count<6 then before.heap else if count<14 then
      Function.update before.heap (write+cursor) (.rational 0) else
      Function.update (Function.update before.heap (write+cursor) (.rational 0)) (base+7) (.natural (cursor+1))) ∧
    state.live=(if count<6 then before.live else if count<14 then insert (write+cursor) before.live else
      insert (base+7) (insert (write+cursor) before.live)) := by
  by_cases early : count<6
  · have first : count≤zeroWriteCode.length := by change count≤6; omega
    have prelude : count≤zeroWritePrefixCode.length := by change count≤5; omega
    rw [zeroCell_decompose,List.take_append_of_le_length first,zeroWrite_decompose,
      List.take_append_of_le_length prelude] at run
    have frame := LinearFrames.of_static (∅ : Finset ℕ) input zeroWritePrefixCode
      (zeroPrelude_static _) before count state run
    have heap : state.heap=before.heap := funext (fun address => frame.1 address (by simp))
    have live : state.live=before.live := Finset.ext (fun address => frame.2 address (by simp))
    simpa only [early,ite_true] using And.intro heap live
  · by_cases middle : count<14
    · rw [zeroCell_decompose,List.take_append,
        List.take_of_length_le (by change 6≤count; omega),linearExecute_append,
        zeroWrite_execute input before base write cursor data.header.fresh (data.header.live 10 (by decide))
          data.writeValue index,Option.bind_some] at run
      change linearExecute input ((incrementSlot 7).take (count-6)) (zeroWriteResult before base write cursor)=some state at run
      have code : incrementSlot 7=initIncrementPrefixCode 7++[.store .address .index] := rfl
      have prelude : count-6≤(initIncrementPrefixCode 7).length := by change count-6≤7; omega
      rw [code,List.take_append_of_le_length prelude] at run
      have frame := LinearFrames.of_static (∅ : Finset ℕ) input (initIncrementPrefixCode 7)
        (incrementPrelude_static _) (zeroWriteResult before base write cursor) (count-6) state run
      have heap : state.heap=(zeroWriteResult before base write cursor).heap :=
        funext (fun address => frame.1 address (by simp))
      have live : state.live=(zeroWriteResult before base write cursor).live :=
        Finset.ext (fun address => frame.2 address (by simp))
      have fields := zeroWrite_fields before base write cursor
      simpa only [early,ite_false,middle,ite_true] using And.intro (heap.trans fields.1) (live.trans fields.2.1)
    · have equal : count=14 := by omega
      subst count
      change linearExecute input (basicBlock .zeroCell).body before=some state at run
      have whole := zeroCell_execute input P before base level read write cursor data.header data.buffers
        data.writeValue data.cursorValue index
      have same := Option.some.inj (whole.symm.trans run)
      subst state
      have fields := zeroCell_fields before base write cursor
      simpa only [show ¬(14 : ℕ)<6 from by decide,show ¬(14 : ℕ)<14 from by decide,ite_false] using
        And.intro fields.1 fields.2.1

end PDROC.CalibrationRow.ZeroRuntime
