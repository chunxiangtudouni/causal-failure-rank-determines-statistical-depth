module

public import Paid.PDROC_CalibrationRow_022
public import Paid.PDROC_CalibrationRow_015

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid.Computation PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- Every actual letter-store prefix retains the true header clock and
the original source cursor, even when .index has become a target index. -/
theorem scatterStore_prefix_header (input : List Cell) (before : State)
    (base M read write target : ℕ) (previous amount : ℚ)
    (buffers : Buffers base M read write)
    (fresh : before.register .fresh=.natural base)
    (pointerLive : base+10 ∈ before.live) (pointer : before.heap (base+10)=.natural write)
    (index : before.register .index=.natural target) (value : before.register .value=.rational amount)
    (cellLive : write+target ∈ before.live) (cell : before.heap (write+target)=.rational previous)
    (count : ℕ) (state : State)
    (run : linearExecute input (scatterStoreCode.take count) before=some state) :
    ∀ offset<16,state.heap (base+offset)=before.heap (base+offset) := by
  have actual := scatterStore_execute input before base write target previous amount fresh pointerLive pointer index value cellLive cell
  rw [scatterStore_decompose] at actual run
  have memory := single_last_prefix_memory input scatterStorePrefixCode (.store .address .value) before
    (scatterStoreResult before base write target previous amount) (by
      intro instruction member state
      simp only [scatterStorePrefixCode,loadSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with (h|h|h)|(h|h|h) <;> subst instruction <;> trivial) actual count state run
  intro offset bound
  rcases memory with unchanged|equal
  · exact empty_frame_slot before state (base+offset) unchanged
  · subst state
    rw [(scatterStore_fields before base write target previous amount).1]
    exact Function.update_of_ne
      (Ne.symm (Buffers.write_header_ne base M read write target offset buffers bound)) _ _

theorem scatterStore_preserves_read (before : State) (base M read write target : ℕ)
    (previous amount : ℚ) (row : Array ℚ) (represented : RowAt before read row)
    (buffers : Buffers base M read write) (targetBound : target<rowWidth M) (size : row.size≤rowWidth M) :
    RowAt (scatterStoreResult before base write target previous amount) read row := by
  have fields := scatterStore_fields before base write target previous amount
  constructor
  · intro i inside
    rw [fields.2.1]
    exact Finset.mem_insert_of_mem (represented.live i inside)
  · intro i inside
    rw [fields.1,Function.update_of_ne
      (Buffers.separate base M read write buffers i target (by omega) targetBound)]
    exact represented.value i inside

end PDROC.CalibrationRow
