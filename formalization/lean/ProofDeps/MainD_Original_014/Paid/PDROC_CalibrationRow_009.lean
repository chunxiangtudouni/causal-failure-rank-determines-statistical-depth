module

public import Paid.PDROC_CalibrationRow_006
public import Paid.PDROC_CalibrationRow_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

def levelInitResult (before : State) (base level M : ℕ) : State :=
  constantSlotResult
    (secondPointerResult (firstPointerResult (widthResult before base level) base) base M)
    base 7 (.natural 0)

theorem secondPointer_frame (before : State) (base M : ℕ) :
    MemoryFrame (region base M) before (secondPointerResult before base M) := by
  have fields := secondPointer_fields before base M
  exact frame_of_one_update (region base M) before _ (base+10) (.natural (secondRow base M))
    (header_mem_region base M 10 (by decide) (by decide)) fields.1 fields.2.1

theorem firstPointer_frame (before : State) (base M : ℕ) :
    MemoryFrame (region base M) before (firstPointerResult before base) := by
  have fields := firstPointer_fields before base
  exact frame_of_one_update (region base M) before _ (base+9) (.natural (firstRow base))
    (header_mem_region base M 9 (by decide) (by decide)) fields.1 fields.2.1

theorem constant_row_frame (before : State) (base M offset : ℕ) (value : Cell)
    (low : 6 ≤ offset) (high : offset ≤ 10) :
    MemoryFrame (region base M) before (constantSlotResult before base offset value) :=
  frame_of_one_update _ before _ _ value (header_mem_region base M offset low high)
    (constantSlot_heap before base offset value) (constantSlot_live before base offset value)

theorem levelInit_execute (input : List Cell) (P : Parameters) (before : State) (base level : ℕ)
    (header : Header P base level before) :
    linearExecute input (basicBlock .levelInit).body before =
      some (levelInitResult before base level P.certificate.M) := by
  let width := widthResult before base level
  have widthFields := widthResult_fields before base level
  have widthHeader := header.transport P base level before width
    (widthResult_frame before base level _) (by rw [widthFields.2.1]; exact Finset.subset_insert _ _)
    widthFields.2.2.1
  let first := firstPointerResult width base
  have firstFields := firstPointer_fields width base
  have firstHeader := widthHeader.transport P base level width first
    (firstPointer_frame width base _) (by rw [firstFields.2.1]; exact Finset.subset_insert _ _)
    firstFields.2.2.1
  have secondFresh := (secondPointer_fields first base P.certificate.M).2.2.1.trans firstHeader.fresh
  rw [levelInit_decompose,buffersCode_decompose,linearExecute_append,
    width_execute input before base level header.fresh (header.live 5 (by decide)) header.level,
    Option.bind_some,linearExecute_append,linearExecute_append,
    firstPointer_execute input width base widthHeader.fresh,Option.bind_some,
    secondPointer_execute input first base P.certificate.M firstHeader.fresh firstFields.2.2.2.1
      (firstHeader.live 2 (by decide)) firstHeader.M,Option.bind_some,
    constantSlot_execute input _ base 7 (.natural 0) secondFresh]
  rfl

theorem levelInit_fields (before : State) (base level M : ℕ) :
    (levelInitResult before base level M).heap =
      Function.update (Function.update (Function.update (Function.update before.heap
        (base+8) (.natural (2*level+1))) (base+9) (.natural (firstRow base)))
        (base+10) (.natural (secondRow base M))) (base+7) (.natural 0) ∧
    (levelInitResult before base level M).live =
      insert (base+7) (insert (base+10) (insert (base+9) (insert (base+8) before.live))) ∧
    (levelInitResult before base level M).register .fresh = before.register .fresh ∧
    (levelInitResult before base level M).pc = before.pc+30 ∧
    (levelInitResult before base level M).output = before.output := by
  simp only [levelInitResult,constantSlot_heap,constantSlot_live,constantSlot_fresh,
    constantSlot_pc,constantSlot_output,(secondPointer_fields _ _ _).1,
    (secondPointer_fields _ _ _).2.1,(secondPointer_fields _ _ _).2.2.1,
    (secondPointer_fields _ _ _).2.2.2.1,(secondPointer_fields _ _ _).2.2.2.2,
    (firstPointer_fields _ _).1,(firstPointer_fields _ _).2.1,
    (firstPointer_fields _ _).2.2.1,(firstPointer_fields _ _).2.2.2.2.1,
    (firstPointer_fields _ _).2.2.2.2.2,(widthResult_fields _ _ _).1,
    (widthResult_fields _ _ _).2.1,(widthResult_fields _ _ _).2.2.1,
    (widthResult_fields _ _ _).2.2.2.2.1,(widthResult_fields _ _ _).2.2.2.2.2,
    Nat.add_assoc]
  trivial

theorem levelInit_frame (before : State) (base level M : ℕ) :
    MemoryFrame (region base M) before (levelInitResult before base level M) :=
  (widthResult_frame before base level M).trans
    ((firstPointer_frame _ base M).trans ((secondPointer_frame _ base M).trans
      (constant_row_frame _ base M 7 (.natural 0) (by decide) (by decide))))

end PDROC.CalibrationRow
