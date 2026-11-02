module
public import Paid.PDCompute_Pack_Code_002

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDMenu.ComputeFrame PDCompute.Solver

def NoInputCode (code : List Instruction) : Prop := ∀ instruction∈code,NoInputInstruction instruction

@[simp] theorem noInput_append (first later : List Instruction) :
    NoInputCode (first++later) ↔ NoInputCode first ∧ NoInputCode later := List.forall_mem_append
@[simp] theorem noInput_cons (instruction : Instruction) (rest : List Instruction) :
    NoInputCode (instruction::rest) ↔ NoInputInstruction instruction ∧ NoInputCode rest := List.forall_mem_cons
@[simp] theorem noInput_nil : NoInputCode [] := by simp [NoInputCode]

@[simp] theorem load_noInput (slot : ℕ) (target : Register) :
    NoInputCode (PDLower.CalibrationCompute.loadSlot slot target) := by
  simp [PDLower.CalibrationCompute.loadSlot,NoInputInstruction]
@[simp] theorem store_noInput (slot : ℕ) (source : Register) :
    NoInputCode (PDLower.CalibrationCompute.storeSlot slot source) := by
  simp [PDLower.CalibrationCompute.storeSlot,NoInputInstruction]
@[simp] theorem copy_noInput (source target : ℕ) : NoInputCode (copySlot source target) := by
  simp only [copySlot,noInput_append,load_noInput,store_noInput,and_self]
@[simp] theorem add_noInput (slot value : ℕ) : NoInputCode (addNatSlot slot value) := by
  simp [addNatSlot,NoInputInstruction]
@[simp] theorem writeSlots_noInput (slots : List ℕ) : NoInputCode (writeSlots slots) := by
  induction slots with
  | nil => simp only [writeSlots,List.flatMap_nil,noInput_nil]
  | cons slot slots ih =>
    simp only [writeSlots] at ih
    simp only [writeSlots,List.flatMap_cons,noInput_append,load_noInput,
      noInput_cons,NoInputInstruction,noInput_nil,ih,and_self]
@[simp] theorem denseRead_noInput (start count : ℕ) : NoInputCode (denseReadBlockCode start count) := by
  induction count generalizing start with
  | zero => simp only [denseReadBlockCode,noInput_nil]
  | succ count ih => simp [denseReadBlockCode,denseReadCellCode,NoInputInstruction,ih]
@[simp] theorem decrement_noInput (slot : ℕ) : NoInputCode (decrementSlot slot) := by
  simp [decrementSlot,NoInputInstruction]
@[simp] theorem initialize_noInput : NoInputCode initializeCode := by
  simp [initializeCode,NoInputInstruction]
@[simp] theorem startRow_noInput : NoInputCode startRowCode := by
  simp [startRowCode]
@[simp] theorem readEntry_noInput : NoInputCode readEntryCode := by
  simp [readEntryCode,NoInputInstruction]
@[simp] theorem return_noInput : NoInputCode returnCode := by
  simp [returnCode,NoInputInstruction]

theorem serializerCode_noInput (origin : ℕ) :
    ∀ instruction∈serializerCode origin, NoInputInstruction instruction := by
  change NoInputCode (serializerCode origin)
  simp [serializerCode,NoInputInstruction]

theorem row_test_fetch (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (serializerCode origin)) :
    program[origin+66]?=some (.branchZero .index (origin+222) (origin+67)) :=
  (fetched 66 (by rw [serializerCode_length];omega)).trans (by
    simp [serializerCode,List.getElem_append,initializeCode_length,startRowCode_length,readEntryCode_length,
      returnCode,writeSlots_length,decrementSlot_length,PDLower.CalibrationCompute.loadSlot,PDLower.CalibrationCompute.storeSlot])

theorem column_test_fetch (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (serializerCode origin)) :
    program[origin+88]?=some (.branchZero .index (origin+213) (origin+89)) :=
  (fetched 88 (by rw [serializerCode_length];omega)).trans (by
    simp [serializerCode,List.getElem_append,initializeCode_length,startRowCode_length,readEntryCode_length,
      returnCode,writeSlots_length,decrementSlot_length,PDLower.CalibrationCompute.loadSlot,PDLower.CalibrationCompute.storeSlot])

theorem entry_test_fetch (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (serializerCode origin)) :
    program[origin+139]?=some (.branchZero .value (origin+165) (origin+140)) :=
  (fetched 139 (by rw [serializerCode_length];omega)).trans (by
    simp [serializerCode,List.getElem_append,initializeCode_length,startRowCode_length,readEntryCode_length,
      returnCode,writeSlots_length,decrementSlot_length,PDLower.CalibrationCompute.loadSlot,PDLower.CalibrationCompute.storeSlot])

theorem short_entry_jump_fetch (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (serializerCode origin)) :
    program[origin+164]?=some (.jump (origin+201)) :=
  (fetched 164 (by rw [serializerCode_length];omega)).trans (by
    simp [serializerCode,List.getElem_append,initializeCode_length,startRowCode_length,readEntryCode_length,
      returnCode,writeSlots_length,decrementSlot_length,PDLower.CalibrationCompute.loadSlot,PDLower.CalibrationCompute.storeSlot])

theorem column_back_fetch (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (serializerCode origin)) :
    program[origin+212]?=some (.jump (origin+85)) :=
  (fetched 212 (by rw [serializerCode_length];omega)).trans (by
    simp [serializerCode,List.getElem_append,initializeCode_length,startRowCode_length,readEntryCode_length,
      returnCode,writeSlots_length,decrementSlot_length,PDLower.CalibrationCompute.loadSlot,PDLower.CalibrationCompute.storeSlot])

theorem row_back_fetch (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (serializerCode origin)) :
    program[origin+221]?=some (.jump (origin+63)) :=
  (fetched 221 (by rw [serializerCode_length];omega)).trans (by
    simp [serializerCode,List.getElem_append,initializeCode_length,startRowCode_length,readEntryCode_length,
      returnCode,writeSlots_length,decrementSlot_length,PDLower.CalibrationCompute.loadSlot,PDLower.CalibrationCompute.storeSlot])

theorem indirect_return_fetch (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (serializerCode origin)) :
    program[origin+232]?=some (.jumpIndirect .old) :=
  (fetched 232 (by rw [serializerCode_length];omega)).trans (by
    simp [serializerCode,List.getElem_append,initializeCode_length,startRowCode_length,readEntryCode_length,
      returnCode,writeSlots_length,decrementSlot_length,PDLower.CalibrationCompute.loadSlot,PDLower.CalibrationCompute.storeSlot])

end PDCompute.Pack
