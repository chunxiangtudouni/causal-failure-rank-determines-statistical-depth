module
public import Paid.PDCompute_Pack_Code_002

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (loadSlot storeSlot)

def rowTestCode (origin : ℕ) : List Instruction :=
  loadSlot rowRemaining .index++[.branchZero .index (origin+222) (origin+67)]
def columnTestCode (origin : ℕ) : List Instruction :=
  loadSlot columnRemaining .index++[.branchZero .index (origin+213) (origin+89)]
def tagTestCode (origin : ℕ) : List Instruction := [.branchZero .value (origin+165) (origin+140)]
def shortBranchCode (origin : ℕ) : List Instruction := writeSlots [24,27,28,29]++[.jump (origin+201)]
def testBranchCode : List Instruction := writeSlots [24,25,26,27,28,29]
def entryAdvanceCode (origin : ℕ) : List Instruction :=
  storeSlot outputCursor .old++decrementSlot columnRemaining++[.jump (origin+85)]
def rowAdvanceCode (origin : ℕ) : List Instruction := decrementSlot rowRemaining++[.jump (origin+63)]

theorem rowTest_length (origin : ℕ) : (rowTestCode origin).length=4 := rfl
theorem columnTest_length (origin : ℕ) : (columnTestCode origin).length=4 := rfl
theorem tagTest_length (origin : ℕ) : (tagTestCode origin).length=1 := rfl
theorem shortBranch_length (origin : ℕ) : (shortBranchCode origin).length=25 := rfl
theorem testBranch_length : testBranchCode.length=36 := rfl
theorem entryAdvance_length (origin : ℕ) : (entryAdvanceCode origin).length=12 := rfl
theorem rowAdvance_length (origin : ℕ) : (rowAdvanceCode origin).length=9 := rfl

theorem serializer_decompose (origin : ℕ) : serializerCode origin=
    initializeCode++rowTestCode origin++startRowCode++columnTestCode origin++readEntryCode++tagTestCode origin++
    shortBranchCode origin++testBranchCode++entryAdvanceCode origin++rowAdvanceCode origin++returnCode := by
  simp only [serializerCode,rowTestCode,columnTestCode,tagTestCode,shortBranchCode,testBranchCode,
    entryAdvanceCode,rowAdvanceCode,List.append_assoc]

theorem fetch_initialize (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (serializerCode origin)) : FetchesCode program origin initializeCode := by
  rw [serializer_decompose] at fetched
  simp only [List.append_assoc] at fetched
  exact fetched.append_left

theorem fetch_rowTest (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (serializerCode origin)) : FetchesCode program (origin+63) (rowTestCode origin) := by
  rw [serializer_decompose] at fetched
  simp only [List.append_assoc] at fetched
  simpa only [initializeCode_length] using fetched.append_right.append_left

theorem fetch_startRow (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (serializerCode origin)) : FetchesCode program (origin+67) startRowCode := by
  rw [serializer_decompose] at fetched
  simp only [List.append_assoc] at fetched
  simpa only [initializeCode_length,rowTest_length,Nat.add_assoc] using
    fetched.append_right.append_right.append_left

theorem fetch_columnTest (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (serializerCode origin)) : FetchesCode program (origin+85) (columnTestCode origin) := by
  rw [serializer_decompose] at fetched
  simp only [List.append_assoc] at fetched
  simpa only [initializeCode_length,rowTest_length,startRowCode_length,Nat.add_assoc] using
    fetched.append_right.append_right.append_right.append_left

theorem fetch_readEntry (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (serializerCode origin)) : FetchesCode program (origin+89) readEntryCode := by
  rw [serializer_decompose] at fetched
  simp only [List.append_assoc] at fetched
  simpa only [initializeCode_length,rowTest_length,startRowCode_length,columnTest_length,Nat.add_assoc] using
    fetched.append_right.append_right.append_right.append_right.append_left

theorem fetch_tagTest (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (serializerCode origin)) : FetchesCode program (origin+139) (tagTestCode origin) := by
  rw [serializer_decompose] at fetched
  simp only [List.append_assoc] at fetched
  simpa only [initializeCode_length,rowTest_length,startRowCode_length,columnTest_length,readEntryCode_length,Nat.add_assoc] using
    fetched.append_right.append_right.append_right.append_right.append_right.append_left

theorem fetch_shortBranch (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (serializerCode origin)) : FetchesCode program (origin+140) (shortBranchCode origin) := by
  rw [serializer_decompose] at fetched
  simp only [List.append_assoc] at fetched
  simpa only [initializeCode_length,rowTest_length,startRowCode_length,columnTest_length,readEntryCode_length,
    tagTest_length,Nat.add_assoc] using
    fetched.append_right.append_right.append_right.append_right.append_right.append_right.append_left

theorem fetch_testBranch (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (serializerCode origin)) : FetchesCode program (origin+165) testBranchCode := by
  rw [serializer_decompose] at fetched
  simp only [List.append_assoc] at fetched
  simpa only [initializeCode_length,rowTest_length,startRowCode_length,columnTest_length,readEntryCode_length,
    tagTest_length,shortBranch_length,Nat.add_assoc] using
    fetched.append_right.append_right.append_right.append_right.append_right.append_right.append_right.append_left

theorem fetch_entryAdvance (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (serializerCode origin)) : FetchesCode program (origin+201) (entryAdvanceCode origin) := by
  rw [serializer_decompose] at fetched
  simp only [List.append_assoc] at fetched
  simpa only [initializeCode_length,rowTest_length,startRowCode_length,columnTest_length,readEntryCode_length,
    tagTest_length,shortBranch_length,testBranch_length,Nat.add_assoc] using
    fetched.append_right.append_right.append_right.append_right.append_right.append_right.append_right.append_right.append_left

theorem fetch_rowAdvance (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (serializerCode origin)) : FetchesCode program (origin+213) (rowAdvanceCode origin) := by
  rw [serializer_decompose] at fetched
  simp only [List.append_assoc] at fetched
  simpa only [initializeCode_length,rowTest_length,startRowCode_length,columnTest_length,readEntryCode_length,
    tagTest_length,shortBranch_length,testBranch_length,entryAdvance_length,Nat.add_assoc] using
    fetched.append_right.append_right.append_right.append_right.append_right.append_right.append_right.append_right.append_right.append_left

theorem fetch_return (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (serializerCode origin)) : FetchesCode program (origin+222) returnCode := by
  rw [serializer_decompose] at fetched
  simp only [List.append_assoc] at fetched
  simpa only [initializeCode_length,rowTest_length,startRowCode_length,columnTest_length,readEntryCode_length,
    tagTest_length,shortBranch_length,testBranch_length,entryAdvance_length,rowAdvance_length,Nat.add_assoc] using
    fetched.append_right.append_right.append_right.append_right.append_right.append_right.append_right.append_right.append_right.append_right

end PDCompute.Pack
