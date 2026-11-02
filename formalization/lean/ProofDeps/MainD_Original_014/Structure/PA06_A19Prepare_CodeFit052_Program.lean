module

public import Structure.PA06_A19Prepare_CodeFit052_Builder
public import Structure.PA06_A19Prepare_PreBuild044_Layout
public import Structure.PA06_A19Prepare_StaticMetadata036_MetadataRun
public import Structure.PA06_A19Prepare_InitialUsed037
public import Structure.PA06_A19Prepare_FinalHeader033

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED definition and exact boundaries of ONE positive-q program.
No dimension, schedule, tree, heap or strategy is an argument to this code.
The sole terminal HALT is added by packingCode after the entire list. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCodeFit052

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

def metadataSegment : List PackingOp :=
  PA06A19PrepareStaticMetadata036.metadataProgramAt builderEnd

def usedSegment : List PackingOp :=
  PA06A19PrepareInitialUsed037.programAt (builderEnd + 532)

def finalSegment : List PackingOp := PA06A19PrepareFinalHeader033.program

def afterBuilder : List PackingOp := metadataSegment ++ usedSegment ++ finalSegment

def positiveTail : List PackingOp := builderProgram ++ afterBuilder

def positiveProgram : List PackingOp := PA06A19PreparePreBuild044.program positiveTail

/-- This prefix includes the actual whole-program-length dispatcher value.
It is not the prefix for program [] or for a different future tail. -/
def positivePrefix : List PackingOp :=
  PA06A19PreparePreBuild044.rawFront positiveTail ++
    PA06A19PrepareChildrenCache023.programAt 1444 ++
    PA06A19PrepareClearVM045.programAt 1588

theorem metadataSegment_length : metadataSegment.length = 532 :=
  PA06A19PrepareStaticMetadata036.metadataProgramAt_length builderEnd

theorem usedSegment_length : usedSegment.length = 135 :=
  PA06A19PrepareInitialUsed037.programAt_length (builderEnd + 532)

theorem finalSegment_length : finalSegment.length = 24 :=
  PA06A19PrepareFinalHeader033.program_length

theorem afterBuilder_length : afterBuilder.length = 691 := by
  simp only [afterBuilder, List.length_append, metadataSegment_length,
    usedSegment_length, finalSegment_length]

theorem positivePrefix_length : positivePrefix.length = 1639 := by
  simp only [positivePrefix, List.length_append,
    PA06A19PreparePreBuild044.rawFront_length,
    PA06A19PrepareChildrenCache023.programAt_length,
    PA06A19PrepareClearVM045.programAt_length]

theorem positive_layout : positivePrefix ++ positiveTail = positiveProgram := by
  have layout := PA06A19PreparePreBuild044.clear_layout positiveTail
  rw [PA06A19PreparePreBuild044.clearFront_length] at layout
  simpa only [positivePrefix, PA06A19PreparePreBuild044.clearFront,
    positiveProgram, List.append_assoc] using layout

theorem positiveProgram_length : positiveProgram.length = builderEnd + 691 := by
  simp only [positiveProgram, PA06A19PreparePreBuild044.program_length,
    positiveTail, List.length_append, afterBuilder_length, builderEnd]
  omega

theorem positiveProgram_length_from_builder :
    positiveProgram.length = 2330 + builderProgram.length := by
  rw [positiveProgram_length, builderEnd]
  omega

theorem positive_code_length :
    (packingCode positiveProgram).length = 5 * (builderEnd + 691) + 5 := by
  rw [packingCode_length, positiveProgram_length]

/-- Exact entry labels consumed by the actual metadata and used producers. -/
theorem metadata_entry_label :
    (positivePrefix ++ builderProgram).length = builderEnd := by
  rw [List.length_append, positivePrefix_length]
  rfl

theorem used_entry_label :
    ((positivePrefix ++ builderProgram) ++ metadataSegment).length = builderEnd + 532 := by
  rw [List.length_append, metadata_entry_label, metadataSegment_length]

theorem header_entry_label :
    (((positivePrefix ++ builderProgram) ++ metadataSegment) ++ usedSegment).length =
      builderEnd + 667 := by
  rw [List.length_append, used_entry_label, usedSegment_length]

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCodeFit052
