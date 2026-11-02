module

public import Structure.PA06_A19Prepare_CodeFit052_Program

set_option autoImplicit false
set_option warningAsError true

/-! The actual532/135/24 suffix, in one containing program and with one
global implicit HALT. All labels use the real containing prefix length.
Candidate until strict validation. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompletion060

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

def metadataRight (start : Nat) : List PackingOp :=
  PA06A19PrepareInitialUsed037.programAt (start + 532) ++ PA06A19PrepareFinalHeader033.program

def tail (start : Nat) : List PackingOp :=
  PA06A19PrepareStaticMetadata036.metadataProgramAt start ++ metadataRight start

def program (left : List PackingOp) : List PackingOp := left ++ tail left.length

def usedLeft (left : List PackingOp) : List PackingOp :=
  left ++ PA06A19PrepareStaticMetadata036.metadataProgramAt left.length

def headerLeft (left : List PackingOp) : List PackingOp :=
  usedLeft left ++ PA06A19PrepareInitialUsed037.programAt (left.length + 532)

theorem usedLeft_length (left : List PackingOp) : (usedLeft left).length = left.length + 532 := by
  simp only [usedLeft, List.length_append, PA06A19PrepareStaticMetadata036.metadataProgramAt_length]

theorem headerLeft_length (left : List PackingOp) : (headerLeft left).length = left.length + 667 := by
  simp only [headerLeft, List.length_append, usedLeft_length, PA06A19PrepareInitialUsed037.programAt_length]

theorem tail_length (start : Nat) : (tail start).length = 691 := by
  simp only [tail, metadataRight, List.length_append,
    PA06A19PrepareStaticMetadata036.metadataProgramAt_length,
    PA06A19PrepareInitialUsed037.programAt_length, PA06A19PrepareFinalHeader033.program_length]

theorem program_length (left : List PackingOp) : (program left).length = left.length + 691 := by
  rw [program, List.length_append, tail_length]

theorem metadata_layout (left : List PackingOp) :
    left ++ PA06A19PrepareStaticMetadata036.metadataProgramAt left.length ++ metadataRight left.length =
      program left := by
  simp only [program, tail, List.append_assoc]

theorem used_layout (left : List PackingOp) :
    usedLeft left ++ PA06A19PrepareInitialUsed037.programAt (usedLeft left).length ++
      PA06A19PrepareFinalHeader033.program = program left := by
  rw [usedLeft_length]
  simp only [usedLeft, program, tail, metadataRight, List.append_assoc]

theorem header_layout (left : List PackingOp) :
    headerLeft left ++ PA06A19PrepareFinalHeader033.program ++ [] = program left := by
  simp only [headerLeft, usedLeft, program, tail, metadataRight, List.append_nil, List.append_assoc]

def builderFront : List PackingOp :=
  PA06A19PrepareCodeFit052.positivePrefix ++ PA06A19PrepareCodeFit052.builderProgram

theorem builderFront_length : builderFront.length = PA06A19PrepareCodeFit052.builderEnd :=
  PA06A19PrepareCodeFit052.metadata_entry_label

theorem builder_layout :
    PA06A19PrepareCodeFit052.positivePrefix ++
      PSTRBuildLower.CounterInit.builderCode PA06A19PrepareCodeFit052.positivePrefix.length ++
      PA06A19PrepareCodeFit052.afterBuilder = PA06A19PrepareCodeFit052.positiveProgram := by
  rw [PA06A19PrepareCodeFit052.positivePrefix_length]
  simpa only [PA06A19PrepareCodeFit052.positiveTail, PA06A19PrepareCodeFit052.builderProgram,
    List.append_assoc] using PA06A19PrepareCodeFit052.positive_layout

theorem selected_program : program builderFront = PA06A19PrepareCodeFit052.positiveProgram := by
  rw [← PA06A19PrepareCodeFit052.positive_layout]
  unfold program tail metadataRight
  rw [builderFront_length]
  simp only [PA06A19PrepareCodeFit052.positiveTail, PA06A19PrepareCodeFit052.afterBuilder,
    PA06A19PrepareCodeFit052.metadataSegment, PA06A19PrepareCodeFit052.usedSegment,
    PA06A19PrepareCodeFit052.finalSegment, builderFront, List.append_assoc]

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompletion060
