module

public import Structure.PA06_A19Prepare_StaticMetadata036_MetadataRun
public import Structure.PA06_A19Prepare_InitialUsed037
public import Structure.PA06_A19Prepare_FinalHeader033

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED actual532/135/24 body with an arbitrary containing tail.
These layout lemmas do not execute that tail or the containing implicit
HALT. No fixed positive program, builderFront or zero-tool code is chosen. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareActiveSuffix076

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

def metadataRight (start : Nat) (right : List PackingOp) : List PackingOp :=
  PA06A19PrepareInitialUsed037.programAt (start + 532) ++
    PA06A19PrepareFinalHeader033.program ++ right

def tail (start : Nat) (right : List PackingOp) : List PackingOp :=
  PA06A19PrepareStaticMetadata036.metadataProgramAt start ++ metadataRight start right

def program (left right : List PackingOp) : List PackingOp := left ++ tail left.length right

def usedLeft (left : List PackingOp) : List PackingOp :=
  left ++ PA06A19PrepareStaticMetadata036.metadataProgramAt left.length

def headerLeft (left : List PackingOp) : List PackingOp :=
  usedLeft left ++ PA06A19PrepareInitialUsed037.programAt (left.length + 532)

theorem usedLeft_length (left : List PackingOp) : (usedLeft left).length = left.length + 532 := by
  simp only [usedLeft, List.length_append, PA06A19PrepareStaticMetadata036.metadataProgramAt_length]

theorem headerLeft_length (left : List PackingOp) : (headerLeft left).length = left.length + 667 := by
  simp only [headerLeft, List.length_append, usedLeft_length, PA06A19PrepareInitialUsed037.programAt_length]

theorem tail_length (start : Nat) (right : List PackingOp) :
    (tail start right).length = 691 + right.length := by
  simp only [tail, metadataRight, List.length_append,
    PA06A19PrepareStaticMetadata036.metadataProgramAt_length,
    PA06A19PrepareInitialUsed037.programAt_length, PA06A19PrepareFinalHeader033.program_length]
  omega

theorem program_length (left right : List PackingOp) :
    (program left right).length = left.length + 691 + right.length := by
  rw [program, List.length_append, tail_length]
  omega

theorem metadata_layout (left right : List PackingOp) :
    left ++ PA06A19PrepareStaticMetadata036.metadataProgramAt left.length ++ metadataRight left.length right =
      program left right := by
  simp only [program, tail, List.append_assoc]

theorem used_layout (left right : List PackingOp) :
    usedLeft left ++ PA06A19PrepareInitialUsed037.programAt (usedLeft left).length ++
      (PA06A19PrepareFinalHeader033.program ++ right) = program left right := by
  rw [usedLeft_length]
  simp only [usedLeft, program, tail, metadataRight, List.append_assoc]

theorem header_layout (left right : List PackingOp) :
    headerLeft left ++ PA06A19PrepareFinalHeader033.program ++ right = program left right := by
  simp only [headerLeft, usedLeft, program, tail, metadataRight, List.append_assoc]

end PaperProofs.Structure.LaminarTree.PA06A19PrepareActiveSuffix076
