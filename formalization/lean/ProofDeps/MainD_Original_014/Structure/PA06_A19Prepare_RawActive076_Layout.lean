module

public import Structure.PA06_A19Prepare_ActiveSuffix076_Program
public import Structure.PA06_A19Prepare_PostDP055

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED positive raw body in an arbitrary fixed containing tail.
The raw dispatcher's code length is computed from THIS whole program.
No old positive implicit HALT is appended, executed or transported. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareRawActive076

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

def builderEnd : Nat := 1639 + (PSTRBuildLower.CounterInit.builderCode 1639).length

def bodyTail (right : List PackingOp) : List PackingOp :=
  PA06A19PrepareActiveSuffix076.tail builderEnd right

def program (right : List PackingOp) : List PackingOp :=
  PA06A19PreparePostDP055.program (bodyTail right)

def front (right : List PackingOp) : List PackingOp :=
  PA06A19PreparePostDP055.front (bodyTail right)

def builderFront (right : List PackingOp) : List PackingOp :=
  front right ++ PSTRBuildLower.CounterInit.builderCode 1639

theorem front_length (right : List PackingOp) : (front right).length = 1639 :=
  PA06A19PreparePostDP055.front_length (bodyTail right)

theorem builderFront_length (right : List PackingOp) : (builderFront right).length = builderEnd := by
  rw [builderFront, List.length_append, front_length]
  rfl

theorem builder_layout (right : List PackingOp) :
    front right ++ PSTRBuildLower.CounterInit.builderCode (front right).length ++ bodyTail right =
      program right :=
  PA06A19PreparePostDP055.program_layout (bodyTail right)

theorem suffix_layout (right : List PackingOp) :
    PA06A19PrepareActiveSuffix076.program (builderFront right) right = program right := by
  unfold PA06A19PrepareActiveSuffix076.program
  rw [builderFront_length]
  change (front right ++ PSTRBuildLower.CounterInit.builderCode 1639) ++ bodyTail right = program right
  have layout := builder_layout right
  rw [front_length] at layout
  exact layout

theorem program_length (right : List PackingOp) :
    (program right).length = builderEnd + 691 + right.length := by
  rw [← suffix_layout, PA06A19PrepareActiveSuffix076.program_length, builderFront_length]

end PaperProofs.Structure.LaminarTree.PA06A19PrepareRawActive076
