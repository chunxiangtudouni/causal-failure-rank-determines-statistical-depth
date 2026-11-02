module

public import PaperProofs.Structure.PSTR_CountControl_050
public import PaperProofs.Structure.PSTR_NodeLeaf_047
public import PaperProofs.Structure.PSTR_CountRestore_048
public import PaperProofs.Structure.PSTR_CountMemory_051
public import PaperProofs.Structure.PSTR_CountChildRows_052
public import PaperProofs.Structure.PSTR_HD_CountProgram_029

/-! One fixed outer traversal instruction array. Every branch position is
static; no dimension, prepared answer or child row is a code parameter.
Its literal components are connected to the SAME containing instruction
array. This module alone does not prove the loop invariant or whole call. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTROuterCountCode

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

def programAt (origin : Nat) : List PackingOp :=
  PSTRParentSentinel.program ++ PSTRCountControl.testBlock (origin + 478) ++
    PSTRNodeLeaf.programAt (origin + 10) ++ PSTRCountRestore.program ++
    PSTRCountKernel.programAt (origin + 123) ++ PSTRParentCopy.program ++
    PSTRCountAdvance.program ++ PSTRCountControl.backBlock (origin + 5)

theorem programAt_length (origin : Nat) : (programAt origin).length = 478 := by
  simp only [programAt, List.length_append, PSTRParentSentinel.program_length,
    PSTRCountControl.testBlock_length, PSTRNodeLeaf.programAt_length,
    PSTRCountRestore.program_length, PSTRCountKernel.programAt_length,
    PSTRParentCopy.program_length, PSTRCountAdvance.program_length, PSTRCountControl.backBlock_length]

theorem block_index_bound (whole : List PackingOp) (start : Nat) (block : List PackingOp)
    (hbound : start + block.length ≤ whole.length) (index : Nat) (hi : index < block.length) :
    start + index < whole.length := by omega

structure BlockAt (whole : List PackingOp) (start : Nat) (block : List PackingOp) : Prop where
  bound : start + block.length ≤ whole.length
  code : ∀ i (hi : i < block.length), whole[start + i]'(block_index_bound whole start block bound i hi) = block[i]

def Contains (whole : List PackingOp) (origin : Nat) : Prop := BlockAt whole origin (programAt origin)

theorem middle_get (before block after : List PackingOp) (index : Nat) (hi : index < block.length) :
    (before ++ block ++ after)[before.length + index]'(by simp only [List.length_append]; omega) = block[index] := by
  rw [List.getElem_append_left (by simp only [List.length_append]; omega),
    List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]

theorem subblock (whole : List PackingOp) (origin : Nat) (hc : Contains whole origin)
    (before block after : List PackingOp) (heq : programAt origin = before ++ block ++ after) :
    BlockAt whole (origin + before.length) block := by
  have hl := congrArg List.length heq
  simp only [List.length_append] at hl
  refine ⟨by have hb := hc.bound; omega, ?_⟩
  intro i hi
  have hh := hc.code (before.length + i) (by omega)
  have hg := congrArg (fun ops : List PackingOp =>
    ops.getD (before.length + i) (.base (.base (.constant .value 0)))) heq
  rw [List.getD_eq_getElem (n := before.length + i) (programAt origin)
      (.base (.base (.constant .value 0))) (by omega),
    List.getD_eq_getElem (n := before.length + i) (before ++ block ++ after)
      (.base (.base (.constant .value 0))) (by simp only [List.length_append]; omega)] at hg
  simpa only [Nat.add_assoc] using hh.trans (hg.trans (middle_get before block after i hi))

theorem sentinel_at (whole : List PackingOp) (origin : Nat) (hc : Contains whole origin) :
    BlockAt whole origin PSTRParentSentinel.program := by
  have h := subblock whole origin hc [] PSTRParentSentinel.program
    (PSTRCountControl.testBlock (origin + 478) ++ PSTRNodeLeaf.programAt (origin + 10) ++
      PSTRCountRestore.program ++ PSTRCountKernel.programAt (origin + 123) ++
      PSTRParentCopy.program ++ PSTRCountAdvance.program ++ PSTRCountControl.backBlock (origin + 5))
    (by simp only [programAt, List.nil_append, List.append_assoc])
  simpa only [List.length_nil, Nat.add_zero] using h

theorem test_at (whole : List PackingOp) (origin : Nat) (hc : Contains whole origin) :
    BlockAt whole (origin + 5) (PSTRCountControl.testBlock (origin + 478)) := by
  have h := subblock whole origin hc PSTRParentSentinel.program (PSTRCountControl.testBlock (origin + 478))
    (PSTRNodeLeaf.programAt (origin + 10) ++ PSTRCountRestore.program ++
      PSTRCountKernel.programAt (origin + 123) ++ PSTRParentCopy.program ++
      PSTRCountAdvance.program ++ PSTRCountControl.backBlock (origin + 5))
    (by simp only [programAt, List.append_assoc])
  simpa only [PSTRParentSentinel.program_length] using h

theorem leaf_at (whole : List PackingOp) (origin : Nat) (hc : Contains whole origin) :
    PSTRNodeLeaf.Contains whole (origin + 10) := by
  have h := subblock whole origin hc
    (PSTRParentSentinel.program ++ PSTRCountControl.testBlock (origin + 478))
    (PSTRNodeLeaf.programAt (origin + 10))
    (PSTRCountRestore.program ++ PSTRCountKernel.programAt (origin + 123) ++
      PSTRParentCopy.program ++ PSTRCountAdvance.program ++ PSTRCountControl.backBlock (origin + 5))
    (by simp only [programAt, List.append_assoc])
  have hb : BlockAt whole (origin + 10) (PSTRNodeLeaf.programAt (origin + 10)) := by
    simpa only [List.length_append, PSTRParentSentinel.program_length,
      PSTRCountControl.testBlock_length] using h
  exact ⟨hb.bound, hb.code⟩

theorem restore_at (whole : List PackingOp) (origin : Nat) (hc : Contains whole origin) :
    BlockAt whole (origin + 97) PSTRCountRestore.program := by
  have h := subblock whole origin hc
    (PSTRParentSentinel.program ++ PSTRCountControl.testBlock (origin + 478) ++
      PSTRNodeLeaf.programAt (origin + 10)) PSTRCountRestore.program
    (PSTRCountKernel.programAt (origin + 123) ++ PSTRParentCopy.program ++
      PSTRCountAdvance.program ++ PSTRCountControl.backBlock (origin + 5))
    (by simp only [programAt, List.append_assoc])
  simpa only [List.length_append, PSTRParentSentinel.program_length,
    PSTRCountControl.testBlock_length, PSTRNodeLeaf.programAt_length] using h

theorem kernel_at (whole : List PackingOp) (origin : Nat) (hc : Contains whole origin) :
    BlockAt whole (origin + 123) (PSTRCountKernel.programAt (origin + 123)) := by
  have h := subblock whole origin hc
    (PSTRParentSentinel.program ++ PSTRCountControl.testBlock (origin + 478) ++
      PSTRNodeLeaf.programAt (origin + 10) ++ PSTRCountRestore.program)
    (PSTRCountKernel.programAt (origin + 123))
    (PSTRParentCopy.program ++ PSTRCountAdvance.program ++ PSTRCountControl.backBlock (origin + 5))
    (by simp only [programAt, List.append_assoc])
  simpa only [List.length_append, PSTRParentSentinel.program_length,
    PSTRCountControl.testBlock_length, PSTRNodeLeaf.programAt_length, PSTRCountRestore.program_length] using h

theorem parent_at (whole : List PackingOp) (origin : Nat) (hc : Contains whole origin) :
    BlockAt whole (origin + 393) PSTRParentCopy.program := by
  have h := subblock whole origin hc
    (PSTRParentSentinel.program ++ PSTRCountControl.testBlock (origin + 478) ++
      PSTRNodeLeaf.programAt (origin + 10) ++ PSTRCountRestore.program ++
      PSTRCountKernel.programAt (origin + 123)) PSTRParentCopy.program
    (PSTRCountAdvance.program ++ PSTRCountControl.backBlock (origin + 5))
    (by simp only [programAt, List.append_assoc])
  simpa only [List.length_append, PSTRParentSentinel.program_length,
    PSTRCountControl.testBlock_length, PSTRNodeLeaf.programAt_length,
    PSTRCountRestore.program_length, PSTRCountKernel.programAt_length] using h

theorem advance_at (whole : List PackingOp) (origin : Nat) (hc : Contains whole origin) :
    BlockAt whole (origin + 443) PSTRCountAdvance.program := by
  have h := subblock whole origin hc
    (PSTRParentSentinel.program ++ PSTRCountControl.testBlock (origin + 478) ++
      PSTRNodeLeaf.programAt (origin + 10) ++ PSTRCountRestore.program ++
      PSTRCountKernel.programAt (origin + 123) ++ PSTRParentCopy.program) PSTRCountAdvance.program
    (PSTRCountControl.backBlock (origin + 5))
    (by simp only [programAt, List.append_assoc])
  simpa only [List.length_append, PSTRParentSentinel.program_length,
    PSTRCountControl.testBlock_length, PSTRNodeLeaf.programAt_length,
    PSTRCountRestore.program_length, PSTRCountKernel.programAt_length, PSTRParentCopy.program_length] using h

theorem back_at (whole : List PackingOp) (origin : Nat) (hc : Contains whole origin) :
    BlockAt whole (origin + 475) (PSTRCountControl.backBlock (origin + 5)) := by
  have h := subblock whole origin hc
    (PSTRParentSentinel.program ++ PSTRCountControl.testBlock (origin + 478) ++
      PSTRNodeLeaf.programAt (origin + 10) ++ PSTRCountRestore.program ++
      PSTRCountKernel.programAt (origin + 123) ++ PSTRParentCopy.program ++ PSTRCountAdvance.program)
    (PSTRCountControl.backBlock (origin + 5)) [] (by simp only [programAt, List.append_nil])
  simpa only [List.length_append, PSTRParentSentinel.program_length,
    PSTRCountControl.testBlock_length, PSTRNodeLeaf.programAt_length,
    PSTRCountRestore.program_length, PSTRCountKernel.programAt_length,
    PSTRParentCopy.program_length, PSTRCountAdvance.program_length] using h

end PaperProofs.Structure.LaminarTree.PSTROuterCountCode
