module

public import Structure.PSTR_BuildLower_BuilderRoom_039
public import PaperProofs.Structure.PackingProgramPrefix

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000

/-! UNVALIDATED fixed-code candidate. This checks the actual relocated
builderCode 1639, separately from the historical builderCode 0 certificate.
The per-op check never materializes one flattened encoded program. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCodeFit052

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

def builderProgram : List PackingOp := PSTRBuildLower.CounterInit.builderCode 1639

def builderEnd : Nat := 1639 + builderProgram.length

/-- The same finite per-op certificate used by the existing BuilderRoom039.
The Boolean is reduced by the kernel, without native evaluation or an axiom. -/
theorem encoded_words_fit32_of_checked (program : List PackingOp)
    (checked : program.all (fun op =>
      op.encode.toArray.toList.all (fun value => decide (value < 2 ^ 32))) = true) :
    WordsFit 32 (packingCode program) := by
  have haltChecked : haltWords.toArray.toList.all (fun value =>
      decide (value < 2 ^ 32)) = true := by decide
  intro value hv
  change value < 2 ^ 32
  change value ∈ program.flatMap (fun op => op.encode.toArray.toList) ++
    haltWords.toArray.toList at hv
  rcases List.mem_append.mp hv with hv | hv
  · obtain ⟨op, hop, hword⟩ := List.mem_flatMap.mp hv
    exact of_decide_eq_true
      ((List.all_eq_true.mp ((List.all_eq_true.mp checked) op hop)) value hword)
  · exact of_decide_eq_true ((List.all_eq_true.mp haltChecked) value hv)

/-- Appending code replaces the earlier implicit HALT. The old body and
the right block's body plus final HALT retain their existing word bounds. -/
theorem append_encoded_words_fit {bits : Nat} (left right : List PackingOp)
    (hl : WordsFit bits (packingCode left))
    (hr : WordsFit bits (packingCode right)) :
    WordsFit bits (packingCode (left ++ right)) := by
  intro value hv
  rw [ProgramPrefix.packingCode_append] at hv
  rcases List.mem_append.mp hv with hv | hv
  · apply hl value
    change value ∈ bodyWords left ++ haltWords.toArray.toList
    exact List.mem_append_left _ hv
  · exact hr value hv

theorem builder_encoded_words_fit32 : WordsFit 32 (packingCode builderProgram) := by
  apply encoded_words_fit32_of_checked
  decide

/-- Equality of lengths is checked for the two concrete relocated lists;
no equality of their instruction words or branch labels is asserted. -/
theorem builder_length_eq_zero_start :
    builderProgram.length = PSTRBuildLower.CounterInit.program.length := by
  decide

theorem builder_end_room32 : Fits 32 (5 * builderEnd) := by
  change 5 * builderEnd < 2 ^ 32
  decide

/-- The remaining metadata/used/header blocks contain 532+135+24 ops. -/
theorem final_end_room32 : Fits 32 (5 * (builderEnd + 691)) := by
  change 5 * (builderEnd + 691) < 2 ^ 32
  decide

/-- Includes all five words of the one trailing HALT. -/
theorem final_encoded_length_le32 : 5 * (builderEnd + 691) + 5 ≤ 2 ^ 32 := by
  decide

theorem builder_encoded_words_fit (bits : Nat) (hb : 32 ≤ bits) :
    WordsFit bits (packingCode builderProgram) := by
  intro value hv
  exact PA17WordBounds023.fits_mono_bits hb (builder_encoded_words_fit32 value hv)

theorem builder_end_room (bits : Nat) (hb : 32 ≤ bits) :
    Fits bits (5 * builderEnd) :=
  PA17WordBounds023.fits_mono_bits hb builder_end_room32

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCodeFit052
