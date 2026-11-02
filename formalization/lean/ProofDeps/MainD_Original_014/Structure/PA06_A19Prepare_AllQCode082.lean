module

public import Structure.PA06_A19Prepare_AllQCode082_Prefix
public import Structure.PA06_A19Prepare_AllQCode082_Tail

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED static certificates for ONE fixed all-q code list.
The selected word width is real32*clog2(N+q+2), includingN=q=0.
These conclusions assert word/PC/encoded-length room, not whole execution. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareAllQCode082

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

theorem encoded_words_fit32 : WordsFit 32 (packingCode program) := by
  rw [← program_layout]
  simpa only [List.append_assoc] using
    (PA06A19PrepareCodeFit052.append_encoded_words_fit patchedPrefix
      (PA06A19PrepareCodeFit052.builderProgram ++ PA06A19PrepareCodeFit052.afterBuilder ++ right)
      prefix_encoded_words_fit32 after_prefix_encoded_words_fit32)

theorem pc_room32 : Fits 32 (5 * program.length) := by
  rw [program_length]
  exact final_end_room32

theorem encoded_length_le29 : (packingCode program).length ≤ 2 ^ 29 := by
  rw [program_code_length]
  exact final_encoded_length_le29

theorem encoded_length_le32 : (packingCode program).length ≤ 2 ^ 32 :=
  encoded_length_le29.trans (by decide)

theorem encoded_words_fit (bits : Nat) (room : 32 ≤ bits) :
    WordsFit bits (packingCode program) := by
  intro value member
  exact PA17WordBounds023.fits_mono_bits room (encoded_words_fit32 value member)

theorem pc_room (bits : Nat) (room : 32 ≤ bits) : Fits bits (5 * program.length) :=
  PA17WordBounds023.fits_mono_bits room pc_room32

theorem selected_encoded_words_fit (N q : Nat) :
    WordsFit (indexWidth 32 N q) (packingCode program) :=
  encoded_words_fit _ (PSTRBuildLower.CounterInit.selected_width_room N q)

theorem selected_pc_room (N q : Nat) : Fits (indexWidth 32 N q) (5 * program.length) :=
  pc_room _ (PSTRBuildLower.CounterInit.selected_width_room N q)

theorem selected_certificate (N q : Nat) :
    WordsFit (indexWidth 32 N q) (packingCode program) ∧
      Fits (indexWidth 32 N q) (5 * program.length) :=
  ⟨selected_encoded_words_fit N q, selected_pc_room N q⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareAllQCode082
