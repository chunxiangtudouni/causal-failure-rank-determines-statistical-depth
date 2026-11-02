module

public import Structure.PA06_A19Prepare_AllQCode082_Program
public import Structure.PA06_A19Prepare_CodeFit052_Suffix

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000

/-! UNVALIDATED finite checks for only the new three-op skip and60-op
zero handler, followed by append transport of the existing052 suffix.
No runtime safety or execution result is assumed by these certificates. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareAllQCode082

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

theorem skip_encoded_words_fit32 : WordsFit 32 (packingCode skip) := by
  apply PA06A19PrepareCodeFit052.encoded_words_fit32_of_checked
  decide

theorem zero_encoded_words_fit32 : WordsFit 32 (packingCode zeroBody) := by
  apply PA06A19PrepareCodeFit052.encoded_words_fit32_of_checked
  decide

theorem right_encoded_words_fit32 : WordsFit 32 (packingCode right) :=
  PA06A19PrepareCodeFit052.append_encoded_words_fit _ _
    skip_encoded_words_fit32 zero_encoded_words_fit32

theorem after_prefix_encoded_words_fit32 :
    WordsFit 32 (packingCode (PA06A19PrepareCodeFit052.builderProgram ++
      PA06A19PrepareCodeFit052.afterBuilder ++ right)) :=
  PA06A19PrepareCodeFit052.append_encoded_words_fit _ _
    (PA06A19PrepareCodeFit052.append_encoded_words_fit _ _
      PA06A19PrepareCodeFit052.builder_encoded_words_fit32
      PA06A19PrepareCodeFit052.afterBuilder_encoded_words_fit32)
    right_encoded_words_fit32

theorem final_end_room32 : Fits 32 (5 * finalEnd) := by
  change 5 * finalEnd < 2 ^ 32
  decide

/-- All five words of the ONE trailing implicit HALT are included. -/
theorem final_encoded_length_le29 : 5 * finalEnd + 5 ≤ 2 ^ 29 := by
  decide

end PaperProofs.Structure.LaminarTree.PA06A19PrepareAllQCode082
