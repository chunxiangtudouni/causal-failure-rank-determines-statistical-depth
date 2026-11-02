module

public import Structure.PA06_A19Prepare_CodeFit052_Program

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000

/-! UNVALIDATED per-block word certificates for the actual relocated
532 metadata,135 initial-used and24 final-header instruction lists. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCodeFit052

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

theorem metadata_encoded_words_fit32 : WordsFit 32 (packingCode metadataSegment) := by
  apply encoded_words_fit32_of_checked
  decide

theorem used_encoded_words_fit32 : WordsFit 32 (packingCode usedSegment) := by
  apply encoded_words_fit32_of_checked
  decide

theorem final_encoded_words_fit32 : WordsFit 32 (packingCode finalSegment) := by
  apply encoded_words_fit32_of_checked
  decide

theorem afterBuilder_encoded_words_fit32 : WordsFit 32 (packingCode afterBuilder) := by
  unfold afterBuilder
  exact append_encoded_words_fit (metadataSegment ++ usedSegment) finalSegment
    (append_encoded_words_fit metadataSegment usedSegment
      metadata_encoded_words_fit32 used_encoded_words_fit32)
    final_encoded_words_fit32

theorem tail_encoded_words_fit32 : WordsFit 32 (packingCode positiveTail) :=
  append_encoded_words_fit _ _ builder_encoded_words_fit32 afterBuilder_encoded_words_fit32

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCodeFit052
