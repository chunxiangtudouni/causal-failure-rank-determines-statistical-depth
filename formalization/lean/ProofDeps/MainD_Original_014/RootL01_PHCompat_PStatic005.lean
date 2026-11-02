module
public import RootL01_PHCompat_PFacade001
import all RootL01_PHCompat_PFacade001

public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace RootL01.PHCompat.Preparation
open PaperProofs.Structure.LaminarTree
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

private theorem program_eq_original : program=PA06A19PrepareAllQCode082.program := rfl

theorem encoded_words_fit32 : WordsFit 32 (packingCode program) := by
  rw [program_eq_original]
  exact PA06A19PrepareAllQCode082.encoded_words_fit32

theorem pc_room32 : Fits 32 (5*program.length) := by
  rw [program_eq_original]
  exact PA06A19PrepareAllQCode082.pc_room32

theorem encoded_length_le29 : (packingCode program).length≤2^29 := by
  rw [program_eq_original]
  exact PA06A19PrepareAllQCode082.encoded_length_le29

theorem selected_certificate (N q : Nat) :
    WordsFit (indexWidth 32 N q) (packingCode program) ∧
      Fits (indexWidth 32 N q) (5*program.length) := by
  rw [program_eq_original]
  exact PA06A19PrepareAllQCode082.selected_certificate N q

end RootL01.PHCompat.Preparation
