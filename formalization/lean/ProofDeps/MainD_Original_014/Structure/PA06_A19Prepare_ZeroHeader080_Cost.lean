module

public import Structure.PA06_A19Prepare_ZeroHeader080_Word
public import PaperProofs.Structure.PackingExecutionCost

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED linear original q0 allocation/loading and actual-body
trace charges. This does not restart the body at a fresh zero heap and
does not silently charge the early gate or global HALT to this body. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareZeroHeader080

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims CompactControllerClaims

theorem rom_size (full : List (Finset (Fin 0))) (used : Finset (Fin 0)) :
    (controllerInput 0 full used).size = 2 := by
  change (controllerInput 0 full used).input.length + 0 + 0 = 2
  rw [PA06A19PrepareFinalHeader033InitialUsedROM.input_length]
  omega

theorem body_trace_le (full : List (Finset (Fin 0))) (used : Finset (Fin 0))
    (code : List PackingOp) (before : WordState (wordBits full.length)) :
    (packingDynamicTrace (controllerInput 0 full used) code (clock full.length) before).length ≤
      72 * full.length + 696 := by
  have trace := packingDynamicTrace_length_le (controllerInput 0 full used) code (clock full.length) before
  have bound := Nat.mul_le_mul_left 12 (clock_le full.length)
  omega

theorem body_cost_le (full : List (Finset (Fin 0))) (used : Finset (Fin 0))
    (code : List PackingOp) (before : WordState (wordBits full.length)) :
    (controllerInput 0 full used).size + (packingCode code).length + allocation full.length + 8 +
        (packingDynamicTrace (controllerInput 0 full used) code (clock full.length) before).length ≤
      (9000 + (packingCode code).length) * (full.length + 1) := by
  have trace := body_trace_le full used code before
  have codeLoad : (packingCode code).length ≤ (packingCode code).length * (full.length + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  rw [rom_size, allocation_eq]
  nlinarith

end PaperProofs.Structure.LaminarTree.PA06A19PrepareZeroHeader080
