module

public import Structure.PA06_A19Prepare_EarlyGate079_Footprint
public import Structure.PA06_A19Prepare_ZeroHeader080_Cost

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED original WHOLE q0 charge: true gate8 + real width/header
body + one global HALT. Complete ROM, encoded code, allocation and startup
are charged once. The code and its constant precede all input instances. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareAllQZero083

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims CompactControllerClaims

def costFactor (code : List PackingOp) : Nat := 10000 + (packingCode code).length

theorem costFactor_pos (code : List PackingOp) : 0 < costFactor code := by
  unfold costFactor
  omega

theorem total_steps_le (N : Nat) :
    8 + PA06A19PrepareZeroHeader080.clock N + 1 ≤ 6 * N + 67 := by
  have bound := PA06A19PrepareZeroHeader080.clock_le N
  omega

theorem whole_cost_le (full : List (Finset (Fin 0))) (used : Finset (Fin 0))
    (code : List PackingOp) (steps : Nat)
    (bound : steps ≤ 6 * full.length + 67) :
    totalCost (PA06A19PreparePreBuild044.allocation 0 full) (controllerInput 0 full used) code steps
      (fun _ => BitVec.ofNat (indexWidth 32 full.length 0) 0) ≤
        costFactor code * (full.length + 1) := by
  have trace := packingDynamicTrace_length_le (controllerInput 0 full used) code steps
    (packingInitial (fun _ => BitVec.ofNat (indexWidth 32 full.length 0) 0))
  have codeLoad : (packingCode code).length ≤ (packingCode code).length * (full.length + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  unfold totalCost
  rw [PA06A19PrepareZeroHeader080.rom_size,
    PA06A19PrepareEarlyGate079.zero_allocation_eq]
  unfold costFactor
  nlinarith

end PaperProofs.Structure.LaminarTree.PA06A19PrepareAllQZero083
