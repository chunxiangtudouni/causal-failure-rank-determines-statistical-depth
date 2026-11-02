module

public import Structure.PA06_A19Prepare_EarlyGate079_Safe
public import Structure.PA06_A19Prepare_EarlyGate079_Footprint
public import Structure.PA06_A19Prepare_InitialUsed037_Prefix

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED actual q0 gate on the original physical input and zero
heap. The only remaining premises concern the selected fixed code and its
real handler label. They must be discharged inside the final all-q proof. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareEarlyGate079

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims RawIncidenceLaminarRAM CompactControllerClaims
open PA06A19PrepareInitialUsed037 (Fetched)

private theorem wordzero_control_of_refinement {bits : Nat}
    (state : WordState bits) (natural : NatState) (endpointPC : Nat)
    (refineEq : state = natural.toWord bits)
    (naturalPC : natural.pc = endpointPC) (naturalActive : natural.halted = false)
    (pcFit : Fits bits endpointPC) :
    state.pc.toNat = endpointPC ∧ state.halted = false := by
  have pcEq := congrArg (fun after : WordState bits => after.pc.toNat) refineEq
  change state.pc.toNat = (BitVec.ofNat bits natural.pc).toNat at pcEq
  have naturalWordPC : (BitVec.ofNat bits natural.pc).toNat = endpointPC := by
    rw [naturalPC, BitVec.toNat_ofNat, Nat.mod_eq_of_lt pcFit]
  have activeEq := congrArg (fun after : WordState bits => after.halted) refineEq
  change state.halted = natural.halted at activeEq
  exact ⟨pcEq.trans naturalWordPC, activeEq.trans naturalActive⟩

theorem zero_word_entry (full : List (Finset (Fin 0))) (used : Finset (Fin 0))
    (handlerIndex : Nat) (old : List PackingOp)
    (handlerLabel : handlerIndex ≤ (program (5 * handlerIndex) old).length)
    (hcode : WordsFit (indexWidth 32 full.length 0) (packingCode (program (5 * handlerIndex) old)))
    (hcodePC : Fits (indexWidth 32 full.length 0) (5 * (program (5 * handlerIndex) old).length)) :
    let rom := controllerInput 0 full used
    let bits := indexWidth 32 full.length 0
    let H := PA06A19PreparePreBuild044.allocation 0 full
    let code := program (5 * handlerIndex) old
    let initial := packingInitial (fun _ => BitVec.ofNat bits 0)
    let after := packingRun rom code 8 initial
    after.pc.toNat = 5 * handlerIndex ∧ after.halted = false ∧
      (∀ count < 8, Fetched H rom code (packingRun rom code count initial)) ∧
      (packingDynamicTrace rom code 8 initial).length ≤ 96 := by
  let rom := controllerInput 0 full used
  let bits := indexWidth 32 full.length 0
  let H := PA06A19PreparePreBuild044.allocation 0 full
  let code := program (5 * handlerIndex) old
  let B := max full.length (max (5 * handlerIndex) 8)
  have nFit : Fits bits full.length :=
    PA17WordBounds023.fits_mono_bits
      (PA17WordBounds023.indexWidth_mono_factor 16 32 full.length 0 (by decide))
      ((show full.length ≤ full.length * 0 + full.length + 0 + 640 by omega).trans_lt
        (fits_checker_register_bound full.length 0))
  have handlerFit : Fits bits (5 * handlerIndex) :=
    (Nat.mul_le_mul_left 5 handlerLabel).trans_lt hcodePC
  have smallFit : Fits bits 8 := PA17WordBounds023.small_word_fit full.length 0
  have bFit : Fits bits B := by
    change max full.length (max (5 * handlerIndex) 8) < 2 ^ bits
    exact max_lt_iff.mpr ⟨nFit, max_lt_iff.mpr ⟨handlerFit, smallFit⟩⟩
  have headerN : rom.semantic.read .input 0 = full.length := by
    change (controllerInput 0 full used).semantic.read .input 0 = full.length
    rw [original_rom_zero]
    exact raw_header_N 0 full
  have headerQ : rom.semantic.read .input 1 = 0 := by
    change (controllerInput 0 full used).semantic.read .input 1 = 0
    rw [original_rom_zero]
    exact raw_header_q 0 full
  have inputBound : 2 ≤ (rom.words .input).length := by
    change 2 ≤ ((controllerInput 0 full used).words .input).length
    rw [original_rom_zero]
    simp only [rawIncidenceROM, PhysicalROM.words, List.length_append,
      List.length_cons, List.length_nil]
    omega
  have heapBound : 2 ≤ H := by
    dsimp only [H]
    rw [zero_allocation_eq]
    omega
  have nBound : full.length ≤ B := le_max_left full.length (max (5 * handlerIndex) 8)
  have handlerBound : 5 * handlerIndex ≤ B :=
    (le_max_left (5 * handlerIndex) 8).trans (le_max_right full.length (max (5 * handlerIndex) 8))
  have small : 8 ≤ B :=
    (le_max_right (5 * handlerIndex) 8).trans (le_max_right full.length (max (5 * handlerIndex) 8))
  have safe := gate_safe rom full.length 0 handlerIndex B H old headerN headerQ
    nBound (Nat.zero_le B) handlerBound small inputBound heapBound handlerLabel
  have word (count : Nat) (bound : count ≤ 8) :
      packingRun rom code count (natInitial.toWord bits) = (natRun rom code count natInitial).toWord bits :=
    PA17UniformGenerator035p.actual_word_run rom B H bits code 8 natInitial safe bFit hcode hcodePC count bound
  have natural := zero_entry rom full.length (5 * handlerIndex) old headerN headerQ
  dsimp only at natural
  dsimp only
  change
    (packingRun rom code 8 (natInitial.toWord bits)).pc.toNat = 5 * handlerIndex ∧
    (packingRun rom code 8 (natInitial.toWord bits)).halted = false ∧
    (∀ count < 8, Fetched H rom code (packingRun rom code count (natInitial.toWord bits))) ∧
    (packingDynamicTrace rom code 8 (natInitial.toWord bits)).length ≤ 96
  have endpoint := wordzero_control_of_refinement
    (packingRun rom code 8 (natInitial.toWord bits))
    (natRun rom code 8 natInitial) (5 * handlerIndex)
    (word 8 le_rfl) natural.1 natural.2.1 handlerFit
  refine ⟨endpoint.1, endpoint.2, ?_, ?_⟩
  · intro count bound
    exact PA17UniformGenerator035p.actual_word_fetch_access rom B H bits code 8 natInitial
      safe bFit hcode hcodePC count bound
  · exact packingDynamicTrace_length_le rom code 8 (natInitial.toWord bits)

end PaperProofs.Structure.LaminarTree.PA06A19PrepareEarlyGate079
