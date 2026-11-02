module

public import Structure.PA06_A19Prepare_ROM_001
public import Structure.PA06_A19Prepare_Word_002

set_option autoImplicit false
set_option warningAsError true

/-! The actual original A19 initial input reaches the active A06 serialized
output at any common factor>=16. All input/laminarity hypotheses are the
original ones. This module neither restarts a halted state nor turns the
serialized heap into a supplied ROM or a compact A19 HeapRepresents. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareEntry003

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawTreePreprocessingWordInterface
open RawTreePreprocessingNat (program)

/-- Genuine controllerInput, arbitrary initialUsed and every actual clock,
at the single selected word factor. No old run/output/safety premise. -/
theorem run_refines (factor q : Nat) (full : List (Finset (Fin q)))
    (initialUsed : Finset (Fin q)) (hf : 16 ≤ factor) (hq : 0 < q) (count : Nat) :
    packingRun (CompactControllerClaims.controllerInput q full initialUsed) program count
      (packingInitial (fun _ => BitVec.ofNat (indexWidth factor full.length q) 0)) =
      (natRun (rawIncidenceROM q full) program count natInitial).toWord
        (indexWidth factor full.length q) := by
  let bits := indexWidth factor full.length q
  have hb : indexWidth 16 full.length q ≤ bits :=
    PA17WordBounds023.indexWidth_mono_factor 16 factor full.length q hf
  have fits {value : Nat} (h : Fits (indexWidth 16 full.length q) value) : Fits bits value :=
    PA17WordBounds023.fits_mono_bits hb h
  change packingRun _ program count (natInitial.toWord bits) = _
  rw [natRun_toWord (CompactControllerClaims.controllerInput q full initialUsed) program natInitial count
    (fun value hvalue => fits (RawTreePreprocessingCostBounds.code_wordsFit full.length q value hvalue)) (by
      intro clock hclock
      rw [PA06A19PrepareROM001.controllerInput_natRun_eq_raw q full initialUsed hq clock]
      have hs := RawTreePreprocessingA06Closure.all_prefix_safe q full hq count clock hclock
      exact ⟨fun register => fits (hs.1 register), fits (safePoint_pcFit q full _ hs)⟩)]
  rw [PA06A19PrepareROM001.controllerInput_natRun_eq_raw q full initialUsed hq count]

/-- Same actual physical state as the original raw-input program, at the
same clock and factor. Nothing here asserts a new ROM or heap allocation. -/
theorem wordRun_eq_raw (factor q : Nat) (full : List (Finset (Fin q)))
    (initialUsed : Finset (Fin q)) (hf : 16 ≤ factor) (hq : 0 < q) (count : Nat) :
    let bits := indexWidth factor full.length q
    let initial := packingInitial (fun _ => BitVec.ofNat bits 0)
    packingRun (CompactControllerClaims.controllerInput q full initialUsed) program count initial =
      packingRun (rawIncidenceROM q full) program count initial :=
  (run_refines factor q full initialUsed hf hq count).trans
    (PA06A19PrepareWord002.run_refines factor q full hf hq count).symm

/-- Actual event trace is unchanged. The increased input loading bill is
charged separately below; it is not hidden by state equality. -/
theorem dynamicTrace_eq_raw (factor q : Nat) (full : List (Finset (Fin q)))
    (initialUsed : Finset (Fin q)) (hf : 16 ≤ factor) (hq : 0 < q) (count : Nat) :
    let bits := indexWidth factor full.length q
    let initial := packingInitial (fun _ => BitVec.ofNat bits 0)
    packingDynamicTrace (CompactControllerClaims.controllerInput q full initialUsed) program count initial =
      packingDynamicTrace (rawIncidenceROM q full) program count initial := by
  let bits := indexWidth factor full.length q
  let initial := packingInitial (fun _ => BitVec.ofNat bits 0)
  change packingDynamicTrace _ program count initial = packingDynamicTrace _ program count initial
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [dynamicTrace_succ_right, dynamicTrace_succ_right, ih,
      wordRun_eq_raw factor q full initialUsed hf hq count]
    rfl

theorem controllerInput_size (q : Nat) (full : List (Finset (Fin q)))
    (initialUsed : Finset (Fin q)) :
    (CompactControllerClaims.controllerInput q full initialUsed).size = full.length * q + q + 2 := by
  simp only [CompactControllerClaims.controllerInput, rawIncidenceROM, PhysicalROM.size,
    List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_finRange, incidence_length]
  omega

/-- Full original loading/initialization/trace cost differs by exactly the
q appended initial-used words. The trace includes every actually executed
instruction; no HALT is falsely inserted at this active endpoint. -/
theorem totalCost_eq_raw_add_q (factor q : Nat) (full : List (Finset (Fin q)))
    (initialUsed : Finset (Fin q)) (hf : 16 ≤ factor) (hq : 0 < q) (count : Nat) :
    let bits := indexWidth factor full.length q
    let heap := fun _ => BitVec.ofNat bits 0
    totalCost (RawTreePreprocessingCostBounds.heapWords full.length q)
      (CompactControllerClaims.controllerInput q full initialUsed) program count heap =
      totalCost (RawTreePreprocessingCostBounds.heapWords full.length q)
        (rawIncidenceROM q full) program count heap + q := by
  dsimp only
  unfold totalCost
  rw [dynamicTrace_eq_raw factor q full initialUsed hf hq count,
    controllerInput_size, RawIncidenceLaminarRAM.rawIncidenceROM_size]
  omega

theorem totalCost_le (factor q : Nat) (full : List (Finset (Fin q)))
    (initialUsed : Finset (Fin q)) (hf : 16 ≤ factor) (hq : 0 < q)
    (count : Nat) (hcount : count ≤ 16384 * treeWork full.length q) :
    let bits := indexWidth factor full.length q
    totalCost (RawTreePreprocessingCostBounds.heapWords full.length q)
      (CompactControllerClaims.controllerInput q full initialUsed) program count
      (fun _ => BitVec.ofNat bits 0) ≤ 262145 * treeWork full.length q := by
  dsimp only
  rw [totalCost_eq_raw_add_q factor q full initialUsed hf hq count]
  have hold := RawTreePreprocessingCostBounds.totalCost_le q full hq count
    (fun _ => BitVec.ofNat (indexWidth factor full.length q) 0) hcount
  have hqwork : q ≤ treeWork full.length q := by
    unfold treeWork
    have hsquare : 1 ≤ (full.length + q + 1) ^ 2 := by
      simpa only [one_pow] using Nat.pow_le_pow_left (show 1 ≤ full.length + q + 1 by omega) 2
    simpa only [one_mul] using Nat.mul_le_mul_right q hsquare
  omega

/-- Unconditional positive-q original A19 input, original laminarity, a
common selected factor, true active endpoint and true decoded A06 output.
The heap bound here is A06's proved allocation, not A19's compact heap. -/
theorem active_word_output (factor q : Nat) (full : List (Finset (Fin q)))
    (initialUsed : Finset (Fin q)) (hf : 16 ≤ factor) (hq : 0 < q) (hl : LaminarSchedule full) :
    ∃ clock ≤ 16384 * treeWork full.length q,
      let bits := indexWidth factor full.length q
      let state := packingRun (CompactControllerClaims.controllerInput q full initialUsed) program clock
        (packingInitial (fun _ => BitVec.ofNat bits 0))
      state.pc.toNat = 5 * program.length ∧ state.halted = false ∧
      state.register .value = BitVec.ofNat bits 1 ∧
      TreeOutputCorrect q full (RawTreePreprocessingCostBounds.heapWords full.length q) state ∧
      totalCost (RawTreePreprocessingCostBounds.heapWords full.length q)
        (CompactControllerClaims.controllerInput q full initialUsed) program clock (fun _ => BitVec.ofNat bits 0) ≤
          262145 * treeWork full.length q := by
  obtain ⟨clock, hclock, pc, active, accepted, output, _oldcost⟩ :=
    PA06A19PrepareWord002.active_word_output factor q full hf hq hl
  refine ⟨clock, hclock, ?_⟩
  dsimp only
  have hs := wordRun_eq_raw factor q full initialUsed hf hq clock
  refine ⟨?_, ?_, ?_, ?_, totalCost_le factor q full initialUsed hf hq clock hclock⟩
  · rw [hs]
    exact pc
  · rw [hs]
    exact active
  · rw [hs]
    exact accepted
  · rw [hs]
    exact output

/-- At the genuine controller input, an arbitrary appended body preserves
all Nat clocks through an actual pre-HALT serialized-output endpoint.
No assertion about safety or behavior AFTER that endpoint is made. -/
theorem append_active_nat_output (q : Nat) (full : List (Finset (Fin q)))
    (initialUsed : Finset (Fin q)) (hq : 0 < q) (hl : LaminarSchedule full) (later : List PackingOp) :
    ∃ clock ≤ 16384 * treeWork full.length q,
      PA06A19PreparePreHalt001.Ready q full
        (natRun (CompactControllerClaims.controllerInput q full initialUsed) (program ++ later) clock natInitial) ∧
      ∀ count ≤ clock,
        natRun (CompactControllerClaims.controllerInput q full initialUsed) (program ++ later) count natInitial =
          natRun (rawIncidenceROM q full) program count natInitial := by
  obtain ⟨clock, hclock, ready, _safe, body⟩ := PA06A19PreparePreHalt001.active_output q full hq hl
  have newBody (count : Nat) (hc : count < clock) :
      ∃ index < program.length,
        (natRun (CompactControllerClaims.controllerInput q full initialUsed) program count natInitial).pc = 5 * index := by
    rw [PA06A19PrepareROM001.controllerInput_natRun_eq_raw q full initialUsed hq count]
    exact body count hc
  have appendEq := ProgramPrefix.natRun_append_all_prefixes
    (CompactControllerClaims.controllerInput q full initialUsed) program later clock natInitial newBody
  have eq (count : Nat) (hc : count ≤ clock) :
      natRun (CompactControllerClaims.controllerInput q full initialUsed) (program ++ later) count natInitial =
        natRun (rawIncidenceROM q full) program count natInitial :=
    (appendEq count hc).trans (PA06A19PrepareROM001.controllerInput_natRun_eq_raw q full initialUsed hq count)
  refine ⟨clock, hclock, ?_, eq⟩
  rw [eq clock le_rfl]
  exact ready

end PaperProofs.Structure.LaminarTree.PA06A19PrepareEntry003
