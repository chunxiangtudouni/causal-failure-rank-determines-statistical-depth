module

public import Structure.PA06_A19Prepare_PreHalt_001
public import PaperProofs.Structure.PA17_WordBounds_023

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareWord002

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawTreePreprocessingWordInterface
open RawTreePreprocessingNat (program)

/-- The original raw program refines at every larger selected word factor.
No dimension or input restriction is imposed by widening its actual words. -/
theorem run_refines (factor q : Nat) (full : List (Finset (Fin q)))
    (hf : 16 ≤ factor) (hq : 0 < q) (count : Nat) :
    packingRun (rawIncidenceROM q full) program count
      (packingInitial (fun _ => BitVec.ofNat (indexWidth factor full.length q) 0)) =
      (natRun (rawIncidenceROM q full) program count natInitial).toWord
        (indexWidth factor full.length q) := by
  let bits := indexWidth factor full.length q
  have hb : indexWidth 16 full.length q ≤ bits :=
    PA17WordBounds023.indexWidth_mono_factor 16 factor full.length q hf
  have fits {value : Nat} (h : Fits (indexWidth 16 full.length q) value) : Fits bits value :=
    PA17WordBounds023.fits_mono_bits hb h
  change packingRun (rawIncidenceROM q full) program count (natInitial.toWord bits) = _
  apply natRun_toWord
  · intro value hvalue
    exact fits (RawTreePreprocessingCostBounds.code_wordsFit full.length q value hvalue)
  · intro k hk
    have hs := RawTreePreprocessingA06Closure.all_prefix_safe q full hq count k hk
    exact ⟨fun register => fits (hs.1 register), fits (safePoint_pcFit q full _ hs)⟩

/-- A06's ACTIVE physical output boundary at any one common factor>=16.
This is still the A06 heap layout, not the A19 packed final representation. -/
theorem active_word_output (factor q : Nat) (full : List (Finset (Fin q)))
    (hf : 16 ≤ factor) (hq : 0 < q) (hl : LaminarSchedule full) :
    ∃ clock ≤ 16384 * treeWork full.length q,
      let bits := indexWidth factor full.length q
      let state := packingRun (rawIncidenceROM q full) program clock
        (packingInitial (fun _ => BitVec.ofNat bits 0))
      state.pc.toNat = 5 * program.length ∧ state.halted = false ∧
      state.register .value = BitVec.ofNat bits 1 ∧
      TreeOutputCorrect q full (RawTreePreprocessingCostBounds.heapWords full.length q) state ∧
      totalCost (RawTreePreprocessingCostBounds.heapWords full.length q)
        (rawIncidenceROM q full) program clock (fun _ => BitVec.ofNat bits 0) ≤
          262144 * treeWork full.length q := by
  obtain ⟨clock, hclock, ready, _hsafe, _hbody⟩ := PA06A19PreparePreHalt001.active_output q full hq hl
  refine ⟨clock, hclock, ?_⟩
  let bits := indexWidth factor full.length q
  let state := natRun (rawIncidenceROM q full) program clock natInitial
  have hb : indexWidth 16 full.length q ≤ bits :=
    PA17WordBounds023.indexWidth_mono_factor 16 factor full.length q hf
  have fits {value : Nat} (h : Fits (indexWidth 16 full.length q) value) : Fits bits value :=
    PA17WordBounds023.fits_mono_bits hb h
  have hs := RawTreePreprocessingA06Closure.all_prefix_safe q full hq (clock + 1) clock (by omega)
  have hr : RegistersFit bits state := fun register => fits (hs.1 register)
  have hlength : Fits bits (serializeROM (givenTreeROM q full)).length :=
    fits (RawTreeSerialization.serialize_givenTreeROM_length_fits q full hq hl)
  have houtput : TreeOutputCorrect q full (RawTreePreprocessingCostBounds.heapWords full.length q)
      (state.toWord bits) := by
    apply RawTreeSerialization.treeOutputCorrect_of_words
    · rw [toWord_register_toNat bits state hr]
      exact ready.nodes
    · rw [toWord_register_toNat bits state hr]
      exact ready.length
    · exact (RawTreePreprocessingCostBounds.output_length_lt_heapWords q full hq hl).le
    · intro position hp
      have hposition : Fits bits position := hp.trans hlength
      have hword : Fits bits ((serializeROM (givenTreeROM q full))[position]) :=
        fits (RawTreeOutputWords.serialize_givenTreeROM_wordsFit q full hq hl _ (List.getElem_mem hp))
      change (BitVec.ofNat bits (state.heap (BitVec.ofNat bits position).toNat)).toNat = _
      have haddress : (BitVec.ofNat bits position).toNat = position := Nat.mod_eq_of_lt hposition
      rw [haddress, ready.words position hp, List.getD_eq_getElem _ 0 hp]
      exact Nat.mod_eq_of_lt hword
  dsimp only
  rw [run_refines factor q full hf hq clock]
  refine ⟨?_, ready.active, ?_, houtput, ?_⟩
  · change (BitVec.ofNat bits state.pc).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (fits (safePoint_pcFit q full _ hs))]
    exact ready.pc
  · change BitVec.ofNat bits (state.register .value) = _
    rw [ready.accepted]
  · exact RawTreePreprocessingCostBounds.totalCost_le q full hq clock _ hclock

end PaperProofs.Structure.LaminarTree.PA06A19PrepareWord002
