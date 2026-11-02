module

public import Structure.PA06_A19Prepare_Entry_003

set_option autoImplicit false
set_option warningAsError true

/-! Real finite-word fetch/access eligibility of the unchanged fixed raw
constructor at the genuine A19 initial ROM. Every input-tail word is a
real 0/1 initial-used bit. This is all-clock active-prefix safety on the
original A06 allocation; it does not assert an A19 compact heap or later
code safety and it does not restart any halted state. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareAccess004

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawTreePreprocessingWordInterface
open RawCandidateWorkspaceInit (candidateCount workspaceBase)
open RawCandidateWorkspaceBounds (workspaceLimit)
open RawTreePreprocessingNat (program)

theorem widen_fits (factor N q : Nat) (hf : 16 ≤ factor) {value : Nat}
    (hfit : Fits (indexWidth 16 N q) value) : Fits (indexWidth factor N q) value :=
  PA17WordBounds023.fits_mono_bits (PA17WordBounds023.indexWidth_mono_factor 16 factor N q hf) hfit

theorem code_wordsFit (factor N q : Nat) (hf : 16 ≤ factor) :
    WordsFit (indexWidth factor N q) (packingCode program) :=
  fun value hvalue => widen_fits factor N q hf (RawTreePreprocessingCostBounds.code_wordsFit N q value hvalue)

/-- Real appended initialUsed bits are proved to fit. They are not supplied
as arbitrary unbounded words or omitted from ROM eligibility. -/
theorem controllerInput_wordsFit (factor q : Nat) (full : List (Finset (Fin q)))
    (initialUsed : Finset (Fin q)) (hf : 16 ≤ factor) :
    ∀ region, WordsFit (indexWidth factor full.length q)
      ((CompactControllerClaims.controllerInput q full initialUsed).words region) := by
  intro region value hv
  cases region with
  | internal | children => cases hv
  | input =>
    change value ∈ (rawIncidenceROM q full).input ++
      (List.finRange q).map (fun tool => bit (decide (tool ∈ initialUsed))) at hv
    rcases List.mem_append.mp hv with hraw | hused
    · exact widen_fits factor full.length q hf (raw_rom_wordsFit q full .input value hraw)
    · obtain ⟨tool, _htool, rfl⟩ := List.mem_map.mp hused
      have hbit : bit (decide (tool ∈ initialUsed)) ≤ 1 := by
        unfold bit
        split_ifs <;> omega
      exact hbit.trans_lt (widen_fits factor full.length q hf
        (RawTreePreprocessingCodeBounds.constant_fits full.length q 1 (by decide)))

/-- Numeric footprint includes all q appended words in the original input.
The original A06 workspace remains unchanged and is explicitly allocated. -/
theorem controllerInput_footprint_fits (factor q : Nat) (full : List (Finset (Fin q)))
    (initialUsed : Finset (Fin q)) (hf : 16 ≤ factor) :
    Fits (indexWidth factor full.length q)
      ((CompactControllerClaims.controllerInput q full initialUsed).size +
        RawTreePreprocessingCostBounds.heapWords full.length q + (packingCode program).length) := by
  apply widen_fits factor full.length q hf
  rw [PA06A19PrepareEntry003.controllerInput_size, RawTreePreprocessingCostBounds.code_length]
  apply fits_indexWidth_of_lt_power
  let base := full.length + q + 2
  have hb : 2 ≤ base := by dsimp only [base]; omega
  have hsq : 4 ≤ base ^ 2 := Nat.pow_le_pow_left hb 2
  have hpower : 16384 ≤ base ^ 14 := Nat.pow_le_pow_left hb 14
  have hprod : candidateCount full.length q * q ≤ base ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul
      (show candidateCount full.length q ≤ base by dsimp only [candidateCount, base]; omega)
      (show q ≤ base by dsimp only [base]; omega)
  have hlinear : candidateCount full.length q ≤ base ^ 2 := by
    have hmb : candidateCount full.length q ≤ base := by dsimp only [candidateCount, base]; omega
    have hbs : base ≤ base ^ 2 := by nlinarith
    exact hmb.trans hbs
  have hraw : full.length * q ≤ base ^ 2 := by
    have hnm : full.length ≤ candidateCount full.length q := by unfold candidateCount; omega
    exact (Nat.mul_le_mul_right q hnm).trans hprod
  have hq : q ≤ base ^ 2 :=
    (show q ≤ candidateCount full.length q by unfold candidateCount; omega).trans hlinear
  calc
    full.length * q + q + 2 + RawTreePreprocessingCostBounds.heapWords full.length q + 10450 ≤
        18 * base ^ 2 + 18660 := by
      unfold RawTreePreprocessingCostBounds.heapWords workspaceLimit workspaceBase
      nlinarith
    _ < base ^ 2 * 16384 := by nlinarith
    _ ≤ base ^ 2 * base ^ 14 := Nat.mul_le_mul_left _ hpower
    _ = base ^ 16 := by rw [← pow_add]

/-- Actual fetched code and real data accesses at every active physical
clock. No access certificate, old run or SafePoint is assumed by callers. -/
theorem active_fetch_access (factor q : Nat) (full : List (Finset (Fin q)))
    (initialUsed : Finset (Fin q)) (hf : 16 ≤ factor) (hq : 0 < q) (count : Nat) :
    let bits := indexWidth factor full.length q
    let rom := CompactControllerClaims.controllerInput q full initialUsed
    let state := packingRun rom program count (packingInitial (fun _ => BitVec.ofNat bits 0))
    state.halted = false →
      state.pc.toNat + 4 < (packingCode program).length ∧
      match PackingOp.decode (fetch program state) with
      | none => fetch program state = haltWords
      | some op => packingAccessFits rom (RawTreePreprocessingCostBounds.heapWords full.length q) state op := by
  let bits := indexWidth factor full.length q
  let rom := CompactControllerClaims.controllerInput q full initialUsed
  let state := natRun (rawIncidenceROM q full) program count natInitial
  have hs : SafePoint q full state :=
    RawTreePreprocessingA06Closure.all_prefix_safe q full hq (count + 1) count (by omega)
  have hr : RegistersFit bits state := fun register => widen_fits factor full.length q hf (hs.1 register)
  have hp : Fits bits state.pc := widen_fits factor full.length q hf (safePoint_pcFit q full _ hs)
  have hfetch : fetch program (state.toWord bits) = natFetch program state.pc := by
    change physicalFetch bits (packingCode program) (BitVec.ofNat bits state.pc).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp,
      physicalFetch_eq bits (packingCode program) state.pc (code_wordsFit factor full.length q hf)]
    rfl
  have hprefix : PA06A19PrepareROM001.ROMPrefix (rawIncidenceROM q full) rom :=
    PA06A19PrepareROM001.inputTail_prefix (rawIncidenceROM q full)
      ((List.finRange q).map (fun tool => bit (decide (tool ∈ initialUsed))))
  dsimp only
  rw [PA06A19PrepareEntry003.run_refines factor q full initialUsed hf hq count]
  intro hactive
  refine ⟨?_, ?_⟩
  · change (BitVec.ofNat bits state.pc).toNat + 4 < _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
    exact safePoint_fetchWindow q full _ hs
  · rw [hfetch]
    obtain ⟨_hr, _index, _bound, _pc, access⟩ := hs
    have ha := access hactive
    cases hd : PackingOp.decode (natFetch program state.pc) with
    | none => simpa only [hd] using ha
    | some op =>
      have oldAccess : RawIncidenceScanSafety.NatAccessFits (rawIncidenceROM q full)
          (RawTreePreprocessingCostBounds.heapWords full.length q) state op := by simpa only [hd] using ha
      apply physical_access_of_nat rom (RawTreePreprocessingCostBounds.heapWords full.length q) state op hr
      cases op with
      | base op =>
        exact PA06A19PrepareROM001.accessFits_of_romPrefix hprefix
          (RawTreePreprocessingCostBounds.heapWords full.length q) ⟨state.register, state.heap, state.pc⟩ op oldAccess
      | arithmetic operation target left right => exact oldAccess
      | jumpIfZero condition target => exact oldAccess

/-- Complete all-clock word/access eligibility package for this actual raw
constructor/input, without falsely asserting a final halt at each clock. -/
theorem all_clock_safety (factor q : Nat) (full : List (Finset (Fin q)))
    (initialUsed : Finset (Fin q)) (hf : 16 ≤ factor) (hq : 0 < q) :
    let bits := indexWidth factor full.length q
    let rom := CompactControllerClaims.controllerInput q full initialUsed
    WordsFit bits (packingCode program) ∧
      (∀ region, WordsFit bits (rom.words region)) ∧
      Fits bits (rom.size + RawTreePreprocessingCostBounds.heapWords full.length q + (packingCode program).length) ∧
      ∀ count,
        let state := packingRun rom program count (packingInitial (fun _ => BitVec.ofNat bits 0))
        state.halted = false →
          state.pc.toNat + 4 < (packingCode program).length ∧
          match PackingOp.decode (fetch program state) with
          | none => fetch program state = haltWords
          | some op => packingAccessFits rom (RawTreePreprocessingCostBounds.heapWords full.length q) state op :=
  ⟨code_wordsFit factor full.length q hf, controllerInput_wordsFit factor q full initialUsed hf,
    controllerInput_footprint_fits factor q full initialUsed hf,
    active_fetch_access factor q full initialUsed hf hq⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareAccess004
