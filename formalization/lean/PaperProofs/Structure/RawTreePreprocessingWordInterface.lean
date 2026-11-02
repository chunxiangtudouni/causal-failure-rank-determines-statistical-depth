module

public import PaperProofs.Structure.RawTreePreprocessingCostBounds
public import PaperProofs.Structure.RawIncidenceOuterSafety

/-! Pending whole-program word-safety handoff.  Output semantics, fixed code,
footprint, and numeric cost are already proved.  The global prefix invariant
defined here is a remaining obligation, never an axiom or an eligible-input
restriction.  Conditional adapters do not close A06. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.RawTreePreprocessingWordInterface

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawTreeSerialization
open RawTreePreprocessingNat (program)
open RawTreePreprocessingCostBounds (heapWords)
open RawIncidenceScanSafety (NatAccessFits)

/-- All runtime safety facts still to be established phase by phase.
The access clause is used only while the actual state remains active. -/
def SafePoint (q : Nat) (full : List (Finset (Fin q))) (state : NatState) : Prop :=
  RegistersFit (indexWidth 16 full.length q) state ∧
  ∃ index ≤ program.length, state.pc = 5 * index ∧
    (state.halted = false →
      match PackingOp.decode (natFetch program state.pc) with
      | none => natFetch program state.pc = haltWords
      | some op => NatAccessFits (rawIncidenceROM q full) (heapWords full.length q) state op)

theorem safePoint_pcFit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hs : SafePoint q full state) : Fits (indexWidth 16 full.length q) state.pc := by
  obtain ⟨_hr, index, hi, hp, _ha⟩ := hs
  apply RawTreePreprocessingCodeBounds.constant_fits
  rw [RawTreePreprocessingCostBounds.program_length] at hi
  rw [hp]
  omega

theorem safePoint_fetchWindow (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hs : SafePoint q full state) : state.pc + 4 < (packingCode program).length := by
  obtain ⟨_hr, index, hi, hp, _ha⟩ := hs
  rw [hp, RawTreePreprocessingCostBounds.code_length]
  rw [RawTreePreprocessingCostBounds.program_length] at hi
  omega

theorem safePoint_physicalFetch (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hs : SafePoint q full state) :
    fetch program (state.toWord (indexWidth 16 full.length q)) = natFetch program state.pc := by
  change physicalFetch (indexWidth 16 full.length q) (packingCode program)
    (BitVec.ofNat (indexWidth 16 full.length q) state.pc).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (safePoint_pcFit q full state hs),
    physicalFetch_eq _ _ _ (RawTreePreprocessingCostBounds.code_wordsFit full.length q)]
  rfl

/-- Actual Nat output plus the separately proved word/layout bounds gives
the original decoded physical tree-output predicate. -/
theorem wordOutput_of_natOutput (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hl : LaminarSchedule full) (state : NatState) (output : RawTreePreprocessingNat.Output q full state) :
    TreeOutputCorrect q full (heapWords full.length q) (state.toWord (indexWidth 16 full.length q)) := by
  let bits := indexWidth 16 full.length q
  have hnodes : Fits bits (prepareNormalization q full).indexed.nodes.size := by
    have ht := prepared_indexed_size_le q full
    exact lt_of_le_of_lt (ht.trans (by omega)) (fits_checker_register_bound full.length q)
  have hlength : Fits bits (serializeROM (givenTreeROM q full)).length :=
    serialize_givenTreeROM_length_fits q full hq hl
  apply treeOutputCorrect_of_words q full (heapWords full.length q) (state.toWord bits)
  · change (BitVec.ofNat bits (state.register .old)).toNat = _
    rw [output.nodes]
    exact Nat.mod_eq_of_lt hnodes
  · change (BitVec.ofNat bits (state.register .fresh)).toNat = _
    rw [output.length]
    exact Nat.mod_eq_of_lt hlength
  · exact (RawTreePreprocessingCostBounds.output_length_lt_heapWords q full hq hl).le
  · intro position hp
    have hposition : Fits bits position := hp.trans hlength
    have haddress : (BitVec.ofNat bits position).toNat = position := Nat.mod_eq_of_lt hposition
    change (BitVec.ofNat bits (state.heap (BitVec.ofNat bits position).toNat)).toNat = _
    rw [haddress, output.words position hp, List.getD_eq_getElem _ 0 hp]
    apply Nat.mod_eq_of_lt
    exact RawTreeOutputWords.serialize_givenTreeROM_wordsFit q full hq hl _ (List.getElem_mem hp)

/-- Precise remaining whole-program invariant.  This is stated rather
than assumed silently in the raw-input model; it has no proof here. -/
def PrefixSafety : Prop :=
  ∀ (q : Nat) (full : List (Finset (Fin q))), 0 < q →
    PrefixSafe (SafePoint q full) (rawIncidenceROM q full) program natInitial
      (16384 * treeWork full.length q)

/-- Conditional assembly only: the remaining premise concerns registers,
code addresses and accesses, and does not contain tree/output/cost answers. -/
theorem fullClaims_of_prefixSafety (hsafety : PrefixSafety) : FullClaims := by
  refine ⟨262144, 16, program, by decide, by decide, ?_⟩
  intro q full hq
  let bits := indexWidth 16 full.length q
  let rom := rawIncidenceROM q full
  let heap : BitVec bits → BitVec bits := fun _ => BitVec.ofNat bits 0
  obtain ⟨steps, hsteps, hhalt, hflag, hcorrect, houtput⟩ :=
    RawTreePreprocessingNat.raw_preprocessing q full hq
  have hsafe : PrefixSafe (SafePoint q full) rom program natInitial steps :=
    PrefixSafe.mono _ _ _ _ hsteps (hsafety q full hq)
  obtain ⟨first, hfirst, hsame, hh, hbefore⟩ := exists_first_halt rom program natInitial steps hhalt
  have hword (count : Nat) (hc : count ≤ first) :
      packingRun rom program count (packingInitial heap) =
        (natRun rom program count natInitial).toWord bits := by
    change packingRun rom program count (natInitial.toWord bits) = _
    apply natRun_toWord rom program natInitial count (RawTreePreprocessingCostBounds.code_wordsFit full.length q)
    intro k hk
    have hs := hsafe k (hk.trans_le (hc.trans hfirst))
    exact ⟨hs.1, safePoint_pcFit q full _ hs⟩
  have hNatFlag : (natRun rom program first natInitial).register .value ≤ 1 := by
    rw [hsame]
    exact hflag
  have hflagFit : Fits bits ((natRun rom program first natInitial).register .value) :=
    RawTreePreprocessingCodeBounds.constant_fits full.length q _ (hNatFlag.trans (by decide))
  refine ⟨first, heapWords full.length q, ?_,
    RawTreePreprocessingCostBounds.totalCost_le q full hq first heap (hfirst.trans hsteps), ?_⟩
  · refine ⟨RawTreePreprocessingCostBounds.code_wordsFit full.length q, raw_rom_wordsFit q full,
      RawTreePreprocessingCostBounds.footprint_fits q full, ?_, ?_⟩
    · rw [hword first le_rfl]
      exact hh
    · intro count hc
      have hs := hsafe count (hc.trans_le hfirst)
      dsimp only
      rw [hword count hc.le]
      refine ⟨hbefore count hc, ?_, ?_⟩
      · change (BitVec.ofNat bits (natRun rom program count natInitial).pc).toNat + 4 < _
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (safePoint_pcFit q full _ hs)]
        exact safePoint_fetchWindow q full _ hs
      · rw [safePoint_physicalFetch q full _ hs]
        obtain ⟨_hr, _index, _hi, _hp, ha⟩ := hs
        have ha' := ha (hbefore count hc)
        cases hd : PackingOp.decode (natFetch program (natRun rom program count natInitial).pc) with
        | none => simpa only [hd] using ha'
        | some op =>
          apply physical_access_of_nat rom (heapWords full.length q) _ op _hr
          simpa only [hd] using ha'
  · rw [hword first le_rfl]
    refine ⟨?_, ?_, ?_⟩
    · change (BitVec.ofNat bits ((natRun rom program first natInitial).register .value)).toNat ≤ 1
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hflagFit]
      exact hNatFlag
    · change (BitVec.ofNat bits ((natRun rom program first natInitial).register .value)).toNat = 1 ↔ _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hflagFit, hsame]
      exact hcorrect
    · intro hl
      apply wordOutput_of_natOutput q full hq hl
      rw [hsame]
      exact houtput hl

end PaperProofs.Structure.LaminarTree.RawTreePreprocessingWordInterface
