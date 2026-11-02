module

public import PaperProofs.Structure.RawCandidateSerializedInputRun
public import PaperProofs.Structure.RawCandidateSerializedChildrenRun
public import PaperProofs.Structure.RawTreeOutputFinalizeRAM

/-! Assemble the executed serializer phases and the executed footer.
This is the natural-address execution layer; it does not assert the
whole-program physical-word/access/cost obligations of A06. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateSerializationAssembly

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawTreeSerialization

theorem serialized_words (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hl : LaminarSchedule full) (pointer : Nat) (before after : NatState)
    (hprefix : ∀ position < RawCandidateSerializedInputLayout.prefixLength q full,
      before.heap position = (serializeROM (givenTreeROM q full)).getD position 0)
    (output : RawCandidateSerializedChildrenRun.Output q full pointer before after) :
    ∀ position < (serializeROM (givenTreeROM q full)).length,
      after.heap position = (serializeROM (givenTreeROM q full)).getD position 0 := by
  let rom := givenTreeROM q full
  have hprefixLength : RawCandidateSerializedInputLayout.prefixLength q full =
      RawCandidateSerializedChildrenRAM.internalStart q full := by
    simp only [RawCandidateSerializedInputLayout.prefixLength,
      RawCandidateSerializedChildrenRAM.internalStart, givenTreeROM_input_length]
    omega
  have hchildStart : RawCandidateSerializedChildrenRAM.childrenStart q full =
      3 + rom.input.length + rom.internal.length := by
    simp only [RawCandidateSerializedChildrenRAM.childrenStart,
      RawCandidateSerializedChildrenRAM.internalStart, givenTreeROM_internal_length,
      RawCandidateSerializedChildrenRAM.size, rom]
  have hlength : (serializeROM rom).length =
      3 + rom.input.length + rom.internal.length + rom.children.length := by
    rw [serializeROM_length, PhysicalROM.size]
    omega
  intro position hposition
  by_cases hp : position < RawCandidateSerializedChildrenRAM.internalStart q full
  · rw [output.prefix_frame hq hl position hp]
    exact hprefix position (hprefixLength.symm ▸ hp)
  · have hs : RawCandidateSerializedChildrenRAM.internalStart q full ≤ position := by omega
    by_cases hi : position < RawCandidateSerializedChildrenRAM.childrenStart q full
    · let offset := position - RawCandidateSerializedChildrenRAM.internalStart q full
      have heq : position = RawCandidateSerializedChildrenRAM.internalStart q full + offset := by
        dsimp [offset]; omega
      have hoffset : offset < rom.internal.length := by
        have hlow : 3 + rom.input.length ≤ position := hs
        have hhigh : position < 3 + rom.input.length + rom.internal.length := by
          rwa [← hchildStart]
        change position - (3 + rom.input.length) < rom.internal.length
        omega
      rw [heq, output.internal offset hoffset]
      have hh := serializeROM_getD_internal rom offset hoffset
      rw [← List.getD_eq_getElem _ 0 hoffset] at hh
      exact hh.symm
    · let offset := position - RawCandidateSerializedChildrenRAM.childrenStart q full
      have heq : position = RawCandidateSerializedChildrenRAM.childrenStart q full + offset := by
        dsimp [offset]; omega
      have hoffset : offset < rom.children.length := by
        have hlow : 3 + rom.input.length + rom.internal.length ≤ position := by
          rw [← hchildStart]
          omega
        have hhigh : position < 3 + rom.input.length + rom.internal.length + rom.children.length := by
          rw [← hlength]
          exact hposition
        dsimp only [offset]
        rw [hchildStart]
        omega
      rw [heq, output.children offset hoffset]
      have hh := serializeROM_getD_children rom offset hoffset
      rw [← List.getD_eq_getElem _ 0 hoffset, ← hchildStart] at hh
      exact hh.symm

/-- The footer reads real region-length and node-count heads, restores the
success flag, and consumes the actual trailing HALT instruction. -/
theorem finalize (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hl : LaminarSchedule full) (left : List PackingOp) (state : NatState)
    (hheaders : RawCandidateSerializedReady.HeaderSpec q full state)
    (hwords : ∀ position < (serializeROM (givenTreeROM q full)).length,
      state.heap position = (serializeROM (givenTreeROM q full)).getD position 0)
    (hpc : state.pc = 5 * left.length) (hactive : state.halted = false) :
    let result := natRun (rawIncidenceROM q full) (left ++ RawTreeOutputFinalizeRAM.program) 14 state
    result.halted = true ∧ result.register .value = 1 ∧
      result.register .old = (prepareNormalization q full).indexed.nodes.size ∧
      result.register .fresh = (serializeROM (givenTreeROM q full)).length ∧
      ∀ position < (serializeROM (givenTreeROM q full)).length,
        result.heap position = (serializeROM (givenTreeROM q full)).getD position 0 := by
  have h0 : state.heap 0 = (givenTreeROM q full).input.length := by
    simpa only [List.getD_cons_zero, givenTreeROM_input_length] using hheaders 0 (by decide)
  have h1 : state.heap 1 = (givenTreeROM q full).internal.length := by
    simpa [givenTreeROM_internal_length] using hheaders 1 (by decide)
  have h2 : state.heap 2 = (givenTreeROM q full).children.length := by
    simpa [givenTreeROM_children_length q full hq hl] using hheaders 2 (by decide)
  have h5 := hheaders.count
  have hf := RawTreeOutputFinalizeRAM.finalize_halt (rawIncidenceROM q full) left state
    (givenTreeROM q full).input.length (givenTreeROM q full).internal.length
    (givenTreeROM q full).children.length (prepareNormalization q full).indexed.nodes.size
    h0 h1 h2 h5 hpc hactive
  dsimp only at hf ⊢
  rcases hf with ⟨hheap, hnodes, hlength, hvalue, hhalt⟩
  refine ⟨hhalt, hvalue, hnodes, ?_, ?_⟩
  · rw [hlength, serializeROM_length, PhysicalROM.size]
    omega
  · intro position hp
    rw [hheap]
    exact hwords position hp

end PaperProofs.Structure.LaminarTree.RawCandidateSerializationAssembly
