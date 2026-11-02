module

public import Structure.PA06_A19Prepare_AfterGate081
public import Structure.PA06_A19Prepare_InitialUsed037_Prefix
public import Structure.PA06_A19Prepare_ROM_001

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED physical transport of the actual generic compact run.
The raw/controller ROM comparison and Word refinement preserve every
selected clock, and keep the original local PC windows explicit. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareAfterGate081

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety CompactControllerClaims

theorem word_prefix_of_points (q : Nat) (full : List (Finset (Fin q)))
    (used : Finset (Fin q)) (whole : List PackingOp) (before : NatState) (steps : Nat)
    (points : PrefixSafe (Point q full whole) (rawIncidenceROM q full) whole before steps)
    (hwords : WordsFit (bits q full) (packingCode whole)) :
    (∀ count ≤ steps,
      packingRun (controllerInput q full used) whole count (before.toWord (bits q full)) =
        (natRun (rawIncidenceROM q full) whole count before).toWord (bits q full)) ∧
      ∀ count < steps,
        let actual := packingRun (controllerInput q full used) whole count (before.toWord (bits q full))
        5 * retentionStart <= actual.pc.toNat ∧ actual.pc.toNat < 5 * inputStart ∧
          PA06A19PrepareInitialUsed037.Fetched (linearLimit full.length q)
            (controllerInput q full used) whole actual := by
  let runtime := controllerInput q full used
  have hprefix : PA06A19PrepareROM001.ROMPrefix (rawIncidenceROM q full) runtime :=
    PA06A19PrepareROM001.inputTail_prefix (rawIncidenceROM q full)
      ((List.finRange q).map (fun tool => bit (decide (tool ∈ used))))
  have rawEq (count : Nat) (hc : count <= steps) :
      natRun runtime whole count before = natRun (rawIncidenceROM q full) whole count before := by
    apply PA06A19PrepareROM001.natRun_eq_of_romPrefix hprefix (linearLimit full.length q)
    intro clock hclock _active op decoded
    obtain ⟨_registers, _pcFit, _a, _start, _width, _offset, _segment, _hoff, _bound, _pc,
      actualOp, actualDecode, access⟩ := points clock (by omega)
    have opEq : op = actualOp := Option.some.inj (decoded.symm.trans actualDecode)
    subst op
    exact access
  have word (count : Nat) (hc : count <= steps) :
      packingRun runtime whole count (before.toWord (bits q full)) =
        (natRun (rawIncidenceROM q full) whole count before).toWord (bits q full) := by
    have actual := natRun_toWord runtime whole before count hwords (by
      intro clock hclock
      rw [rawEq clock (by omega)]
      have point := points clock (by omega)
      exact ⟨point.1, point.2.1⟩)
    exact actual.trans (congrArg (NatState.toWord (bits q full)) (rawEq count hc))
  refine ⟨word, ?_⟩
  intro count hc
  have point := points count hc
  have window := point.pc_window
  obtain ⟨registers, pcFit, active, start, _width, offset, _segment, _hoff, bound, pc,
    op, decoded, access⟩ := point
  have wordPC : ((natRun (rawIncidenceROM q full) whole count before).toWord (bits q full)).pc.toNat =
      (natRun (rawIncidenceROM q full) whole count before).pc := by
    change (BitVec.ofNat (bits q full) _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pcFit]
  dsimp only
  rw [word count hc.le]
  refine ⟨?_, ?_, active, ?_, op, ?_, ?_⟩
  · rw [wordPC]
    exact window.1
  · rw [wordPC]
    exact window.2
  · rw [wordPC, pc, packingCode_length]
    omega
  · change PackingOp.decode (physicalFetch (bits q full) (packingCode whole)
        ((natRun (rawIncidenceROM q full) whole count before).toWord (bits q full)).pc.toNat) = some op
    rw [wordPC, physicalFetch_eq _ _ _ hwords]
    exact decoded
  · apply physical_access_of_nat runtime (linearLimit full.length q) _ _ registers
    cases op with
    | base instruction =>
      exact PA06A19PrepareROM001.accessFits_of_romPrefix hprefix (linearLimit full.length q) _ instruction
        (by simpa only [RawIncidenceScanSafety.NatAccessFits] using access)
    | arithmetic operation target left right => trivial
    | jumpIfZero condition target => trivial

private theorem word_data_of_refinement (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (native : NatState) (actual : WordState (bits q full))
    (entry : ParentEntry q full native)
    (ordinal : PA06A19PrepareCompactParents035Ord.OrdDataNat q full native)
    (pcFit : Fits (bits q full) (5 * PA06A19PrepareCompactCandidates007.inputStart))
    (refinement : actual = native.toWord (bits q full)) :
    PA06A19PrepareCompactParents035Entry.WordParents q full actual ∧
      PA06A19PrepareCompactParents035Ord.OrdData q full actual ∧
      PA06A19PrepareCompactParents035Cards.CardData q full actual := by
  rw [refinement]
  refine ⟨?_, ?_, ?_⟩
  · apply PA06A19PrepareCompactParents035Entry.wordParents_of_native q full hq native entry
    simpa only [bits, PA06A19PrepareCompactParents035Entry.inputStart,
      PA06A19PrepareCompactCandidates007.inputStart_eq] using pcFit
  · exact (PA06A19PrepareCompactParents035Ord.ord_data_toWord q full native ordinal).1
  · exact PA06A19PrepareCompactParents035Cards.card_data_of_native q full native
      (native.toWord (bits q full)) entry rfl

/-- Parent/ord/card data and all fetched compact prefixes belong to this
one actual controllerInput run from the supplied initialized state. -/
theorem after_gate_word (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (whole : List PackingOp) (retention : RetentionAt whole)
    (ordering : OrderingAt whole) (parents : ParentsAt whole)
    (before : NatState) (initialized : Initialized q full before)
    (hend : Fits (bits q full) (5 * whole.length))
    (hwords : WordsFit (bits q full) (packingCode whole)) :
    ∃ clock ≤ clockBound q full,
      let native := natRun (rawIncidenceROM q full) whole clock before
      let actual := packingRun (controllerInput q full used) whole clock (before.toWord (bits q full))
      ParentEntry q full native ∧ PA06A19PrepareCompactArrays018.InverseValuesBound q full native ∧
        RegistersFit (bits q full) native ∧
        PA06A19PrepareCompactParents035Entry.WordParents q full actual ∧
        PA06A19PrepareCompactParents035Ord.OrdData q full actual ∧
        PA06A19PrepareCompactParents035Cards.CardData q full actual ∧
        (∀ count ≤ clock,
          packingRun (controllerInput q full used) whole count (before.toWord (bits q full)) =
            (natRun (rawIncidenceROM q full) whole count before).toWord (bits q full)) ∧
        ∀ count < clock,
          let current := packingRun (controllerInput q full used) whole count (before.toWord (bits q full))
          5 * retentionStart <= current.pc.toNat ∧ current.pc.toNat < 5 * inputStart ∧
            PA06A19PrepareInitialUsed037.Fetched (linearLimit full.length q)
              (controllerInput q full used) whole current := by
  obtain ⟨clock, bound, points, registers, entry, inverse, ordinal, _cards, _pc, _active⟩ :=
    after_gate_native q full hq whole retention ordering parents before initialized hend
  have bridge := word_prefix_of_points q full used whole before clock points hwords
  have pend : Fits (bits q full) (5 * PA06A19PrepareCompactCandidates007.inputStart) := by
    rw [PA06A19PrepareCompactCandidates007.inputStart_eq]
    exact (Nat.mul_le_mul_left 5 parents.1).trans_lt hend
  have wordData := word_data_of_refinement q full hq
    (natRun (rawIncidenceROM q full) whole clock before)
    (packingRun (controllerInput q full used) whole clock (before.toWord (bits q full)))
    entry ordinal pend (bridge.1 clock le_rfl)
  refine ⟨clock, bound, ?_⟩
  dsimp only
  exact ⟨entry, inverse, registers, wordData.1, wordData.2.1, wordData.2.2, bridge.1, bridge.2⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareAfterGate081
