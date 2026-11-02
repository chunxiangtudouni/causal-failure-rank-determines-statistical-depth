module

public import Structure.PA06_A19Prepare_CompactOrdering034Loop
public import Structure.PA06_A19Prepare_CompactRetention030Entry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! One actual checker→gate→initialization→398-retention→303-sort run.
All source tables and numerical qualifications are produced by that run.
The generic Nat sorting semantics remain unchanged. Internal all-clock
Nat certificates are consumed by true input-tail ROM/Word transport. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactOrdering034Entry

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety

abbrev orderingStart := PA06A19PrepareCompactCandidates007.Metadata.orderingStart
abbrev retentionStart := PA06A19PrepareCompactCandidates007.Metadata.retentionStart
abbrev linearLimit := PA06A19PrepareCompactWord008.linearLimit
abbrev frontProgram := PA06A19PrepareCompactRetention030Entry.program
abbrev Point := PA06A19PrepareCompactRetention030Entry.Point

def suffix (tail : List PackingOp) : List PackingOp := RawCandidateOrderingRAM.programAt orderingStart ++ tail
def program (tail : List PackingOp) : List PackingOp := frontProgram (suffix tail)

theorem program_eq_ordered (tail : List PackingOp) :
    program tail = PA06A19PrepareCompactCandidates007.Metadata.orderedProgram tail := rfl

theorem program_eq_front (tail : List PackingOp) :
    program tail = PA06A19PrepareCompactCandidates007.Metadata.program (suffix tail) := rfl

theorem ordering_slice (tail : List PackingOp) :
    orderingStart + 303 ≤ (program tail).length ∧
      ∀ position < 303, (program tail).getD (orderingStart + position) RawCandidateOrderingRAM.paddingOp =
        (RawCandidateOrderingRAM.programAt orderingStart).getD position RawCandidateOrderingRAM.paddingOp := by
  have slice := RawCandidateOrderingRAM.append_slice
    (PA06A19PrepareCompactCandidates007.Metadata.orderingFront tail) tail
  rw [PA06A19PrepareCompactCandidates007.Metadata.orderedProgram_eq tail] at slice
  simpa only [program_eq_ordered,
    PA06A19PrepareCompactCandidates007.Metadata.orderingFront_length] using slice

theorem retention_slice (tail : List PackingOp) :
    retentionStart + 398 ≤ (program tail).length ∧
      ∀ position < 398, (program tail).getD (retentionStart + position) RawCandidateRetentionRAM.paddingOp =
        (RawCandidateRetentionRAM.programAt retentionStart).getD position RawCandidateRetentionRAM.paddingOp := by
  have slice := RawCandidateRetentionRAM.append_slice
    (PA06A19PrepareCompactCandidates007.Metadata.front (suffix tail)) (suffix tail)
  rw [PA06A19PrepareCompactCandidates007.Metadata.program_eq (suffix tail)] at slice
  simpa only [program_eq_front,
    PA06A19PrepareCompactCandidates007.Metadata.front_length] using slice

/-- A decoded real-code state becomes the common actual-run point.
This is an internal change of representation, with no new safe-run
assumption in either public entry theorem. -/
theorem point_of_decoded (q : Nat) (full : List (Finset (Fin q))) (tail : List PackingOp)
    (state : NatState) (registers : RegistersFit (indexWidth 32 full.length q) state)
    (pcFit : Fits (indexWidth 32 full.length q) state.pc) (active : state.halted = false)
    (index : Nat) (hi : index < (frontProgram tail).length) (pc : state.pc = 5 * index)
    (op : PackingOp) (decoded : PackingOp.decode (natFetch (frontProgram tail) state.pc) = some op)
    (access : NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q) state op) :
    Point q full tail state := by
  have actualDecode : PackingOp.decode (natFetch (frontProgram tail) state.pc) =
      some ((frontProgram tail)[index]'hi) := by
    rw [pc, natFetch_body (frontProgram tail) index hi, decode_encode]
  have opEq : op = (frontProgram tail)[index]'hi := Option.some.inj (decoded.symm.trans actualDecode)
  refine ⟨registers, pcFit, active, index, hi, pc, ?_⟩
  simpa only [opEq] using access

private theorem input_prefix (q : Nat) (full : List (Finset (Fin q))) (initialUsed : Finset (Fin q)) :
    PA06A19PrepareROM001.ROMPrefix (rawIncidenceROM q full)
      (CompactControllerClaims.controllerInput q full initialUsed) :=
  PA06A19PrepareROM001.inputTail_prefix _
    ((List.finRange q).map (fun tool => bit (decide (tool ∈ initialUsed))))

/-- Consume the common Nat point certificate once, obtaining actual Word
execution on the distinct controllerInput ROM and physical fetch/access
safety for every strict clock. This interface is shared by sort/parents. -/
theorem word_prefix_of_points (q : Nat) (full : List (Finset (Fin q))) (tail : List PackingOp)
    (initialUsed : Finset (Fin q)) (steps : Nat)
    (points : PrefixSafe (Point q full tail) (rawIncidenceROM q full) (frontProgram tail) natInitial steps)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode (frontProgram tail))) :
    (∀ count ≤ steps,
      packingRun (CompactControllerClaims.controllerInput q full initialUsed) (frontProgram tail) count
        (natInitial.toWord (indexWidth 32 full.length q)) =
          (natRun (rawIncidenceROM q full) (frontProgram tail) count natInitial).toWord (indexWidth 32 full.length q)) ∧
      ∀ count < steps,
        let actual := packingRun (CompactControllerClaims.controllerInput q full initialUsed) (frontProgram tail) count
          (natInitial.toWord (indexWidth 32 full.length q))
        actual.halted = false ∧ actual.pc.toNat + 4 < (packingCode (frontProgram tail)).length ∧
          ∃ op, PackingOp.decode (fetch (frontProgram tail) actual) = some op ∧
            packingAccessFits (CompactControllerClaims.controllerInput q full initialUsed) (linearLimit full.length q) actual op := by
  let bits := indexWidth 32 full.length q
  let runtime := CompactControllerClaims.controllerInput q full initialUsed
  have rawEq (count : Nat) (hc : count ≤ steps) :
      natRun runtime (frontProgram tail) count natInitial = natRun (rawIncidenceROM q full) (frontProgram tail) count natInitial := by
    apply PA06A19PrepareROM001.natRun_eq_of_romPrefix (input_prefix q full initialUsed) (linearLimit full.length q)
    intro clock hclock _active op decoded
    obtain ⟨_registers, _pcFit, _active, index, hi, pc, access⟩ := points clock (by omega)
    have actualDecode : PackingOp.decode (natFetch (frontProgram tail)
        (natRun (rawIncidenceROM q full) (frontProgram tail) clock natInitial).pc) = some ((frontProgram tail)[index]'hi) := by
      rw [pc, natFetch_body (frontProgram tail) index hi, decode_encode]
    have opEq : op = (frontProgram tail)[index]'hi := Option.some.inj (decoded.symm.trans actualDecode)
    subst op
    exact access
  have word (count : Nat) (hc : count ≤ steps) :
      packingRun runtime (frontProgram tail) count (natInitial.toWord bits) =
        (natRun (rawIncidenceROM q full) (frontProgram tail) count natInitial).toWord bits := by
    have actual := natRun_toWord runtime (frontProgram tail) natInitial count hwords (by
      intro clock hclock
      rw [rawEq clock (by omega)]
      have point := points clock (by omega)
      exact ⟨point.1, point.2.1⟩)
    exact actual.trans (congrArg (NatState.toWord bits) (rawEq count hc))
  refine ⟨word, ?_⟩
  intro count hc
  obtain ⟨registers, pcFit, active, index, hi, pc, access⟩ := points count hc
  change index < (frontProgram tail).length at hi
  dsimp only
  rw [word count hc.le]
  have wordPC : ((natRun (rawIncidenceROM q full) (frontProgram tail) count natInitial).toWord bits).pc.toNat = 5 * index := by
    change (BitVec.ofNat bits _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pcFit, pc]
  refine ⟨active, ?_, (frontProgram tail)[index]'hi, ?_, ?_⟩
  · rw [wordPC, packingCode_length]
    omega
  · change PackingOp.decode (physicalFetch bits (packingCode (frontProgram tail))
      ((natRun (rawIncidenceROM q full) (frontProgram tail) count natInitial).toWord bits).pc.toNat) = _
    rw [wordPC, physicalFetch_eq _ _ _ hwords]
    change PackingOp.decode (natFetch (frontProgram tail) (5 * index)) = _
    rw [natFetch_body (frontProgram tail) index hi, decode_encode]
  · apply physical_access_of_nat runtime (linearLimit full.length q) _ _ registers
    cases hop : (frontProgram tail)[index]'hi with
    | base instruction =>
      exact PA06A19PrepareROM001.accessFits_of_romPrefix (input_prefix q full initialUsed) (linearLimit full.length q) _ instruction
        (by simpa only [hop, RawIncidenceScanSafety.NatAccessFits,
          PA06A19PrepareCompactRetention030Entry.linearLimit] using access)
    | arithmetic operation target left right => trivial
    | jumpIfZero condition target => trivial

/-- Native certificate at the real sort endpoint. The before state in
Sorted belongs to this very execution, and all earlier phases remain in
the prefix certificate. All metadata premises are discharged internally. -/
theorem sorted_native_entry (q : Nat) (full : List (Finset (Fin q))) (tail : List PackingOp)
    (hlaminar : LaminarSchedule full)
    (hend : Fits (indexWidth 32 full.length q) (5 * (program tail).length)) :
    ∃ first ≤ checkerSteps full.length q + 17 + RawCandidateRetentionRAM.totalSteps full.length q,
      let clock := first + RawCandidateOrderingRAM.totalSteps (full.length + q + 1)
      let before := natRun (rawIncidenceROM q full) (program tail) first natInitial
      let after := natRun (rawIncidenceROM q full) (program tail) clock natInitial
      PrefixSafe (Point q full (suffix tail)) (rawIncidenceROM q full) (program tail) natInitial clock ∧
        RegistersFit (indexWidth 32 full.length q) after ∧
        RawCandidateOrderingRAM.Sorted q full 16 orderingStart before after ∧
        ∀ address, 16 + 5 + 4 * (full.length + q + 1) ≤ address → after.heap address = 0 := by
  let M := full.length + q + 1
  let rtime := RawCandidateRetentionRAM.totalSteps full.length q
  let stime := RawCandidateOrderingRAM.totalSteps M
  obtain ⟨initClock, initBound, front⟩ :=
    PA06A19PrepareCompactRetention030Entry.initialized_front q full (suffix tail) hlaminar hend
  let initialized := natRun (rawIncidenceROM q full) (program tail) initClock natInitial
  have rslice := retention_slice tail
  have sslice := ordering_slice tail
  have rend : Fits (indexWidth 32 full.length q) (5 * (retentionStart + 398)) :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 5 rslice.1) hend
  have send : Fits (indexWidth 32 full.length q) (5 * (orderingStart + 303)) :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 5 sslice.1) hend
  have rsafe := PA06A19PrepareCompactRetention030Loop.retention_nat_safe q full (program tail) retentionStart
    rslice.1 rslice.2 initialized front.pointer front.header front.pc front.active front.registers rend
  have rnative := PA06A19PrepareCompactRetention030Loop.retention_native_output q full (program tail) retentionStart
    rslice.1 rslice.2 initialized front.pointer front.header front.pc front.active
  dsimp only at rnative
  let retained := natRun (rawIncidenceROM q full) (program tail) rtime initialized
  have retainedRun : natRun (rawIncidenceROM q full) (program tail) (initClock + rtime) natInitial = retained :=
    natRun_add _ _ _ _ _
  have tables : RawCandidateOrderingRAM.InputTables 16 M
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) retained := by
    constructor
    · intro index hi
      simpa only [RawCandidateOrderingRAM.arraySlot, Nat.mul_zero, Nat.add_zero,
        RawCandidateStableOrder.candidateCard, RawCandidateRetentionRAM.cardAddress] using (rnative.2.2.2.1 index hi).1
    · intro index hi
      simpa only [M, RawCandidateOrderingRAM.arraySlot, Nat.mul_one,
        RawCandidateRetentionRAM.keepAddress, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (rnative.2.2.2.1 index hi).2
  have retainedZero (address : Nat) (above : 16 + 4 + 2 * M ≤ address) : retained.heap address = 0 := by
    have outside : RawCandidateRetentionRAM.OutsideWorkspace 16 M address :=
      ⟨by omega, by omega, by omega, by omega, Or.inr above⟩
    exact (rnative.2.2.2.2.1 address outside).trans (front.zero address (by omega) (by omega) (by omega))
  have ordFit : PA06A19PrepareCompactOrdering034Data.OrdFits q full retained := by
    intro index hi
    rw [retainedZero _ (by unfold RawCandidateOrderingRAM.arraySlot; omega)]
    exact PA06A19PrepareCompactMacros014.small_constant_fits full.length q 0 (by decide)
  have rpc : retained.pc = 5 * orderingStart := rnative.2.2.2.2.2.1
  have ra : retained.halted = false := rnative.2.2.2.2.2.2
  have ssafe := PA06A19PrepareCompactOrdering034Loop.sort_nat_safe q full (program tail) orderingStart sslice.1 sslice.2
    retained rsafe.2.1 rnative.1 rnative.2.1 tables ordFit rpc ra send
  have snative := RawCandidateOrderingRAM.sort (rawIncidenceROM q full) (program tail) orderingStart sslice.1 sslice.2
    q full 16 retained (by decide) rnative.1 rnative.2.1 tables rpc ra
  have rpoints : PrefixSafe (Point q full (suffix tail)) (rawIncidenceROM q full) (program tail) initialized rtime := by
    intro count hc
    have point := rsafe.1 count hc
    have pcFit := PA06A19PrepareCompactRetention030Parts.point_pcFits point rend
    obtain ⟨registers, offset, hoff, pc, active, op, decoded, access⟩ := point
    exact point_of_decoded q full (suffix tail) _ registers pcFit active (retentionStart + offset)
      (by change retentionStart + offset < (program tail).length; omega)
      pc op decoded access
  have spoints : PrefixSafe (Point q full (suffix tail)) (rawIncidenceROM q full) (program tail) retained stime := by
    intro count hc
    have point := ssafe.1 count hc
    have pcFit := point.pcFits send
    obtain ⟨registers, offset, hoff, pc, active, op, decoded, access⟩ := point
    exact point_of_decoded q full (suffix tail) _ registers pcFit active (orderingStart + offset)
      (by change orderingStart + offset < (program tail).length; omega)
      pc op decoded access
  have beforePoints : PrefixSafe (Point q full (suffix tail)) (rawIncidenceROM q full) (program tail) natInitial
      (initClock + rtime) := PrefixSafe.add _ _ _ _ _ _ front.before_points rpoints
  have wholePoints : PrefixSafe (Point q full (suffix tail)) (rawIncidenceROM q full) (program tail) natInitial
      ((initClock + rtime) + stime) := by
    apply PrefixSafe.add _ _ _ _ _ _ beforePoints
    rw [retainedRun]
    exact spoints
  have finalRun : natRun (rawIncidenceROM q full) (program tail) ((initClock + rtime) + stime) natInitial =
      natRun (rawIncidenceROM q full) (program tail) stime retained := by
    rw [natRun_add, retainedRun]
  refine ⟨initClock + rtime, by omega, ?_⟩
  dsimp only
  refine ⟨wholePoints, ?_, ?_, ?_⟩
  · rw [finalRun]
    exact ssafe.2
  · rw [retainedRun, finalRun]
    exact snative
  · intro address above
    rw [finalRun]
    have hprotected : RawCandidateOrderingRAM.ProtectedAddress 16 M address := by
      refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩
      · intro index hi
        unfold RawCandidateOrderingRAM.arraySlot
        omega
      · intro index hi
        unfold RawCandidateOrderingRAM.arraySlot
        omega
      · unfold RawCandidateOrderingRAM.arraySlot
        omega
    rw [snative.frame address hprotected]
    exact retainedZero address (by omega)

/-- Public same-run sorter entry. Laminar input and code arithmetic are
the only qualifiers; actual card/keep/order/inverse tables are outputs. -/
theorem sorted_entry (q : Nat) (full : List (Finset (Fin q))) (tail : List PackingOp)
    (initialUsed : Finset (Fin q)) (hlaminar : LaminarSchedule full)
    (hend : Fits (indexWidth 32 full.length q) (5 * (program tail).length))
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode (program tail))) :
    ∃ first ≤ checkerSteps full.length q + 17 + RawCandidateRetentionRAM.totalSteps full.length q,
      let clock := first + RawCandidateOrderingRAM.totalSteps (full.length + q + 1)
      let after := natRun (rawIncidenceROM q full) (program tail) clock natInitial
      RawCandidateOrderingRAM.Sorted q full 16 orderingStart
        (natRun (rawIncidenceROM q full) (program tail) first natInitial) after ∧
        RegistersFit (indexWidth 32 full.length q) after ∧
        (∀ count ≤ clock,
          packingRun (CompactControllerClaims.controllerInput q full initialUsed) (program tail) count
            (natInitial.toWord (indexWidth 32 full.length q)) =
              (natRun (rawIncidenceROM q full) (program tail) count natInitial).toWord (indexWidth 32 full.length q)) ∧
        (∀ count < clock,
          let actual := packingRun (CompactControllerClaims.controllerInput q full initialUsed) (program tail) count
            (natInitial.toWord (indexWidth 32 full.length q))
          actual.halted = false ∧ actual.pc.toNat + 4 < (packingCode (program tail)).length ∧
            ∃ op, PackingOp.decode (fetch (program tail) actual) = some op ∧
              packingAccessFits (CompactControllerClaims.controllerInput q full initialUsed) (linearLimit full.length q) actual op) ∧
        ∀ address, 16 + 5 + 4 * (full.length + q + 1) ≤ address → after.heap address = 0 := by
  obtain ⟨first, bound, points, registers, sorted, zero⟩ := sorted_native_entry q full tail hlaminar hend
  have words := word_prefix_of_points q full (suffix tail) initialUsed
    (first + RawCandidateOrderingRAM.totalSteps (full.length + q + 1)) points hwords
  exact ⟨first, bound, sorted, registers, words.1, words.2, zero⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactOrdering034Entry

