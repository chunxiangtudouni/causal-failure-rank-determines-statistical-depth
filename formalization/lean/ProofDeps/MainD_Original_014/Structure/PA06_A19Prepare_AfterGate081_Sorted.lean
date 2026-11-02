module

public import Structure.PA06_A19Prepare_AfterGate081_Control

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED actual398 retention followed by actual303 sorting in the
supplied containing code.  Both deterministic clocks and all source array
facts refer to the one real intermediate state. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareAfterGate081

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety

def retentionClock (N q : Nat) : Nat := RawCandidateRetentionRAM.totalSteps N q
def orderingClock (N q : Nat) : Nat := RawCandidateOrderingRAM.totalSteps (N + q + 1)

theorem retained_sorted (q : Nat) (full : List (Finset (Fin q)))
    (whole : List PackingOp) (retention : RetentionAt whole) (ordering : OrderingAt whole)
    (before : NatState) (entry : Initialized q full before)
    (hend : Fits (bits q full) (5 * whole.length)) :
    let retained := natRun (rawIncidenceROM q full) whole (retentionClock full.length q) before
    let clock := retentionClock full.length q + orderingClock full.length q
    let sorted := natRun (rawIncidenceROM q full) whole clock before
    PrefixSafe (Point q full whole) (rawIncidenceROM q full) whole before clock ∧
      RegistersFit (bits q full) sorted ∧
      RawCandidateOrderingRAM.Sorted q full 16 orderingStart retained sorted ∧
      ∀ address, 16 + 5 + 4 * (full.length + q + 1) <= address → sorted.heap address = 0 := by
  let rom := rawIncidenceROM q full
  let M := full.length + q + 1
  let rtime := retentionClock full.length q
  let stime := orderingClock full.length q
  let retained := natRun rom whole rtime before
  have rend : Fits (bits q full) (5 * (retentionStart + 398)) :=
    (Nat.mul_le_mul_left 5 retention.1).trans_lt hend
  have send : Fits (bits q full) (5 * (orderingStart + 303)) :=
    (Nat.mul_le_mul_left 5 ordering.1).trans_lt hend
  have rsafe := PA06A19PrepareCompactRetention030Loop.retention_nat_safe q full whole retentionStart
    retention.1 retention.2 before entry.pointer entry.header entry.pc entry.active entry.registers rend
  have rnative := PA06A19PrepareCompactRetention030Loop.retention_native_output q full whole retentionStart
    retention.1 retention.2 before entry.pointer entry.header entry.pc entry.active
  dsimp only at rnative
  have tables : RawCandidateOrderingRAM.InputTables 16 M
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) retained := by
    constructor
    · intro index hi
      simpa only [retained, rom, rtime, retentionClock,
        RawCandidateOrderingRAM.arraySlot, Nat.mul_zero, Nat.add_zero,
        RawCandidateStableOrder.candidateCard, RawCandidateRetentionRAM.cardAddress] using (rnative.2.2.2.1 index hi).1
    · intro index hi
      simpa only [retained, rom, rtime, retentionClock, M, RawCandidateOrderingRAM.arraySlot, Nat.mul_one,
        RawCandidateRetentionRAM.keepAddress, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (rnative.2.2.2.1 index hi).2
  have retainedZero (address : Nat) (above : 16 + 4 + 2 * M <= address) : retained.heap address = 0 := by
    have outside : RawCandidateRetentionRAM.OutsideWorkspace 16 M address :=
      ⟨by omega, by omega, by omega, by omega, Or.inr above⟩
    exact (rnative.2.2.2.2.1 address outside).trans (entry.zero address (by omega) (by omega) (by omega))
  have ordFit : PA06A19PrepareCompactOrdering034Data.OrdFits q full retained := by
    intro index hi
    rw [retainedZero _ (by unfold RawCandidateOrderingRAM.arraySlot; omega)]
    exact PA06A19PrepareCompactMacros014.small_constant_fits full.length q 0 (by decide)
  have rpc : retained.pc = 5 * orderingStart := rnative.2.2.2.2.2.1
  have ra : retained.halted = false := rnative.2.2.2.2.2.2
  have ssafe := PA06A19PrepareCompactOrdering034Loop.sort_nat_safe q full whole orderingStart
    ordering.1 ordering.2 retained rsafe.2.1 rnative.1 rnative.2.1 tables ordFit rpc ra send
  have snative := RawCandidateOrderingRAM.sort rom whole orderingStart ordering.1 ordering.2
    q full 16 retained (by decide) rnative.1 rnative.2.1 tables rpc ra
  have rpoints : PrefixSafe (Point q full whole) rom whole before rtime := by
    intro count hc
    obtain ⟨registers, offset, hoff, pc, active, op, decoded, access⟩ := rsafe.1 count hc
    exact point_of_local q full whole retentionStart 398 (Or.inl ⟨rfl, rfl⟩)
      retention.1 rend _ registers active offset hoff pc op decoded access
  have spoints : PrefixSafe (Point q full whole) rom whole retained stime := by
    intro count hc
    obtain ⟨registers, offset, hoff, pc, active, op, decoded, access⟩ := ssafe.1 count hc
    exact point_of_local q full whole orderingStart 303 (Or.inr (Or.inl ⟨rfl, rfl⟩))
      ordering.1 send _ registers active offset hoff pc op decoded access
  have wholePoints := PrefixSafe.add (Point q full whole) rom whole before rtime stime rpoints spoints
  have finalRun : natRun rom whole (rtime + stime) before = natRun rom whole stime retained :=
    natRun_add rom whole rtime stime before
  dsimp only
  refine ⟨wholePoints, ?_, ?_, ?_⟩
  · rw [finalRun]
    exact ssafe.2
  · rw [finalRun]
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
    have sortedFrame : (natRun rom whole stime retained).heap address = retained.heap address := by
      simpa only [stime, orderingClock] using snative.frame address hprotected
    rw [sortedFrame]
    exact retainedZero address (by omega)

end PaperProofs.Structure.LaminarTree.PA06A19PrepareAfterGate081
