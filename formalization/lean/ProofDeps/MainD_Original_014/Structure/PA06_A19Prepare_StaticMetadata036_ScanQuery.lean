module

public import Structure.PA06_A19Prepare_StaticMetadata036_ScanSemantics

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Exact Nat execution of the frozen022 actual bit query, with numeric
Word bounds intentionally separated. This reuses its real raw32 run rather
than passing a membership answer or an entire-run proof to the scanner. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (preparedSize mass)

abbrev ScanQueryCodeAt := PA06A19PrepareBankNodeBit022.CodeAt

def nodeReadClock (N : Nat) (heap : Nat → Nat) (CB M node tool : Nat) : Nat :=
  14 + PA06A19PrepareBankNodeBit022Raw.steps N (heap (rawOrdAddress CB M node)) tool

theorem nodeReadClock_le (N : Nat) (heap : Nat → Nat) (CB M node tool : Nat) :
    nodeReadClock N heap CB M node tool ≤ 33 := by
  have h := PA06A19PrepareBankNodeBit022Raw.steps_le N (heap (rawOrdAddress CB M node)) tool
  unfold nodeReadClock
  omega

theorem nodeBit_prefix_run (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start : Nat) (code : ScanQueryCodeAt containing start)
    (state : NatState) (hpc : state.pc = 5 * start) (ha : state.halted = false) :
    natRun (rawIncidenceROM q full) containing 14 state =
      runOps (rawIncidenceROM q full) PA06A19PrepareBankNodeBit022.prefix14 state := by
  apply natRun_of_straight_segment _ containing PA06A19PrepareBankNodeBit022.prefix14 start
    (by have h := code.1; rw [PA06A19PrepareBankNodeBit022.prefix14_length]; omega)
    ?_ PA06A19PrepareBankNodeBit022.prefix14_noJump state hpc ha
  intro position hp
  have hi : position < 14 := by simpa only [PA06A19PrepareBankNodeBit022.prefix14_length] using hp
  have h := code.2 position (by omega)
  rw [PA06A19PrepareBankNodeBit022.programAt,
    List.getD_append _ _ _ _ (by rw [PA06A19PrepareBankNodeBit022.prefix14_length]; exact hi)] at h
  have hcontaining : start + position < containing.length := by
    have hbound := code.1
    omega
  rw [List.getD_eq_getElem _ _ hcontaining, List.getD_eq_getElem _ _ hp] at h
  exact h

theorem nodeBit_prefix_effect (q : Nat) (full : List (Finset (Fin q)))
    (CB node candidate : Nat) (state : NatState)
    (hn : state.register .old = node) (hCB : state.register .address = CB)
    (ho : state.heap (rawOrdAddress CB (mass q full) node) = candidate) :
    let after := runOps (rawIncidenceROM q full) PA06A19PrepareBankNodeBit022.prefix14 state
    after.register .old = candidate ∧ after.register .fresh = state.register .fresh ∧
      after.register .address = CB ∧ after.heap = state.heap ∧
      after.pc = state.pc + 70 ∧ after.halted = state.halted := by
  simp [PA06A19PrepareBankNodeBit022.prefix14, runOps, natExecuteOp, natArithmetic,
    Op.execute, Instruction.execute, raw_header_N, raw_header_q, hn, hCB, rawOrdAddress,
    mass, Nat.mul_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at ho ⊢
  exact ho

/-- Full true46-op query call. The dynamic step count is calculated from
its real source ord cell. Arbitrarily large Nat caller registers are allowed;
Word eligibility is a separate later refinement of this actual run. -/
theorem nodeBit_nat_read (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start : Nat) (code : ScanQueryCodeAt containing start)
    (CB : Nat) (state : NatState) (data : RawCardData q full CB state)
    (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q)
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hn : state.register .old = node.val) (htool : state.register .fresh = tool.val)
    (hCB : state.register .address = CB) :
    let after := natRun (rawIncidenceROM q full) containing
      (nodeReadClock full.length state.heap CB (mass q full) node.val tool.val) state
    after.register .value = rawCandidateBit (rawIncidenceROM q full)
        (state.heap (rawOrdAddress CB (mass q full) node.val)) tool.val ∧
      after.register .fresh = tool.val ∧ after.register .address = CB ∧ after.heap = state.heap ∧
      after.pc = 5 * (start + 46) ∧ after.halted = false := by
  obtain ⟨candidate, hord, hsupport⟩ := data.ordered node
  let middle := runOps (rawIncidenceROM q full) PA06A19PrepareBankNodeBit022.prefix14 state
  have hm := nodeBit_prefix_effect q full CB node.val candidate.val state hn hCB hord
  change middle.register .old = candidate.val ∧ middle.register .fresh = state.register .fresh ∧
    middle.register .address = CB ∧ middle.heap = state.heap ∧
    middle.pc = state.pc + 70 ∧ middle.halted = state.halted at hm
  have hmPC : middle.pc = 5 * (start + 14) := by rw [hm.2.2.2.2.1, hpc]; omega
  have hmActive : middle.halted = false := hm.2.2.2.2.2.trans ha
  have rawCode : start + 14 + 32 ≤ containing.length ∧ ∀ position < 32,
      containing.getD (start + 14 + position) PA06A19PrepareBankNodeBit022Raw.paddingOp =
        (PA06A19PrepareBankNodeBit022Raw.programAt (start + 14)).getD position
          PA06A19PrepareBankNodeBit022Raw.paddingOp := by
    refine ⟨by have h := code.1; omega, ?_⟩
    intro position hp
    have h := code.2 (14 + position) (by omega)
    rw [PA06A19PrepareBankNodeBit022.programAt,
      List.getD_append_right _ _ _ _ (by rw [PA06A19PrepareBankNodeBit022.prefix14_length]; omega),
      PA06A19PrepareBankNodeBit022.prefix14_length] at h
    simpa only [Nat.add_assoc, Nat.add_sub_cancel_left] using h
  have hr := PA06A19PrepareBankNodeBit022Raw.query q full containing (start + 14)
    rawCode.1 rawCode.2 candidate tool middle hmPC hmActive hm.1 (hm.2.1.trans htool)
  dsimp only [PA06A19PrepareBankNodeBit022Raw.ReturnedActive] at hr
  have hvalue : bit (decide (tool ∈ RawCandidateParents.candidateSupport q full candidate.val)) =
      rawCandidateBit (rawIncidenceROM q full) candidate.val tool.val :=
    (rawCandidateBit_eq q full candidate tool).symm
  dsimp only [nodeReadClock]
  rw [hord, natRun_add, nodeBit_prefix_run q full containing start code state hpc ha]
  refine ⟨hr.1.trans hvalue, hr.2.2.1.trans (hm.2.1.trans htool),
    hr.2.2.2.1.trans hm.2.2.1, hr.2.2.2.2.1.trans hm.2.2.2.1, ?_, hr.2.2.2.2.2.2⟩
  simpa only [Nat.add_assoc] using hr.2.2.2.2.2.1

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
