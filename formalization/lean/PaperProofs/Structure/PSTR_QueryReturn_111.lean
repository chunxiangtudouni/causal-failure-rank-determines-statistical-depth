module

public import PaperProofs.Structure.PSTR_BranchAccess_088

/-! Genuine three-instruction common-exit jump. All four reply registers
and the entire heap survive; every properclock is actually fetched/safe. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRQueryReturn

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PSTRWordSegments PSTRCountKernel PSTRCountControl

theorem actual_return {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start target : Nat)
    (slice : PSTROuterCountCode.BlockAt whole start (backBlock target))
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    let after := packingRun rom whole 3 state
    after.pc = BitVec.ofNat bits (5 * target) ∧ after.halted = false ∧ after.heap = state.heap ∧
      after.register .value = state.register .value ∧ after.register .old = state.register .old ∧
      after.register .fresh = state.register .fresh ∧ after.register .index = state.register .index := by
  rw [fetched_back rom whole start target slice.bound slice.code hwords hpcfit state hp ha]
  have data := back_payload rom target state
  exact ⟨back_pc rom target state, (executeOps_halted rom _ state).trans ha,
    data.1, data.2.2.2.2, data.2.2.1, data.2.2.2.1, data.2.1⟩

theorem prefix_heap {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start target : Nat)
    (slice : PSTROuterCountCode.BlockAt whole start (backBlock target))
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (clock : Nat) (hc : clock ≤ 3) : (packingRun rom whole clock state).heap = state.heap := by
  by_cases he : clock = 3
  · subst clock
    exact (actual_return rom whole start target slice hwords hpcfit state hp ha).2.2.1
  · have hclock : clock ≤ 2 := by omega
    have hb : start + (backLead target).length ≤ whole.length := by
      have h := slice.bound
      rw [backBlock_length] at h
      rw [backLead_length]
      omega
    have code (i : Nat) (hi : i < (backLead target).length) :
        whole[start + i]'(by omega) = (backLead target)[i] := by
      exact (slice.code i (by rw [backBlock_length]; rw [backLead_length] at hi; omega)).trans (List.getElem_append_left hi)
    rw [fetched_prefix rom whole (backLead target) start hb code (backLead_straight target)
      hwords hpcfit state hp ha clock hclock]
    interval_cases clock <;> rfl

theorem actual_safe {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (start target heapWords : Nat) (slice : PSTROuterCountCode.BlockAt whole start (backBlock target))
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (clock : Nat) (hc : clock < 3) : AtSafe rom whole heapWords (packingRun rom whole clock state) :=
  PSTRBranchAccess.back_safe rom whole start target heapWords slice hwords hpcfit state hp ha clock hc

theorem reply_iff {bits q : Nat} (rom : PhysicalROM) (target capWords : Nat)
    (answer : IndexedQuery.Reply q) (state : WordState bits) :
    ReplyCorrect q answer (replyState q capWords (executeOps rom (backBlock target) state)) ↔
      ReplyCorrect q answer (replyState q capWords state) := Iff.rfl

end PaperProofs.Structure.LaminarTree.PSTRQueryReturn
