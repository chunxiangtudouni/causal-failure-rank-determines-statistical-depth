module

public import PaperProofs.Structure.PSTR_HD_HeadsDecisionRun_075

/-! A selected head is appended by the actual10ops, then the real3op jump
goes to the SAME declaration block. The list extension is proved over the
actual heap; it is not a free runtime list/cardinality operation. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments

theorem append_scan_entry {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (origin endpoint q rank stage : Nat) (entries : List Nat)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (he : Fits bits (endpoint + 10 + entries.length + 1))
    (recorded : RecordedHeads endpoint q rank entries state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 67))) (ha : state.halted = false)
    (haddr : state.register .address = BitVec.ofNat bits endpoint)
    (hold : state.register .old = BitVec.ofNat bits stage) :
    let after := packingRun rom whole 13 state
    after.pc = BitVec.ofNat bits (5 * (origin + 56)) ∧ after.halted = false ∧
    after.heap = (executeOps rom headsAppend state).heap ∧
    RecordedHeads endpoint q rank (entries ++ [stage]) after.heap ∧
    after.register .address = BitVec.ofNat bits endpoint := by
  dsimp only
  let appended := executeOps rom headsAppend state
  have append_result := execute_headsAppend rom endpoint (endpoint + 10 + entries.length) stage entries.length
    state haddr hold recorded.count recorded.cursor
  have append_pc : appended.pc = BitVec.ofNat bits (5 * (origin + 77)) := by
    change (executeOps rom headsAppend state).pc = _
    rw [executeOps_pc rom headsAppend state headsAppend_straight, hp, BitVec.ofNat_add_ofNat]
    congr 1
  have append_halt : appended.halted = false := (executeOps_halted rom headsAppend state).trans ha
  have run10 : packingRun rom whole 10 state = appended :=
    containing_headsAppend rom whole (origin + 67) (by have h := tailAt_length origin; rw [headsAppend_length]; omega)
      (headsAppend_tail_code whole origin hbound hcode) hwords hpcfit state hp ha
  have back_code := tail_slice whole (jumpBack (origin + 56)) origin 77 hbound hcode
    (by change 77 + 3 ≤ 111; decide) rfl
  have run3 := containing_jumpBack rom whole (origin + 77) (origin + 56)
    (by have h := tailAt_length origin; rw [jumpBack_length]; omega) back_code hwords hpcfit appended append_pc append_halt
  have back := execute_jumpBack rom (origin + 56) appended
  rw [show 13 = 10 + 3 from rfl, run_add, run10, run3]
  refine ⟨back.1, back.2.1.trans append_halt, back.2.2.1, ?_, back.2.2.2.2.2.2.2.1.trans append_result.2.1⟩
  rw [back.2.2.1]
  exact append_recorded rom endpoint q rank stage entries state he recorded haddr hold

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
