module

public import Structure.PSTR_HD_HeadsReturn_066

/-! The first stage0 return actually writes fresh control/output cells and
jumps to the common scan label, in the SAME instruction array and heap. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments

theorem initial_scan_entry {bits q : Nat} (full : List (Finset (Fin q)))
    (origin endpoint rank : Nat) (whole : List PackingOp)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hb : 8 ≤ bits) (he : Fits bits (endpoint + 8))
    (hr : Fits bits rank) (hq : Fits bits (q + 2))
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 80))) (ha : state.halted = false)
    (haddr : state.register .address = BitVec.ofNat bits endpoint)
    (hvalue : state.register .value = BitVec.ofNat bits rank) :
    let after := packingRun (callInput q full .query) whole 24 state
    after.pc = BitVec.ofNat bits (5 * (origin + 40)) ∧ after.halted = false ∧
    after.heap = initHeap endpoint q rank state.heap ∧ RecordedHeads endpoint q rank [] after.heap ∧
    after.register .value = state.register .value ∧ after.register .old = state.register .old ∧
    after.register .fresh = state.register .fresh ∧ after.register .index = state.register .index ∧
    after.register .address = BitVec.ofNat bits endpoint := by
  dsimp only
  let rom := callInput q full .query
  let initialized := executeOps rom headsInit state
  have init_result := execute_headsInit rom endpoint q rank state hb
    ((show endpoint + 3 ≤ endpoint + 8 by omega).trans_lt he) hr hq haddr hvalue rfl
  have init_pc : initialized.pc = BitVec.ofNat bits (5 * (origin + 101)) := by
    change (executeOps rom headsInit state).pc = _
    rw [executeOps_pc rom headsInit state headsInit_straight, hp, BitVec.ofNat_add_ofNat]
    congr 1
  have init_halt : initialized.halted = false := init_result.2.2.2.2.2.2.trans ha
  have run21 : packingRun rom whole 21 state = initialized :=
    containing_headsInit rom whole (origin + 80) (by have h := tailAt_length origin; rw [headsInit_length]; omega)
      (headsInit_tail_code whole origin hbound hcode) hwords hpcfit state hp ha
  have back_code := tail_slice whole (jumpBack (origin + 40)) origin 101 hbound hcode
    (by change 101 + 3 ≤ 111; decide) rfl
  have run3 := containing_jumpBack rom whole (origin + 101) (origin + 40)
    (by have h := tailAt_length origin; rw [jumpBack_length]; omega) back_code
    hwords hpcfit initialized init_pc init_halt
  have back_result := execute_jumpBack rom (origin + 40) initialized
  rw [show 24 = 21 + 3 from rfl, run_add, run21, run3]
  refine ⟨back_result.1, back_result.2.1.trans init_halt, back_result.2.2.1.trans init_result.1,
    ?_, back_result.2.2.2.1.trans init_result.2.2.1,
    back_result.2.2.2.2.1.trans init_result.2.2.2.1,
    back_result.2.2.2.2.2.1.trans init_result.2.2.2.2.1,
    back_result.2.2.2.2.2.2.1.trans init_result.2.2.2.2.2.1,
    back_result.2.2.2.2.2.2.2.1.trans init_result.2.1⟩
  rw [back_result.2.2.1, init_result.1]
  exact initHeap_recorded endpoint q rank state.heap he

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
