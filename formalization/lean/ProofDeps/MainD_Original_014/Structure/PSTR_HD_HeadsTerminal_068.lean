module

public import Structure.PSTR_HD_HeadsInitialRun_067

/-! Actual terminal stage control: real terminal branch, actual7op count
write/output-base return, and (only when at the real end) fetched HALT. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments

theorem terminal_scan_exit {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (origin endpoint N count : Nat)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * (origin + 40))) (ha : state.halted = false)
    (haddr : state.register .address = BitVec.ofNat bits endpoint)
    (hindex : state.register .index = BitVec.ofNat bits N) (hold : state.register .old = BitVec.ofNat bits N)
    (hk : state.heap (BitVec.ofNat bits (endpoint + 1)) = BitVec.ofNat bits count) (hN : Fits bits N) :
    let after := packingRun rom whole 10 state
    after.pc = BitVec.ofNat bits (5 * (origin + 111)) ∧ after.halted = false ∧
    after.heap = Function.update state.heap (BitVec.ofNat bits (endpoint + 9)) (BitVec.ofNat bits count) ∧
    after.register .index = BitVec.ofNat bits (outputBase endpoint) := by
  dsimp only
  let tested : WordState bits := {executeOps rom (terminalLead origin) state with pc := BitVec.ofNat bits (5 * (origin + 104))}
  have test_result := execute_terminalLead rom origin N N state hN hN hindex hold
  have run3 : packingRun rom whole 3 state = tested :=
    fetched_conditional rom whole (terminalLead origin) (origin + 40) (origin + 104) 0 .flag
      (by have h := tailAt_length origin; rw [terminalLead_length]; omega)
      (terminalLead_tail_code whole origin hbound hcode)
      (hcode 42 (by change 42 < 111; decide)) (terminalLead_straight origin) hwords hpcfit state hp ha
      (by simpa only [Nat.sub_self] using test_result.1) test_result.2.1 (by unfold Fits; positivity)
  have tested_pc : tested.pc = BitVec.ofNat bits (5 * (origin + 104)) := rfl
  have tested_halt : tested.halted = false := ha
  have tested_addr : tested.register .address = BitVec.ofNat bits endpoint := haddr
  have run7 : packingRun rom whole 7 tested = executeOps rom headsFinish tested :=
    containing_headsFinish rom whole (origin + 104) (by have h := tailAt_length origin; rw [headsFinish_length]; omega)
      (headsFinish_tail_code whole origin hbound hcode) hwords hpcfit tested tested_pc tested_halt
  have finish_pc : (executeOps rom headsFinish tested).pc = BitVec.ofNat bits (5 * (origin + 111)) := by
    rw [executeOps_pc rom headsFinish tested headsFinish_straight, tested_pc, BitVec.ofNat_add_ofNat]
    congr 1
  have finish_result := execute_headsFinish rom endpoint count tested tested_addr hk
  rw [show 10 = 3 + 7 from rfl, run_add, run3, run7]
  refine ⟨finish_pc, ?_, finish_result.1, finish_result.2.1⟩
  rw [executeOps_halted]
  exact tested_halt

theorem terminal_scan_halt {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (origin endpoint N count : Nat)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hend : whole.length = origin + 111)
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * (origin + 40))) (ha : state.halted = false)
    (haddr : state.register .address = BitVec.ofNat bits endpoint)
    (hindex : state.register .index = BitVec.ofNat bits N) (hold : state.register .old = BitVec.ofNat bits N)
    (hk : state.heap (BitVec.ofNat bits (endpoint + 1)) = BitVec.ofNat bits count) (hN : Fits bits N) :
    packingRun rom whole 11 state = {packingRun rom whole 10 state with halted := true} := by
  have h := terminal_scan_exit rom whole origin endpoint N count hbound hcode hwords hpcfit state hp ha haddr hindex hold hk hN
  exact PSTRCountKernel.halt_at_exit rom whole 10 state hwords hpcfit h.2.1 (by rw [hend]; exact h.1)

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
