module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009d

/-! All genuine runtime-loop prefixes, including both jump instructions.
Access/frame/fetch safety is derived here from the actual entry data. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

theorem clear_loop_point {bits origin : Nat} {containing : List PackingOp} (em : ClearEmbedded bits origin containing)
    (rom : PhysicalROM) (header base done remaining total heapWords : Nat)
    (heap : BitVec bits → BitVec bits) (state : WordState bits)
    (hr : Fits bits (remaining + 1)) (hd : done < total) (halloc : base + total ≤ heapWords)
    (ready : ClearReady origin header base done (remaining + 1) heap state)
    (count : Nat) (hc : count < 7) :
    ClearPoint rom containing heapWords base total (packingRun rom containing count state) := by
  by_cases htest : count < 2
  · exact clear_test_point em rom heapWords base total state ready.pc ready.active count htest
  · let tested := executeOps rom (clearTest origin) state
    have ht := clear_test_result rom origin (remaining + 1) state ready.pc ready.total hr
    have hpc : tested.pc = BitVec.ofNat bits (5 * (origin + 16)) := by
      simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] using ht.1
    rw [show count = 2 + (count - 2) by omega, run_add, fetched_clear_test em rom state ready.pc ready.active]
    exact clear_body_point em rom heapWords base done total tested
      ((clear_test_register rom origin state .index (by decide)).trans ready.index) hd halloc hpc
      (by rw [executeOps_halted, ready.active]) (count - 2) (by omega)

theorem actual_clear_prefix_point {bits origin : Nat} {containing : List PackingOp}
    (em : ClearEmbedded bits origin containing) (rom : PhysicalROM) (q size header heapWords : Nat) (state : WordState bits)
    (hroom : Fits bits (childBase header q + size + 1)) (halloc : childBase header q + size + 1 ≤ heapWords)
    (hinput : 1 < rom.input.length) (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hq : (rom.words .input).getD 1 0 = q) (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (clock : Nat) (hc : clock < clearSteps size) :
    ClearPoint rom containing heapWords (childBase header q) (size + 1) (packingRun rom containing clock state) := by
  have h1 : Fits bits 1 := (show 1 ≤ childBase header q + size + 1 by omega).trans_lt hroom
  have hsf : Fits bits (size + 1) := (show size + 1 ≤ childBase header q + size + 1 by omega).trans_lt hroom
  by_cases hsetup : clock < 14
  · exact clear_setup_point em rom heapWords (childBase header q) (size + 1) state h1 hinput (by omega) hp ha clock hsetup
  · let a := packingRun rom containing 14 state
    have hinit := clear_ready_setup em rom q size header state h1 hsize hq hh hp ha
    let offset := clock - 14
    have he : clock = 14 + offset := by dsimp only [offset]; omega
    rw [he, run_add]
    change ClearPoint rom containing heapWords (childBase header q) (size + 1) (packingRun rom containing offset a)
    by_cases hloop : offset < 7 * (size + 1)
    · let iterations := offset / 7
      let withinPhase := offset % 7
      let remaining := size + 1 - iterations
      have hi : iterations < size + 1 := by dsimp only [iterations]; omega
      have hlocal : withinPhase < 7 := by dsimp only [withinPhase]; omega
      have hremain : 0 < remaining := by dsimp only [remaining]; omega
      have hsum : remaining + iterations = size + 1 := by dsimp only [remaining]; omega
      have hready := clear_iterations em rom header (childBase header q) 0 remaining iterations state.heap a h1
        (by rw [hsum]; exact hsf) (by rw [hsum]; exact hinit)
      have hready' : ClearReady origin header (childBase header q) iterations (remaining - 1 + 1) state.heap
          (packingRun rom containing (7 * iterations) a) := by
        simpa only [Nat.zero_add, Nat.sub_add_cancel (show 1 ≤ remaining by omega)] using hready
      have hparts : offset = 7 * iterations + withinPhase := by dsimp only [iterations, withinPhase]; omega
      rw [hparts, run_add]
      exact clear_loop_point em rom header (childBase header q) iterations (remaining - 1) (size + 1) heapWords state.heap
        (packingRun rom containing (7 * iterations) a)
        ((show remaining - 1 + 1 ≤ size + 1 by dsimp only [remaining]; omega).trans_lt hsf) hi (by omega)
        hready' withinPhase hlocal
    · let tail := offset - 7 * (size + 1)
      let looped := packingRun rom containing (7 * (size + 1)) a
      have hend : ClearReady origin header (childBase header q) (size + 1) 0 state.heap looped := by
        simpa only [Nat.zero_add] using clear_iterations em rom header (childBase header q) 0 0 (size + 1) state.heap a h1
          (by simpa only [Nat.zero_add] using hsf) (by simpa only [Nat.zero_add] using hinit)
      have htail : tail < 2 := by dsimp only [tail, offset] at *; unfold clearSteps at hc; omega
      have hparts : offset = 7 * (size + 1) + tail := by dsimp only [tail]; omega
      rw [hparts, run_add]
      exact clear_test_point em rom heapWords (childBase header q) (size + 1) looped hend.pc hend.active tail htail

theorem actual_clear_prefix_frame {bits origin : Nat} {containing : List PackingOp}
    (em : ClearEmbedded bits origin containing) (rom : PhysicalROM) (q size header heapWords : Nat) (state : WordState bits)
    (hroom : Fits bits (childBase header q + size + 1)) (halloc : childBase header q + size + 1 ≤ heapWords)
    (hinput : 1 < rom.input.length) (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hq : (rom.words .input).getD 1 0 = q) (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (clock : Nat) (hc : clock ≤ clearSteps size) (address : BitVec bits)
    (hprotect : ClearProtected (childBase header q) (size + 1) address) :
    (packingRun rom containing clock state).heap address = state.heap address := by
  induction clock with
  | zero => rfl
  | succ clock ih =>
    have point := actual_clear_prefix_point em rom q size header heapWords state hroom halloc hinput hsize hq hh hp ha clock (by omega)
    rcases point with ⟨hactive, index, hi, hpc, _, _, hframe⟩
    rw [packingRun_succ, packingStep_of_index rom containing _ index hi em.words hpc hactive]
    exact (hframe address hprotect).trans (ih (by omega))

theorem actual_clear_leading_frame {bits origin : Nat} {containing : List PackingOp}
    (em : ClearEmbedded bits origin containing) (rom : PhysicalROM) (q size header heapWords : Nat) (state : WordState bits)
    (hroom : Fits bits (childBase header q + size + 1)) (halloc : childBase header q + size + 1 ≤ heapWords)
    (hinput : 1 < rom.input.length) (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hq : (rom.words .input).getD 1 0 = q) (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (clock : Nat) (hc : clock ≤ clearSteps size) (physical : Nat) (hphysical : physical < childBase header q) :
    (packingRun rom containing clock state).heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
  apply actual_clear_prefix_frame em rom q size header heapWords state hroom halloc hinput hsize hq hh hp ha clock hc
  intro i hi
  apply (ofNat_injective_of_fit _ _
    ((show physical ≤ childBase header q + size + 1 by omega).trans_lt hroom)
    ((show childBase header q + i ≤ childBase header q + size + 1 by omega).trans_lt hroom)).not.mpr
  omega

theorem actual_clear_prefix_decoded {bits origin : Nat} {containing : List PackingOp}
    (em : ClearEmbedded bits origin containing) (rom : PhysicalROM) (q size header heapWords : Nat) (state : WordState bits)
    (hroom : Fits bits (childBase header q + size + 1)) (halloc : childBase header q + size + 1 ≤ heapWords)
    (hinput : 1 < rom.input.length) (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hq : (rom.words .input).getD 1 0 = q) (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (clock : Nat) (hc : clock < clearSteps size) :
    let before := packingRun rom containing clock state
    before.halted = false ∧ Fits bits (before.pc.toNat + 4) ∧
      before.pc.toNat + 4 < (packingCode containing).length ∧
      ∃ op, PackingOp.decode (physicalFetch bits (packingCode containing) before.pc.toNat) = some op ∧
        packingAccessFits rom heapWords before op := by
  have point := actual_clear_prefix_point em rom q size header heapWords state hroom halloc hinput hsize hq hh hp ha clock hc
  rcases point with ⟨hactive, index, hi, hpc, hfetch, haccess, _⟩
  have hsmall : (packingRun rom containing clock state).pc.toNat + 4 < 5 * containing.length := by rw [hpc]; omega
  refine ⟨hactive, hsmall.trans em.pcfit, ?_, containing[index], ?_, haccess⟩
  · rw [packingCode_length]
    omega
  · rw [hfetch, decode_encode]

theorem clear_exit_pc_toNat {bits origin : Nat} {containing : List PackingOp}
    (em : ClearEmbedded bits origin containing) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 21))) : state.pc.toNat = 5 * (origin + 21) := by
  rw [hp, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hb := em.bound
  rw [clearProgramAt_length] at hb
  exact (Nat.mul_le_mul_left 5 hb).trans_lt em.pcfit

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
