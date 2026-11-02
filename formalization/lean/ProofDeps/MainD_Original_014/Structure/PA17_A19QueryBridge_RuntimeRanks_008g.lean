module

public import Structure.PA17_A19QueryBridge_RuntimeRanks_008f

/-! Whole real-loop prefix safety and complete physical heap frames.
The certificate is derived from scalar layout, actual flag representations
and actual fetched code. No all-prefix safety/trace oracle is an input. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeRanks008

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

theorem loop_point {bits origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing)
    (rom : PhysicalROM) (q header remaining heapWords : Nat) (good bad : Nat → Bool)
    (heap : BitVec bits → BitVec bits) (state : WordState bits)
    (hroom : Fits bits (header + 16 + 2 * (q + 2))) (halloc : header + 16 + 2 * (q + 2) ≤ heapWords)
    (ready : Ready origin q header (remaining + 1) good bad heap state)
    (count : Nat) (hc : count < 15) : Point rom containing heapWords header (packingRun rom containing count state) := by
  by_cases htest : count < 2
  · exact test_point em rom heapWords header state ready.pc ready.active count htest
  · have hqf : Fits bits (q + 2) := (show q + 2 ≤ header + 16 + 2 * (q + 2) by omega).trans_lt hroom
    let tested := executeOps rom (testBlock origin) state
    have ht := execute_test rom origin (remaining + 1) state ready.pc ready.index (ready.bound.trans_lt hqf)
    have hpc : tested.pc = BitVec.ofNat bits (5 * (origin + 10)) := by
      simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] using ht.1
    have hreg (register : Register) (hne : register ≠ .old) : tested.register register = state.register register :=
      test_register rom origin state register hne
    rw [show count = 2 + (count - 2) by omega, run_add, fetched_test em rom state ready.pc ready.active]
    exact body_point em rom q header remaining heapWords tested hroom halloc
      (by have hh := ready.bound; omega) ((hreg .address (by decide)).trans ready.address)
      ((hreg .index (by decide)).trans ready.index) ((hreg .total (by decide)).trans ready.total)
      hpc (by rw [executeOps_halted, ready.active]) (count - 2) (by omega)

theorem actual_prefix_point {bits origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing)
    (rom : PhysicalROM) (q header heapWords : Nat) (good bad : Nat → Bool) (state : WordState bits)
    (hroom : Fits bits (header + 16 + 2 * (q + 2))) (halloc : header + 16 + 2 * (q + 2) ≤ heapWords)
    (hinput : 1 < rom.input.length) (hq : (rom.words .input).getD 1 0 = q)
    (hgood : ∀ budget < q + 2, state.heap (BitVec.ofNat bits (header + 16 + budget)) = BitVec.ofNat bits (bit (good budget)))
    (hbad : ∀ budget < q + 2, state.heap (BitVec.ofNat bits (header + 16 + budget + (q + 2))) = BitVec.ofNat bits (bit (bad budget)))
    (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (clock : Nat) (hc : clock < steps q) :
    Point rom containing heapWords header (packingRun rom containing clock state) := by
  have h1 : Fits bits 1 := (show 1 ≤ header + 16 + 2 * (q + 2) by omega).trans_lt hroom
  have hqf : Fits bits (q + 2) := (show q + 2 ≤ header + 16 + 2 * (q + 2) by omega).trans_lt hroom
  by_cases hsetup : clock < 8
  · exact setup_point em rom heapWords header state h1 hinput hp ha clock hsetup
  · let a := packingRun rom containing 8 state
    have hinit := ready_setup em rom q header good bad state h1 hq hh hp ha
    let offset := clock - 8
    have he : clock = 8 + offset := by dsimp only [offset]; omega
    rw [he, run_add]
    change Point rom containing heapWords header (packingRun rom containing offset a)
    by_cases hloop : offset < 15 * (q + 2)
    · let iterations := offset / 15
      let withinPhase := offset % 15
      let remaining := q + 2 - iterations
      have hi : iterations < q + 2 := by dsimp only [iterations]; omega
      have hlocal : withinPhase < 15 := by dsimp only [withinPhase]; omega
      have hremain : 0 < remaining := by dsimp only [remaining]; omega
      have hsum : remaining + iterations = q + 2 := by dsimp only [remaining]; omega
      have hready0 : Ready origin q header (remaining + iterations) good bad state.heap a := by
        rw [hsum]
        exact hinit
      have hready := fetched_iterations em rom q header remaining iterations good bad state.heap a
        h1 hqf hgood hbad hready0
      have hready' : Ready origin q header (remaining - 1 + 1) good bad state.heap
          (packingRun rom containing (15 * iterations) a) := by
        rw [Nat.sub_add_cancel (show 1 ≤ remaining by omega)]
        exact hready
      have hparts : offset = 15 * iterations + withinPhase := by dsimp only [iterations, withinPhase]; omega
      rw [hparts, run_add]
      exact loop_point em rom q header (remaining - 1) heapWords good bad state.heap
        (packingRun rom containing (15 * iterations) a) hroom halloc hready' withinPhase hlocal
    · let tail := offset - 15 * (q + 2)
      let looped := packingRun rom containing (15 * (q + 2)) a
      have hend : Ready origin q header 0 good bad state.heap looped := by
        simpa only [Nat.zero_add] using fetched_iterations em rom q header 0 (q + 2) good bad state.heap a
          h1 hqf hgood hbad (by simpa only [Nat.zero_add] using hinit)
      have htail : tail < 30 := by dsimp only [tail, offset] at *; unfold steps at hc; omega
      have hparts : offset = 15 * (q + 2) + tail := by dsimp only [tail]; omega
      rw [hparts, run_add]
      change Point rom containing heapWords header (packingRun rom containing tail looped)
      by_cases htest : tail < 2
      · exact test_point em rom heapWords header looped hend.pc hend.active tail htest
      · let tested := executeOps rom (testBlock origin) looped
        have ht := execute_test rom origin 0 looped hend.pc hend.index ((show 0 ≤ 1 by decide).trans_lt h1)
        have hpc : tested.pc = BitVec.ofNat bits (5 * (origin + 23)) := by simpa only [ite_true] using ht.1
        have hheader : tested.register .address = BitVec.ofNat bits header :=
          (test_register rom origin looped .address (by decide)).trans hend.address
        rw [show tail = 2 + (tail - 2) by omega, run_add, fetched_test em rom looped hend.pc hend.active]
        exact footer_point em rom header heapWords tested hheader (by omega) hpc
          (by rw [executeOps_halted, hend.active]) (tail - 2) (by omega)

theorem actual_prefix_frame {bits origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing)
    (rom : PhysicalROM) (q header heapWords : Nat) (good bad : Nat → Bool) (state : WordState bits)
    (hroom : Fits bits (header + 16 + 2 * (q + 2))) (halloc : header + 16 + 2 * (q + 2) ≤ heapWords)
    (hinput : 1 < rom.input.length) (hq : (rom.words .input).getD 1 0 = q)
    (hgood : ∀ budget < q + 2, state.heap (BitVec.ofNat bits (header + 16 + budget)) = BitVec.ofNat bits (bit (good budget)))
    (hbad : ∀ budget < q + 2, state.heap (BitVec.ofNat bits (header + 16 + budget + (q + 2))) = BitVec.ofNat bits (bit (bad budget)))
    (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (clock : Nat) (hc : clock ≤ steps q) (address : BitVec bits) (hprotect : Protected header address) :
    (packingRun rom containing clock state).heap address = state.heap address := by
  induction clock with
  | zero => rfl
  | succ clock ih =>
    have point := actual_prefix_point em rom q header heapWords good bad state hroom halloc hinput hq hgood hbad hh hp ha
      clock (by omega)
    rcases point with ⟨hactive, index, hi, hpc, _, _, hframe⟩
    rw [packingRun_succ, packingStep_of_index rom containing _ index hi em.words hpc hactive]
    exact (hframe address hprotect).trans (ih (by omega))

theorem actual_leading_frame {bits origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing)
    (rom : PhysicalROM) (q header heapWords : Nat) (good bad : Nat → Bool) (state : WordState bits)
    (hroom : Fits bits (header + 16 + 2 * (q + 2))) (halloc : header + 16 + 2 * (q + 2) ≤ heapWords)
    (hinput : 1 < rom.input.length) (hq : (rom.words .input).getD 1 0 = q)
    (hgood : ∀ budget < q + 2, state.heap (BitVec.ofNat bits (header + 16 + budget)) = BitVec.ofNat bits (bit (good budget)))
    (hbad : ∀ budget < q + 2, state.heap (BitVec.ofNat bits (header + 16 + budget + (q + 2))) = BitVec.ofNat bits (bit (bad budget)))
    (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (clock : Nat) (hc : clock ≤ steps q) (physical : Nat) (hphysical : physical < header + 4) :
    (packingRun rom containing clock state).heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
  have hne (offset : Nat) (ho : 4 ≤ offset) (ho' : offset ≤ 7) :
      BitVec.ofNat bits physical ≠ BitVec.ofNat bits (header + offset) := by
    apply (ofNat_injective_of_fit _ _
      ((show physical ≤ header + 16 + 2 * (q + 2) by omega).trans_lt hroom)
      ((show header + offset ≤ header + 16 + 2 * (q + 2) by omega).trans_lt hroom)).not.mpr
    omega
  exact actual_prefix_frame em rom q header heapWords good bad state hroom halloc hinput hq hgood hbad hh hp ha
    clock hc _ ⟨hne 4 (by decide) (by decide), hne 5 (by decide) (by decide),
      hne 6 (by decide) (by decide), hne 7 (by decide) (by decide)⟩

theorem exit_pc_toNat {bits origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing)
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * (origin + 51))) :
    state.pc.toNat = 5 * (origin + 51) := by
  rw [hp, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hb := em.bound
  rw [programAt_length] at hb
  exact (Nat.mul_le_mul_left 5 hb).trans_lt em.pcfit

theorem actual_prefix_decoded {bits origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing)
    (rom : PhysicalROM) (q header heapWords : Nat) (good bad : Nat → Bool) (state : WordState bits)
    (hroom : Fits bits (header + 16 + 2 * (q + 2))) (halloc : header + 16 + 2 * (q + 2) ≤ heapWords)
    (hinput : 1 < rom.input.length) (hq : (rom.words .input).getD 1 0 = q)
    (hgood : ∀ budget < q + 2, state.heap (BitVec.ofNat bits (header + 16 + budget)) = BitVec.ofNat bits (bit (good budget)))
    (hbad : ∀ budget < q + 2, state.heap (BitVec.ofNat bits (header + 16 + budget + (q + 2))) = BitVec.ofNat bits (bit (bad budget)))
    (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (clock : Nat) (hc : clock < steps q) :
    let before := packingRun rom containing clock state
    before.halted = false ∧ Fits bits (before.pc.toNat + 4) ∧
      before.pc.toNat + 4 < (packingCode containing).length ∧
      ∃ op, PackingOp.decode (physicalFetch bits (packingCode containing) before.pc.toNat) = some op ∧
        packingAccessFits rom heapWords before op := by
  have point := actual_prefix_point em rom q header heapWords good bad state hroom halloc hinput hq hgood hbad hh hp ha clock hc
  rcases point with ⟨hactive, index, hi, hpc, hfetch, haccess, _⟩
  have hsmall : (packingRun rom containing clock state).pc.toNat + 4 < 5 * containing.length := by
    rw [hpc]
    omega
  refine ⟨hactive, hsmall.trans em.pcfit, ?_, containing[index], ?_, haccess⟩
  · rw [packingCode_length]
    omega
  · rw [hfetch, decode_encode]

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeRanks008

