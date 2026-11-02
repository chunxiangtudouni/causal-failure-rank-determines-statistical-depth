module

public import Structure.PSTR_WidthEmbedded_033

/-! Every intermediate state of the actual inlined width/mask calculation
preserves the physical heap. In particular, persistent packed capacity is
preserved at all clocks, not only at the final return. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRWidthPrefix

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open PSTRWidthKernel PSTRWidthEmbedded

theorem straight_prefix {bits : Nat} (rom : PhysicalROM) (whole block : List PackingOp)
    (start : Nat) (hbound : start + block.length ≤ whole.length)
    (hcode : ∀ i (hi : i < block.length), whole[start + i]'(by omega) = block[i])
    (hs : StraightProgram block) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ block.length) :
    packingRun rom whole count state = executeOps rom (block.take count) state := by
  have hl : (block.take count).length = count := List.length_take_of_le hc
  conv_lhs => rw [← hl]
  apply PSTRWordSegments.straight_segment rom whole (block.take count) start
    (by omega) ?_ ?_ hw hpcfit state hp ha
  · intro i hi
    have hi' : i < block.length := by rw [hl] at hi; omega
    simpa only [List.getElem_take] using hcode i hi'
  · intro op ho
    exact hs op (List.mem_of_mem_take ho)

theorem init_prefix {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hc : Contains whole start) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (count : Nat) (hn : count ≤ 4) :
    packingRun rom whole count state = executeOps rom (PSTRRuntimeWidth.initCode.take count) state := by
  apply straight_prefix rom whole PSTRRuntimeWidth.initCode start ?_ ?_
    init_straight hw hpcfit state hp ha count hn
  · have h := hc.bound
    rw [kernel_length] at h
    change start + 4 ≤ whole.length
    omega
  · intro i hi
    exact (hc.code i (by rw [kernel_length]; change i < 4 at hi; omega)).trans (kernel_init start i hi)

theorem test_prefix {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hc : Contains whole start) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (start + 4))) (ha : state.halted = false)
    (count : Nat) (hn : count ≤ 3) :
    packingRun rom whole count state = executeOps rom ((testAt start).take count) state := by
  apply PSTRWordSegments.segment_prefix rom whole (testLeadAt start) (.jumpIfZero .flag .address)
    (start + 4) ?_ ?_ ?_ (test_straight start) hw hpcfit state hp ha count hn
  · have h := hc.bound
    rw [kernel_length] at h
    change start + 4 + 2 + 1 ≤ whole.length
    omega
  · intro i hi
    have hh := hc.code (4 + i) (by rw [kernel_length]; rw [testLead_length] at hi; omega)
    simpa only [Nat.add_assoc] using hh.trans (kernel_test start i hi)
  · have hh := hc.code 6 (by rw [kernel_length]; decide)
    have he : (kernel start)[6]'(by rw [kernel_length]; decide) = .jumpIfZero .flag .address := rfl
    simpa only [testLead_length, Nat.add_assoc] using hh.trans he

theorem body_prefix {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hc : Contains whole start) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (start + 7))) (ha : state.halted = false)
    (count : Nat) (hn : count ≤ 5) :
    packingRun rom whole count state = executeOps rom ((bodyAt start).take count) state := by
  apply PSTRWordSegments.segment_prefix rom whole (bodyLeadAt start) (.jumpIfZero .flag .address)
    (start + 7) ?_ ?_ ?_ (body_straight start) hw hpcfit state hp ha count hn
  · have h := hc.bound
    rw [kernel_length] at h
    change start + 7 + 4 + 1 ≤ whole.length
    omega
  · intro i hi
    have hh := hc.code (7 + i) (by rw [kernel_length]; rw [bodyLead_length] at hi; omega)
    simpa only [Nat.add_assoc] using hh.trans (kernel_body start i hi)
  · have hh := hc.code 11 (by rw [kernel_length]; decide)
    have he : (kernel start)[11]'(by rw [kernel_length]; decide) = .jumpIfZero .flag .address := rfl
    simpa only [bodyLead_length, Nat.add_assoc] using hh.trans he

theorem init_heap_prefix {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (count : Nat) (hc : count ≤ 4) :
    (executeOps rom (PSTRRuntimeWidth.initCode.take count) state).heap = state.heap := by
  interval_cases count <;> rfl

theorem test_heap_prefix {bits : Nat} (rom : PhysicalROM) (start : Nat) (state : WordState bits)
    (count : Nat) (hc : count ≤ 3) :
    (executeOps rom ((testAt start).take count) state).heap = state.heap := by
  interval_cases count <;> rfl

theorem body_heap_prefix {bits : Nat} (rom : PhysicalROM) (start : Nat) (state : WordState bits)
    (count : Nat) (hc : count ≤ 5) :
    (executeOps rom ((bodyAt start).take count) state).heap = state.heap := by
  interval_cases count <;> rfl

theorem loop_prefix_heap {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hc : Contains whole start) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (q k : Nat) (state : WordState bits)
    (hs : Ready q k start state) (hroom : Fits bits (2 * (q + 1)))
    (hk : k < CapacityBits.width q) (clock : Nat) (hclock : clock ≤ 8) :
    (packingRun rom whole clock state).heap = state.heap := by
  by_cases ht : clock ≤ 3
  · rw [test_prefix rom whole start hc hw hpcfit state hs.pc hs.active clock ht]
    exact test_heap_prefix rom start state clock ht
  · have hq : Fits bits (q + 1) := by unfold Fits at hroom ⊢; omega
    have hpow := power_room q k hroom hk.le
    have hlt : 2 ^ k < q + 1 := Nat.pow_lt_of_lt_clog hk
    have hne : q + 1 - 2 ^ k ≠ 0 := by omega
    let tested := executeOps rom (testAt start) state
    have hp : tested.pc = BitVec.ofNat bits (5 * (start + 7)) := by
      rw [test_pc rom q k start state hs hq hpow, ite_eq_right hne]
    have ha : tested.halted = false := by rw [executeOps_halted, hs.active]
    have hn : clock - 3 ≤ 5 := by omega
    rw [show clock = 3 + (clock - 3) by omega, PSTRWordSegments.run_add,
      test_run rom whole start hc hw hpcfit state hs.pc hs.active,
      body_prefix rom whole start hc hw hpcfit tested hp ha (clock - 3) hn]
    exact (body_heap_prefix rom start tested _ hn).trans (test_heap rom start state)

theorem iterations_prefix_heap {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hc : Contains whole start) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (q k count : Nat) (state : WordState bits)
    (hs : Ready q k start state) (hroom : Fits bits (2 * (q + 1)))
    (hk : k + count ≤ CapacityBits.width q) (clock : Nat) (hclock : clock ≤ 8 * count) :
    (packingRun rom whole clock state).heap = state.heap := by
  induction count generalizing k state clock with
  | zero =>
    have hz : clock = 0 := by omega
    subst clock
    rfl
  | succ count ih =>
    by_cases hfirst : clock ≤ 8
    · exact loop_prefix_heap rom whole start hc hw hpcfit q k state hs hroom (by omega) clock hfirst
    · obtain ⟨hnext, hframe⟩ := loop_step rom whole start hc hw hpcfit q k state hs hroom (by omega)
      rw [show clock = 8 + (clock - 8) by omega, PSTRWordSegments.run_add]
      exact (ih (k + 1) (packingRun rom whole 8 state) hnext (by omega) (clock - 8) (by omega)).trans hframe

theorem width_prefix_heap {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hc : Contains whole start) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (q : Nat) (state : WordState bits)
    (hf : (state.register .fresh).toNat = q)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (hroom : Fits bits (2 * (q + 1))) (clock : Nat) (hclock : clock ≤ 8 * CapacityBits.width q + 7) :
    (packingRun rom whole clock state).heap = state.heap := by
  by_cases hfirst : clock ≤ 4
  · rw [init_prefix rom whole start hc hw hpcfit state hp ha clock hfirst]
    exact init_heap_prefix rom state clock hfirst
  · have hinit : Ready q 0 start (packingRun rom whole 4 state) := by
      rw [init_run rom whole start hc hw hpcfit state hp ha]
      exact init_ready rom q start state hf hp ha
    have hinitFrame : (packingRun rom whole 4 state).heap = state.heap := by
      rw [init_run rom whole start hc hw hpcfit state hp ha]
      exact init_heap rom state
    rw [show clock = 4 + (clock - 4) by omega, PSTRWordSegments.run_add]
    by_cases hloop : clock - 4 ≤ 8 * CapacityBits.width q
    · exact (iterations_prefix_heap rom whole start hc hw hpcfit q 0 (CapacityBits.width q)
        (packingRun rom whole 4 state) hinit hroom (by omega) (clock - 4) hloop).trans hinitFrame
    · let count := clock - 4 - 8 * CapacityBits.width q
      have hn : count ≤ 3 := by dsimp only [count]; omega
      have he : clock - 4 = 8 * CapacityBits.width q + count := by dsimp only [count]; omega
      have hlooped := iterations rom whole start hc hw hpcfit q 0 (CapacityBits.width q)
        (packingRun rom whole 4 state) hinit hroom (by omega)
      simp only [Nat.zero_add] at hlooped
      rw [he, PSTRWordSegments.run_add,
        test_prefix rom whole start hc hw hpcfit _ hlooped.1.pc hlooped.1.active count hn]
      exact (test_heap_prefix rom start _ count hn).trans (hlooped.2.trans hinitFrame)

theorem width_mask_prefix_heap {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hc : Contains whole start) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (hbound : start + 13 ≤ whole.length)
    (hmask : whole[start + 12]'(by omega) = maskOp)
    (q : Nat) (state : WordState bits) (hf : (state.register .fresh).toNat = q)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (hroom : Fits bits (2 * (q + 1))) (clock : Nat) (hclock : clock ≤ 8 * CapacityBits.width q + 8) :
    (packingRun rom whole clock state).heap = state.heap := by
  by_cases hbefore : clock ≤ 8 * CapacityBits.width q + 7
  · exact width_prefix_heap rom whole start hc hw hpcfit q state hf hp ha hroom clock hbefore
  · have he : clock = 8 * CapacityBits.width q + 8 := by omega
    subst clock
    exact (actual_width_mask rom whole start hc hw hpcfit hbound hmask q state hf hp ha hroom).2.2.2.2

end PaperProofs.Structure.LaminarTree.PSTRWidthPrefix
