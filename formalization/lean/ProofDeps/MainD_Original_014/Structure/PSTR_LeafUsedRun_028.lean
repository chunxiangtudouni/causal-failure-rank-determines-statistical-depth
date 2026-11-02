module

public import Structure.PSTR_LeafUsed_027

/-! Actual fetched Word executions of the cached-label used-bit reader.
Both zero and positive labels have real HALT. In the positive branch, N/q
come from ROM and t/bits from the physical header, then the real packed
scalar read returns the original decoded used word. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRLeafUsedRun

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PSTRLeafUsed

theorem body_run {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (hb : 8 ≤ bits) (hp : state.pc = BitVec.ofNat bits 15) (ha : state.halted = false) :
    packingRun rom program 33 state = executeOps rom body state := by
  have hcode (i : Nat) (hi : i < body.length) :
      program[3 + i]'(by rw [program_length]; rw [body_length] at hi; omega) = body[i] := by
    change ((lead ++ [branch]) ++ body)[3 + i]'(by
      change 3 + i < 36
      have hh : i < 33 := hi
      omega) = body[i]
    rw [List.getElem_append_right (by change 3 ≤ 3 + i; omega)]
    simp only [show (lead ++ [branch]).length = 3 from rfl, Nat.add_sub_cancel_left]
  simpa only [body_length] using PSTRWordSegments.straight_segment rom program body 3 (by decide)
    hcode body_straight (code_fit hb) (pc_fit hb) state hp ha

theorem body_halt {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (hb : 8 ≤ bits) (hp : state.pc = BitVec.ofNat bits 15) (ha : state.halted = false) :
    packingRun rom program 34 state = { executeOps rom body state with halted := true } := by
  rw [show 34 = 33 + 1 from rfl, packingRun_succ, body_run rom state hb hp ha]
  apply packingStep_halt rom program _ (code_fit hb)
  · rw [executeOps_pc rom body state body_straight, hp, body_length,
      BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    change 180 % 2 ^ bits = 180
    exact Nat.mod_eq_of_lt (pc_fit hb)
  · rw [executeOps_halted, ha]

theorem body_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom body state).heap = state.heap := rfl

theorem actual_none {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (hb : 8 ≤ bits) (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false)
    (hz : (state.heap (state.register .address)).toNat = 0) :
    let after := packingRun rom program 4 state
    after.halted = true ∧ after.heap = state.heap ∧ after.register .value = BitVec.ofNat bits 0 := by
  have hv : state.heap (state.register .address) = BitVec.ofNat bits 0 := by
    have he := congrArg (BitVec.ofNat bits) hz
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using he
  have hpc : (executeOps rom (lead ++ [branch]) state).pc.toNat = 5 * program.length := by
    rw [prefix_pc rom state hp, ite_eq_left hz, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (pc_fit hb)
  dsimp only
  rw [show 4 = 3 + 1 from rfl, packingRun_succ, prefix_run rom state hb hp ha,
    packingStep_halt rom program _ (code_fit hb) hpc (by rw [executeOps_halted, ha])]
  exact ⟨rfl, prefix_heap rom state, (prefix_value rom state).trans hv⟩

theorem body_value {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (N q t tool capWords : Nat) (hb : 8 ≤ bits) (hpositive : 0 < q)
    (hw : CapacityBits.width q ≤ bits)
    (hN : (rom.words .input).getD 0 0 = N) (hq : (rom.words .input).getD 1 0 = q)
    (ht : (state.heap (BitVec.ofNat bits 0)).toNat = t)
    (hbits : (state.heap (BitVec.ofNat bits 3)).toNat = bits)
    (hlabel : (state.register .value).toNat = tool + 1)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hmask : state.register .flag = lowMask bits (CapacityBits.width q))
    (hN1 : Fits bits (N + 1)) (hq2 : Fits bits (q + 2))
    (ht1 : Fits bits (t + 1)) (hprod : Fits bits ((N + 1) * (q + 2)))
    (haddress : Fits bits (tableWords N q t + tool))
    (hcap : tableWords N q t + tool < capWords)
    (hs : Fits bits ((tableWords N q t + tool) * CapacityBits.width q))
    (hn : Fits bits (4 + (tableWords N q t + tool) * CapacityBits.width q / bits + 1)) :
    ((executeOps rom body state).register .value).toNat =
      logicalHeap q capWords state.heap (tableWords N q t + tool) := by
  have haddr : ((executeOps rom setup state).register .address).toNat = tableWords N q t + tool := by
    rw [setup_address rom state N q t tool hb hN hq ht hlabel hN1 hq2 ht1 hprod,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddress]
  rw [body, executeOps_append]
  have hresult := PSTRRuntimePackedRead.execute_capacity rom (executeOps rom setup state)
    hpositive (by omega) hw (by rw [setup_width]; exact hwidth) (by rw [setup_mask]; exact hmask)
    (by rw [setup_heap]; exact hbits) capWords (by rw [haddr]; exact hcap)
    (by rw [haddr]; exact hs) (by rw [haddr]; exact hn)
  simpa only [setup_heap, haddr] using hresult

theorem actual_some {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (N q t tool capWords : Nat) (hb : 8 ≤ bits) (hpositive : 0 < q)
    (hw : CapacityBits.width q ≤ bits)
    (hN : (rom.words .input).getD 0 0 = N) (hq : (rom.words .input).getD 1 0 = q)
    (ht : (state.heap (BitVec.ofNat bits 0)).toNat = t)
    (hbits : (state.heap (BitVec.ofNat bits 3)).toNat = bits)
    (hlabel : (state.heap (state.register .address)).toNat = tool + 1)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hmask : state.register .flag = lowMask bits (CapacityBits.width q))
    (hN1 : Fits bits (N + 1)) (hq2 : Fits bits (q + 2))
    (ht1 : Fits bits (t + 1)) (hprod : Fits bits ((N + 1) * (q + 2)))
    (haddress : Fits bits (tableWords N q t + tool))
    (hcap : tableWords N q t + tool < capWords)
    (hs : Fits bits ((tableWords N q t + tool) * CapacityBits.width q))
    (hn : Fits bits (4 + (tableWords N q t + tool) * CapacityBits.width q / bits + 1))
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    let after := packingRun rom program 37 state
    after.halted = true ∧ after.heap = state.heap ∧ (after.register .value).toNat =
      logicalHeap q capWords state.heap (tableWords N q t + tool) := by
  let current := executeOps rom (lead ++ [branch]) state
  have hnonzero : ¬(state.heap (state.register .address)).toNat = 0 := by rw [hlabel]; omega
  have hpc : current.pc = BitVec.ofNat bits 15 := by
    dsimp only [current]
    rw [prefix_pc rom state hp, ite_eq_right hnonzero]
  have hactive : current.halted = false := by dsimp only [current]; rw [executeOps_halted, ha]
  have hv : (current.register .value).toNat = tool + 1 := by
    dsimp only [current]
    rw [prefix_value]
    exact hlabel
  have hval := body_value rom current N q t tool capWords hb hpositive hw hN hq
    (by rw [prefix_heap]; exact ht) (by rw [prefix_heap]; exact hbits) hv
    (by rw [prefix_width]; exact hwidth) (by rw [prefix_mask]; exact hmask)
    hN1 hq2 ht1 hprod haddress hcap hs hn
  dsimp only
  rw [show 37 = 3 + 34 from rfl, PSTRWordSegments.run_add, prefix_run rom state hb hp ha,
    body_halt rom current hb hpc hactive]
  refine ⟨rfl, (body_heap rom current).trans (prefix_heap rom state), ?_⟩
  simpa only [show current.heap = state.heap from prefix_heap rom state] using hval

theorem actual_trace_bound {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (packingDynamicTrace rom program 37 state).length ≤ 444 :=
  packingDynamicTrace_length_le rom program 37 state

end PaperProofs.Structure.LaminarTree.PSTRLeafUsedRun
