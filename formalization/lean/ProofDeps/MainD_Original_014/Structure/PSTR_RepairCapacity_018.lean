module

public import Structure.PSTR_RuntimeRepair_017

/-! Capacity bounds through every prefix of the one contiguous repair run.
The two physical stores occur at the used bit and the uncompressed stage
word. No safe-run or intermediate capacity predicate is assumed. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRRepairCapacity

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims
open PSTRRuntimeRepair

theorem execute_prefix_heap {bits q : Nat} (rom : PhysicalROM) (state : WordState bits)
    (hb : 0 < bits) (hw : CapacityBits.width q ≤ bits)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hh : (state.heap (BitVec.ofNat bits 3)).toNat = bits)
    (hs : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (packed : Nat)
    (hp : (PSTRRuntimeMarkUsed.markHeap
      ((state.register .address).toNat * CapacityBits.width q) state.heap
      (BitVec.ofNat bits 2)).toNat = packed)
    (count : Nat) (hc : count ≤ 21) :
    (executeOps rom (program.take count) state).heap =
      if count < 13 then state.heap
      else if count < 21 then PSTRRuntimeMarkUsed.markHeap
        ((state.register .address).toNat * CapacityBits.width q) state.heap
      else PSTRRuntimeAdvance.bumpHeap packed (PSTRRuntimeMarkUsed.markHeap
        ((state.register .address).toNat * CapacityBits.width q) state.heap) := by
  by_cases hsmall : count ≤ 13
  · rw [program, List.take_append_of_le_length (by simpa only [PSTRRuntimeMarkUsed.program_length] using hsmall),
      PSTRRuntimeMarkUsed.prefix_heap rom state hb hw hwidth hh hs count hsmall]
    by_cases he : count < 13
    · simp only [he, ite_true]
    · have heq : count = 13 := by omega
      subst count
      rfl
  · have hlarge : 13 ≤ count := by omega
    have hcount : count - 13 ≤ 8 := by omega
    have he : count = PSTRRuntimeMarkUsed.program.length + (count - 13) := by
      rw [PSTRRuntimeMarkUsed.program_length]
      omega
    have hm := PSTRRuntimeMarkUsed.execute_heap rom state hb hw hwidth hh hs
    have hmid : ((executeOps rom PSTRRuntimeMarkUsed.program state).heap
        (BitVec.ofNat bits 2)).toNat = packed := by rw [hm]; exact hp
    rw [program, he, List.take_length_add_append, executeOps_append,
      PSTRRuntimeAdvance.prefix_heap rom _ packed hmid _ hcount]
    rw [hm]
    have hnot : ¬count < 13 := by omega
    have hiff : count - 13 < 8 ↔ count < 21 := by omega
    have he' : 13 + (count - 13) = count := by omega
    simp only [PSTRRuntimeMarkUsed.program_length, he', hnot, ite_false, hiff]

theorem actual_prefix_capacity {bits q : Nat} (rom : PhysicalROM)
    (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (state : WordState bits) (tool : Fin q)
    (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (unused : tool ∉ configuration.used)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hi : ∀ offset < 2 + (staticMetadata q full).length,
      Fits bits (4 + packedCapacityWords q capWords bits + offset))
    (hnext : Fits bits (configuration.stage + 1))
    (haddress : (state.register .address).toNat = tableWords full.length q (treeSize q full) + tool.val)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 22) :
    CapacityPrefixBounded q capWords
      (logicalHeap q capWords (packingRun rom program count state).heap) := by
  have haddr : (state.register .address).toNat < capWords := by
    rw [haddress]
    have ht := tool.isLt
    omega
  have hwp : 0 < CapacityBits.width q := Nat.pos_of_ne_zero (by
    intro he
    exact (ne_of_gt hq) ((CapacityBits.width_eq_zero_iff q).mp he))
  have hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q) :=
    (Nat.mul_lt_mul_of_pos_right haddr hwp).trans
      ((Nat.le_add_left (capWords * CapacityBits.width q) 4).trans_lt hr)
  have hstartlt : (state.register .address).toNat * CapacityBits.width q <
      capWords * CapacityBits.width q := Nat.mul_lt_mul_of_pos_right haddr hwp
  have hptr := PSTRMarkUsedBits.physical_fit_of_offset _ _ hstartlt hr
  have hhead : (PSTRRuntimeMarkUsed.markHeap
      ((state.register .address).toNat * CapacityBits.width q) state.heap
      (BitVec.ofNat bits 2)).toNat = packedCapacityWords q capWords bits := by
    rw [PSTRRuntimeMarkUsed.markHeap_header _ state.heap hb hptr 2 (by decide)]
    exact rep.2.2.1
  have hcap := (rep.2.2.2.2.2.2.2.2 hq).2
  have hz : logicalHeap q capWords state.heap (state.register .address).toNat = 0 := by
    rw [haddress]
    simpa only [unused, decide_false, bit, Bool.false_eq_true, ite_false] using
      rep.2.2.2.2.2.2.2.1 tool
  have hmarked := PSTRMarkUsedHeap.mark_capacity_bounded state.heap capWords
    (state.register .address).toNat (by omega) hq haddr hr hz hcap
  by_cases hend : count = 22
  · subst count
    exact ((actual_repair rom full configuration capWords state tool hb hq hw rep unused
      bitmap hr hi hnext haddress hwidth hp ha).2.2.2.2.2.2.2.2.2 hq).2
  · have hcount : count ≤ program.length := by rw [program_length]; omega
    rw [packingRun_eq_executeOps_take rom program state program_straight (code_fit hb)
      (pc_fit hb) hp ha count hcount,
      execute_prefix_heap rom state (by omega) hw hwidth rep.2.2.2.1 hstart
        (packedCapacityWords q capWords bits) hhead count (by rw [← program_length]; exact hcount)]
    split_ifs with hfirst hsecond
    · exact hcap
    · exact hmarked
    · intro address haddress
      have hpidx : Fits bits (4 + packedCapacityWords q capWords bits) := by
        simpa only [Nat.add_zero] using hi 0 (by omega)
      rw [PSTRAdvanceHeap.bump_capacity _ capWords address (by omega) hq haddress hr hpidx]
      exact hmarked address haddress

end PaperProofs.Structure.LaminarTree.PSTRRepairCapacity
