module

public import Structure.PSTR_AdvanceHeap_016

/-! The real no-tool branch writes the original failed flag. It loads the
packed-region length from the actual header and has one final HALT. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRRuntimeFail

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def program : List PackingOp :=
  [.base (.base (.constant .address 2)),
   .base (.base (.loadHeap .index .address)),
   .base (.base (.constant .fresh 5)),
   .base (.base (.add .index .index .fresh)),
   .base (.base (.constant .value 1)),
   .base (.base (.storeHeap .index .value))]

def failHeap {bits : Nat} (packed : Nat) (heap : BitVec bits → BitVec bits) :
    BitVec bits → BitVec bits :=
  Function.update heap (BitVec.ofNat bits (5 + packed)) (BitVec.ofNat bits 1)

theorem program_length : program.length = 6 := rfl

theorem program_straight : StraightProgram program := by
  simp [StraightProgram, StraightOp, program]

theorem code_length : (packingCode program).length = 35 := by
  rw [packingCode_length, program_length]

theorem code_fit {bits : Nat} (hb : 8 ≤ bits) : WordsFit bits (packingCode program) := by
  have hpow : 256 ≤ 2 ^ bits :=
    (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  intro value hv
  simp [packingCode, program, PackingOp.encode, Op.encodeWords, Instruction.encodeWords,
    Register.word, Region.word, haltWords] at hv
  unfold Fits
  omega

theorem pc_fit {bits : Nat} (hb : 8 ≤ bits) : Fits bits (5 * program.length) := by
  have hpow : 256 ≤ 2 ^ bits :=
    (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  change 30 < 2 ^ bits
  omega

theorem execute_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) (packed : Nat)
    (hh : (state.heap (BitVec.ofNat bits 2)).toNat = packed) :
    (executeOps rom program state).heap = failHeap packed state.heap := by
  have hc : packed + 5 = 5 + packed := by omega
  simp +decide only [program, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, PSTRRuntimeAdvance.header_word state packed hh,
    BitVec.ofNat_add_ofNat, hc, failHeap]

theorem heap_frame {bits : Nat} (packed : Nat) (heap : BitVec bits → BitVec bits)
    (address : BitVec bits) (hne : address ≠ BitVec.ofNat bits (5 + packed)) :
    failHeap packed heap address = heap address := by
  exact Function.update_of_ne hne _ _

theorem header_frame {bits : Nat} (packed : Nat) (heap : BitVec bits → BitVec bits)
    (hb : 8 ≤ bits) (hp : Fits bits (5 + packed)) (header : Nat) (hh : header < 4) :
    failHeap packed heap (BitVec.ofNat bits header) = heap (BitVec.ofNat bits header) := by
  apply heap_frame
  have hbits := Nat.lt_two_pow_self (n := bits)
  have hf : Fits bits header := hh.trans (show 4 < 2 ^ bits by omega)
  apply (ofNat_injective_of_fit header (5 + packed) hf hp).not.mpr
  omega

theorem capacity_frame {bits q : Nat} (heap : BitVec bits → BitVec bits)
    (capWords address : Nat) (hb : 0 < bits) (hq : 0 < q) (ha : address < capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hp : Fits bits (5 + packedCapacityWords q capWords bits)) :
    logicalHeap q capWords (failHeap (packedCapacityWords q capWords bits) heap) address =
      logicalHeap q capWords heap address := by
  rw [PSTRMarkUsedBits.scalar_stream _ _ _ hq ha hr,
    PSTRMarkUsedBits.scalar_stream _ _ _ hq ha hr]
  apply congrArg CapacityBits.decodeScalar
  apply congrArg List.ofFn
  funext i
  have hm := Nat.mul_le_mul_right (CapacityBits.width q) (Nat.succ_le_of_lt ha)
  rw [Nat.succ_mul] at hm
  have hoff : address * CapacityBits.width q + i.val < capWords * CapacityBits.width q := by
    have hi := i.isLt
    omega
  have hd : (address * CapacityBits.width q + i.val) / bits <
      packedCapacityWords q capWords bits :=
    (Nat.div_lt_iff_lt_mul hb).mpr
      (hoff.trans_le (packedCapacityWords_mul_bits q capWords hb))
  unfold PSTRMarkUsedBits.bitAt
  rw [heap_frame]
  apply (ofNat_injective_of_fit _ _
    (PSTRMarkUsedBits.physical_fit_of_offset _ _ hoff hr) hp).not.mpr
  omega

theorem index_value {bits q : Nat} (heap : BitVec bits → BitVec bits)
    (capWords offset : Nat) (hb : 8 ≤ bits) (hq : 0 < q)
    (hp : Fits bits (5 + packedCapacityWords q capWords bits))
    (hi : Fits bits (4 + packedCapacityWords q capWords bits + offset)) :
    logicalHeap q capWords (failHeap (packedCapacityWords q capWords bits) heap)
      (capWords + offset) =
      if offset = 1 then 1 else logicalHeap q capWords heap (capWords + offset) := by
  have hnot : ¬capWords + offset < capWords := by omega
  have hid : Fits bits (packedCapacityWords q capWords bits + offset) := by
    exact (show packedCapacityWords q capWords bits + offset ≤
      4 + packedCapacityWords q capWords bits + offset by omega).trans_lt hi
  simp only [logicalHeap, ne_of_gt hq, ite_false, unpackHeap, hnot,
    Nat.add_sub_cancel_left]
  rw [PSTRRuntimePackedRead.dataHeap_at _ _ hid, PSTRRuntimePackedRead.dataHeap_at _ _ hid]
  by_cases he : offset = 1
  · subst offset
    have hptr : 4 + (packedCapacityWords q capWords bits + 1) =
        5 + packedCapacityWords q capWords bits := by omega
    have hone : 1 < 2 ^ bits := by have hh := Nat.lt_two_pow_self (n := bits); omega
    simp only [ite_true, hptr, failHeap, Function.update_self, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hone]
  · rw [ite_eq_right he, heap_frame]
    apply (ofNat_injective_of_fit _ _ (by simpa only [Nat.add_assoc] using hi) hp).not.mpr
    omega

theorem heapRepresents_fail {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords : Nat) (heap : BitVec bits → BitVec bits)
    (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hi : ∀ offset < 2 + (staticMetadata q full).length,
      Fits bits (4 + packedCapacityWords q capWords bits + offset)) :
    HeapRepresents q full capWords { configuration with failed := true }
      (failHeap (packedCapacityWords q capWords bits) heap) := by
  have hp : Fits bits (5 + packedCapacityWords q capWords bits) := by
    have hh := hi 1 (by omega)
    convert hh using 1; omega
  have hindex (offset : Nat) (hoff : offset < 2 + (staticMetadata q full).length)
      (hne : offset ≠ 1) :
      logicalHeap q capWords (failHeap (packedCapacityWords q capWords bits) heap)
          (capWords + offset) = logicalHeap q capWords heap (capWords + offset) := by
    rw [index_value heap capWords offset hb hq hp (hi offset hoff), ite_eq_right hne]
  dsimp only [HeapRepresents] at rep ⊢
  obtain ⟨ht, hc, hphead, hbits, hstage, hfailed, hmetadata, hused, htable⟩ := rep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [header_frame _ heap hb hp 0 (by decide)]; exact ht
  · rw [header_frame _ heap hb hp 1 (by decide)]; exact hc
  · rw [header_frame _ heap hb hp 2 (by decide)]; exact hphead
  · rw [header_frame _ heap hb hp 3 (by decide)]; exact hbits
  · simpa only [Nat.add_zero] using (hindex 0 (by omega) (by decide)).trans hstage
  · simpa only [ite_true, bit, ite_true] using index_value heap capWords 1 hb hq hp (hi 1 (by omega))
  · intro position hposition
    have hf := hindex (2 + position) (by omega) (by omega)
    have hm : logicalHeap q capWords heap (capWords + (2 + position)) =
        (staticMetadata q full)[position] := by
      simpa only [Nat.add_assoc] using hmetadata position hposition
    simpa only [Nat.add_assoc] using hf.trans hm
  · intro tool
    rw [capacity_frame heap capWords _ (by omega) hq (by have ht := tool.isLt; omega) hr hp]
    exact hused tool
  · intro hpositive
    have hsize : treeSize q full = (prepareNormalization q full).indexed.nodes.size := by
      simp only [treeSize, ne_of_gt hq, ite_false]
    refine ⟨?_, ?_⟩
    · apply PA17RequestPaths016.physicalTableCorrect_of_frame q full _ _ (htable hpositive).1
      intro index hidx
      have hsmall : index < tableWords full.length q (treeSize q full) := by
        simpa only [hsize] using hidx
      exact capacity_frame heap capWords index (by omega) hq (hsmall.trans_le (by omega)) hr hp
    · intro address ha
      rw [capacity_frame heap capWords address (by omega) hq ha hr hp]
      exact (htable hpositive).2 address ha

theorem actual_error_none {bits q : Nat} (rom : PhysicalROM) (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (allowed : Allowed full configuration .error)
    (hchoose : (callback q full ⟨configuration.stage, by have hs := allowed.2; omega⟩
      configuration.used).tool = none)
    (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hi : ∀ offset < 2 + (staticMetadata q full).length,
      Fits bits (4 + packedCapacityWords q capWords bits + offset))
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    let after := packingRun rom program 7 state
    after.halted = true ∧ HeapRepresents q full capWords
      (nextConfiguration q full configuration .error) after.heap := by
  dsimp only
  rw [show 7 = program.length + 1 from rfl,
    packingRun_executeOps_halt rom _ _ program_straight (code_fit hb) (pc_fit hb) hp ha]
  refine ⟨rfl, ?_⟩
  rw [execute_heap rom state (packedCapacityWords q capWords bits) rep.2.2.1]
  have hs : configuration.stage < full.length + 1 := by have hh := allowed.2; omega
  simp only [nextConfiguration, hs, dite_true, hchoose]
  exact heapRepresents_fail full configuration capWords state.heap hb hq rep bitmap hr hi

theorem actual_trace_bound {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (packingDynamicTrace rom program 7 state).length ≤ 84 :=
  packingDynamicTrace_length_le rom program 7 state

end PaperProofs.Structure.LaminarTree.PSTRRuntimeFail
