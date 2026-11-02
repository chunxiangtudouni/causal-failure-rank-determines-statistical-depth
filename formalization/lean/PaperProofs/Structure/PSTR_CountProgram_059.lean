module

public import PaperProofs.Structure.PSTR_OuterCountCode_053
public import PaperProofs.Structure.PSTR_BootstrapIn_058
public import PaperProofs.Structure.PSTR_OriginalCountRoom_056

/-! A literal positive-q count-preparation body. Its61op raw bootstrap and
478op outer traversal occupy ONE539op instruction array. Full traversal
induction is separate; this module proves the real code/layout/entry prefix.
No command-dependent table or answer occurs in this fixed instruction list. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountProgram

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims

def program : List PackingOp := PSTRCountBootstrapCode.program ++ PSTROuterCountCode.programAt 61

theorem program_length : program.length = 539 := by
  simp only [program, List.length_append, PSTRCountBootstrapCode.program_length, PSTROuterCountCode.programAt_length]

theorem code_length : (packingCode program).length = 2700 := by rw [packingCode_length, program_length]

theorem bootstrap_contains : PSTRBootstrapSlices.Contains program := by
  refine ⟨by rw [program_length]; decide, ?_⟩
  intro i hi
  exact List.getElem_append_left hi

theorem outer_contains : PSTROuterCountCode.Contains program 61 := by
  refine ⟨by rw [program_length, PSTROuterCountCode.programAt_length], ?_⟩
  intro i hi
  change (PSTRCountBootstrapCode.program ++ PSTROuterCountCode.programAt 61)[61 + i]'(by
    rw [List.length_append, PSTRCountBootstrapCode.program_length, PSTROuterCountCode.programAt_length]
    rw [PSTROuterCountCode.programAt_length] at hi
    omega) = _
  rw [List.getElem_append_right (by rw [PSTRCountBootstrapCode.program_length]; omega)]
  simp only [PSTRCountBootstrapCode.program_length, Nat.add_sub_cancel_left]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem literal_words_below : (packingCode program).all (fun word => decide (word < 4096)) = true := by
  decide

theorem literal_word_bound (word : Nat) (hw : word ∈ packingCode program) : word < 4096 :=
  of_decide_eq_true (List.all_eq_true.mp literal_words_below word hw)

theorem code_fit {bits : Nat} (hb : 12 ≤ bits) : WordsFit bits (packingCode program) := by
  intro word hw
  exact (literal_word_bound word hw).trans_le
    (show 2 ^ 12 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)

theorem pc_fit {bits : Nat} (hb : 12 ≤ bits) : Fits bits (5 * program.length) := by
  rw [program_length]
  have hp : 4096 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb
  unfold Fits
  omega

theorem original_active_bootstrap {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (hq : 0 < q) (hl : LaminarSchedule full)
    (heap : BitVec (indexWidth 32 full.length q) → BitVec (indexWidth 32 full.length q))
    (rep : HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration heap) :
    let bits := indexWidth 32 full.length q
    let capWords := capacityWords 8192 full.length q (treeSize q full)
    let workspace := PSTRCountWorkspace.base q full capWords bits
    let after := packingRun (callInput q full command) program
      (8 * CapacityBits.width q + 56) (packingInitial heap)
    after.halted = false ∧ after.pc = BitVec.ofNat bits 305 ∧
      after.register .old = BitVec.ofNat bits (workspace + 16) ∧
      after.register .index = BitVec.ofNat bits 0 ∧ after.register .fresh = BitVec.ofNat bits 0 ∧
      after.register .value = BitVec.ofNat bits 0 ∧
      (∀ offset < 4, after.heap (BitVec.ofNat bits (workspace + 12 + offset)) =
        if offset = 0 then BitVec.ofNat bits (CapacityBits.width q)
        else if offset = 1 then AlgorithmClaims.PackedCapacityRAM.lowMask bits (CapacityBits.width q)
        else BitVec.ofNat bits 0) ∧
      HeapRepresents q full capWords configuration after.heap := by
  have hb := PSTROriginalCountRoom.word_lower full.length q
  have raw := PSTROriginalCountRoom.raw_rooms full.length q
  have wr := PSTROriginalCountRoom.workspace_rooms full 8192 8192 (by decide) (by decide) (by decide) hq hl
  have hc := code_fit (bits := indexWidth 32 full.length q) (by omega)
  have hp := pc_fit (bits := indexWidth 32 full.length q) (by omega)
  have h := PSTRBootstrapIn.actual_bootstrap program bootstrap_contains hc hp full command configuration _ heap
    (by omega) hq rep raw.1 raw.2.1 raw.2.2 wr.1
  have hr := PSTRBootstrapIn.heap_represents program bootstrap_contains hc hp full command configuration _ heap
    (by omega) hq rep raw.1 raw.2.1 raw.2.2 wr.1 (PSTROriginalCountRoom.bitmap_room full 8192 hq)
    (PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide))
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, hr⟩

end PaperProofs.Structure.LaminarTree.PSTRCountProgram
