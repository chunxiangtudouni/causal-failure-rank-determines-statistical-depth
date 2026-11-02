module

public import PaperProofs.Structure.PSTR_CountMemory_051
public import PaperProofs.Structure.PSTR_CountInit_038

/-! Spatial frames for EVERY prefix of the actual outer stores. Earlier
lower-prefix frames do not imply these high-address results. All Word
addresses are proved distinct using original finite-width injectivity. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTROuterStoreFrame

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRQueryLayout

theorem sentinel_prefix_outside {bits : Nat} (rom : PhysicalROM) (workspace size : Nat)
    (state : WordState bits)
    (hb : state.register .old = BitVec.ofNat bits (countsBase workspace))
    (ht : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size)
    (address : BitVec bits) (hne : address ≠ BitVec.ofNat bits (parentsBase workspace size))
    (count : Nat) (hc : count ≤ 5) :
    (executeOps rom (PSTRParentSentinel.program.take count) state).heap address = state.heap address := by
  by_cases hbefore : count ≤ 4
  · interval_cases count <;> rfl
  · have he : count = 5 := by omega
    subst count
    rw [List.take_of_length_le (show PSTRParentSentinel.program.length ≤ 5 by rw [PSTRParentSentinel.program_length]),
      PSTRParentSentinel.execute_heap rom workspace size state hb ht, Function.update_of_ne hne]

theorem parent_prefix_outside {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (node : (prepareNormalization q full).indexed.NodeId) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap) (hN : Fits bits full.length)
    (hi : state.register .index = BitVec.ofNat bits node.val)
    (address : BitVec bits)
    (hne : address ≠ BitVec.ofNat bits (parentsBase (PSTRCountWorkspace.base q full capWords bits)
      (prepareNormalization q full).indexed.nodes.size + node.val + 1))
    (count : Nat) (hc : count ≤ 50) :
    (executeOps (callInput q full command) (PSTRParentCopy.program.take count) state).heap address = state.heap address := by
  by_cases hbefore : count ≤ 49
  · rw [PSTRParentCopy.before_store_heap _ state count hbefore]
  · have he : count = 50 := by omega
    subst count
    rw [List.take_of_length_le (show PSTRParentCopy.program.length ≤ 50 by rw [PSTRParentCopy.program_length]),
      PSTRParentCopy.execute_parent full command configuration capWords state node hb hq rep hN hi,
      Function.update_of_ne hne]

theorem parent_prefix_high {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (node : (prepareNormalization q full).indexed.NodeId) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap) (hN : Fits bits full.length)
    (hi : state.register .index = BitVec.ofNat bits node.val)
    (hroom : Fits bits (parentsBase (PSTRCountWorkspace.base q full capWords bits)
      (prepareNormalization q full).indexed.nodes.size + (prepareNormalization q full).indexed.nodes.size))
    (physical : Nat) (hp : Fits bits physical)
    (hhigh : parentsBase (PSTRCountWorkspace.base q full capWords bits)
      (prepareNormalization q full).indexed.nodes.size + (prepareNormalization q full).indexed.nodes.size < physical)
    (count : Nat) (hc : count ≤ 50) :
    (executeOps (callInput q full command) (PSTRParentCopy.program.take count) state).heap
      (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
  apply parent_prefix_outside full command configuration capWords state node hb hq rep hN hi _ ?_ count hc
  have hn := node.isLt
  have ht : Fits bits (parentsBase (PSTRCountWorkspace.base q full capWords bits)
      (prepareNormalization q full).indexed.nodes.size + node.val + 1) :=
    (show parentsBase (PSTRCountWorkspace.base q full capWords bits)
      (prepareNormalization q full).indexed.nodes.size + node.val + 1 ≤
        parentsBase (PSTRCountWorkspace.base q full capWords bits)
          (prepareNormalization q full).indexed.nodes.size + (prepareNormalization q full).indexed.nodes.size by omega).trans_lt hroom
  exact (ofNat_injective_of_fit _ _ hp ht).not.mpr (by omega)

set_option maxRecDepth 6000 in
theorem spill_prefix_high {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (base : Nat) (hf : state.register .flag = BitVec.ofNat bits base)
    (hroom : Fits bits (base + 3)) (physical : Nat) (hp : Fits bits physical) (hhigh : base + 3 < physical)
    (count : Nat) (hc : count ≤ 8) :
    (executeOps rom (PSTRReplySpill.spillProgram.take count) state).heap (BitVec.ofNat bits physical) =
      state.heap (BitVec.ofNat bits physical) := by
  have hne (offset : Nat) (ho : offset ≤ 3) :
      BitVec.ofNat bits physical ≠ BitVec.ofNat bits (base + offset) :=
    (ofNat_injective_of_fit _ _ hp (PSTRReplySpill.slot_fit base hroom offset ho)).not.mpr (by omega)
  have hz := hne 0 (by decide)
  simp only [Nat.add_zero] at hz
  have h2 : base + 1 + 1 = base + 2 := by omega
  have h3 : base + 2 + 1 = base + 3 := by omega
  interval_cases count <;>
    simp +decide only [PSTRReplySpill.spillProgram, List.take_succ_cons, List.take_zero, executeOps,
      packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte,
      hf, BitVec.ofNat_add_ofNat, h2, h3, hz, hne 1 (by decide), hne 2 (by decide), hne 3 (by decide)]

theorem init_prefix_high {bits : Nat} (rom : PhysicalROM) (workspace : Nat) (state : WordState bits)
    (ha : state.register .address = BitVec.ofNat bits workspace)
    (hroom : Fits bits (workspace + 15)) (physical : Nat) (hp : Fits bits physical) (hhigh : workspace + 15 < physical)
    (count : Nat) :
    (executeOps rom (PSTRCountInit.program.take count) state).heap (BitVec.ofNat bits physical) =
      state.heap (BitVec.ofNat bits physical) := by
  have hs : Fits bits ((workspace + 12) + 3) := by simpa only [Nat.add_assoc] using hroom
  have regs := PSTRCountInit.head_registers rom workspace state ha
  change (executeOps rom ((PSTRCountInit.head ++ (PSTRReplySpill.spillProgram ++ PSTRCountInit.tail)).take count) state).heap
    (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical)
  by_cases hfirst : count ≤ 7
  · rw [List.take_append_of_le_length (show count ≤ PSTRCountInit.head.length from hfirst),
      PSTRCountInit.head_prefix_heap rom state count hfirst]
  · rw [List.take_append,
      List.take_of_length_le (show PSTRCountInit.head.length ≤ count by rw [PSTRCountInit.head_length]; omega),
      executeOps_append, PSTRCountInit.head_length]
    by_cases hspill : count - 7 ≤ 8
    · rw [List.take_append_of_le_length (show count - 7 ≤ PSTRReplySpill.spillProgram.length from hspill)]
      exact (spill_prefix_high rom (executeOps rom PSTRCountInit.head state) (workspace + 12)
        regs.2.2.2.2.1 hs physical hp (by omega) (count - 7) hspill).trans (congrFun regs.2.2.2.2.2.2 _)
    · rw [List.take_append,
        List.take_of_length_le (show PSTRReplySpill.spillProgram.length ≤ count - 7 by rw [PSTRReplySpill.spill_length]; omega),
        executeOps_append, PSTRCountInit.tail_prefix_heap]
      have frame := spill_prefix_high rom (executeOps rom PSTRCountInit.head state) (workspace + 12)
        regs.2.2.2.2.1 hs physical hp (by omega) 8 le_rfl
      rw [List.take_of_length_le (show PSTRReplySpill.spillProgram.length ≤ 8 by rw [PSTRReplySpill.spill_length])] at frame
      exact frame.trans (congrFun regs.2.2.2.2.2.2 _)

end PaperProofs.Structure.LaminarTree.PSTROuterStoreFrame
