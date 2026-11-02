module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009ao

/-! Descent's real readonly index/leaf prelude and85+1-op body's prefix
certificates. All actual source cells and restoration facts are derived
from the current represented heap, not supplied as per-prefix oracles. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 3400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def descendRead : List PackingOp := descendIndex ++ leafReadProgram

theorem descendRead_noStore : ∀ op ∈ descendRead, HeapPreservingOp op := by
  intro op ho
  rcases List.mem_append.mp ho with hi | hl
  · have hn : ∀ item ∈ descendIndex, HeapPreservingOp item := by simp [descendIndex, HeapPreservingOp]
    exact hn op hi
  · exact leafReadProgram_noStore op hl

theorem descendTest_noStore (origin : Nat) : ∀ op ∈ descendTest origin, HeapPreservingOp op := by
  simp [descendTest, descendTestLead, HeapPreservingOp]

theorem descendRead_result {bits q capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hptr : state.heap (BitVec.ofNat bits (header + 14)) = BitVec.ofNat bits (nodeSlot header q size))
    (hbound : (state.heap (BitVec.ofNat bits (nodeSlot header q size))).toNat ≤ size) :
    (executeOps (callInput q full command) descendRead state).register .address = BitVec.ofNat bits header ∧
      (executeOps (callInput q full command) descendRead state).heap = state.heap := by
  let current := (state.heap (BitVec.ofNat bits (nodeSlot header q size))).toNat
  let node := clampedNode layout current hbound
  let indexed := executeOps (callInput q full command) descendIndex state
  have hn : state.heap (BitVec.ofNat bits (nodeSlot header q size)) = BitVec.ofNat bits current := by
    simp only [current, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hi := descendIndex_result (callInput q full command) header (nodeSlot header q size) current state
    layout.oneFits (hbound.trans_lt layout.sizeFits) hh hptr hn
  have hl := execute_leafRead full command configuration capWords indexed node layout.bits8 layout.positive
    (by rw [hi.2.2]; exact rep) layout.lengthFits hi.1
  rw [descendRead, executeOps_append]
  exact ⟨by simpa only [← layout.header_eq] using hl.1, hl.2.2.2.1.trans hi.2.2⟩

theorem descendIndex_access {bits q capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (rom : PhysicalROM) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hptr : state.heap (BitVec.ofNat bits (header + 14)) = BitVec.ofNat bits (nodeSlot header q size))
    (clock : Nat) (hc : clock < descendIndex.length) :
    packingAccessFits rom heapWords (executeOps rom (descendIndex.take clock) state) descendIndex[clock] := by
  have he := layout.allocated
  change clock < 6 at hc
  interval_cases clock <;> try exact True.intro
  all_goals simp +decide only [descendIndex, List.take_succ_cons, List.take_zero, List.getElem_cons_succ, List.getElem_cons_zero,
    executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte, hh, hptr,
    BitVec.ofNat_add_ofNat, packingAccessFits, AccessFits, BitVec.toNat_ofNat]
  all_goals exact (Nat.mod_le _ _).trans_lt (by unfold endpoint nodeSlot childBase at *; omega)

theorem descendTest_access {bits q capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (rom : PhysicalROM) (origin : Nat) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header)
    (clock : Nat) (hc : clock < (descendTest origin).length) :
    packingAccessFits rom heapWords (executeOps rom ((descendTest origin).take clock) state) (descendTest origin)[clock] := by
  have he := layout.allocated
  change clock < 5 at hc
  interval_cases clock <;> try exact True.intro
  simp +decide only [descendTest, descendTestLead, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
    List.getElem_cons_succ, List.getElem_cons_zero, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, hh, BitVec.ofNat_add_ofNat, packingAccessFits, AccessFits, BitVec.toNat_ofNat]
  exact (Nat.mod_le _ _).trans_lt (by unfold endpoint childBase at *; omega)

theorem descendBody_access {bits q capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (origin : Nat) (state : WordState bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hptr : state.heap (BitVec.ofNat bits (header + 14)) = BitVec.ofNat bits (nodeSlot header q size))
    (htool : state.heap (BitVec.ofNat bits (header + 15)) = BitVec.ofNat bits (toolSlot header q size))
    (hbase : state.heap (BitVec.ofNat bits (header + 10)) = BitVec.ofNat bits (childBase header q))
    (hbound : (state.heap (BitVec.ofNat bits (nodeSlot header q size))).toNat ≤ size) :
    ∀ clock (hc : clock < (descendBody origin).length), packingAccessFits (callInput q full command) heapWords
      (executeOps (callInput q full command) ((descendBody origin).take clock) state) (descendBody origin)[clock] := by
  let rom := callInput q full command
  let current := (state.heap (BitVec.ofNat bits (nodeSlot header q size))).toNat
  let node := clampedNode layout current hbound
  let indexed := executeOps rom descendIndex state
  let loaded := executeOps rom descendRead state
  have hn : state.heap (BitVec.ofNat bits (nodeSlot header q size)) = BitVec.ofNat bits current := by
    simp only [current, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hi := descendIndex_result rom header (nodeSlot header q size) current state layout.oneFits
    (hbound.trans_lt layout.sizeFits) hh hptr hn
  have hr := descendRead_result layout command configuration state rep hh hptr hbound
  have hl := PA17A19RuntimeRead007.access_append rom heapWords descendIndex leafReadProgram state
    (descendIndex_access layout rom state hh hptr)
    (leafReadProgram_access layout command configuration indexed node (by rw [hi.2.2]; exact rep) hi.1)
  have ht := descendTail_access layout rom origin current hbound loaded hr.1
    (by rw [hr.2]; exact hptr) (by rw [hr.2]; exact htool) (by rw [hr.2]; exact hbase) (by rw [hr.2]; exact hn)
  rw [descendBody_eq]
  exact PA17A19RuntimeRead007.access_append rom heapWords descendRead (descendTail origin) state hl ht

theorem descendBody_prefixFrame {bits q capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (origin : Nat) (state : WordState bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hptr : state.heap (BitVec.ofNat bits (header + 14)) = BitVec.ofNat bits (nodeSlot header q size))
    (htool : state.heap (BitVec.ofNat bits (header + 15)) = BitVec.ofNat bits (toolSlot header q size))
    (hbound : (state.heap (BitVec.ofNat bits (nodeSlot header q size))).toNat ≤ size)
    (address : BitVec bits) (hn : address ≠ BitVec.ofNat bits (nodeSlot header q size))
    (ht : address ≠ BitVec.ofNat bits (toolSlot header q size)) (hf : address ≠ BitVec.ofNat bits (header + 13)) :
    WordPrefixFrame (callInput q full command) (descendBody origin) state address := by
  have hr := descendRead_result layout command configuration state rep hh hptr hbound
  rw [descendBody_eq]
  exact WordPrefixFrame.append (callInput q full command) descendRead (descendTail origin) state address
    (WordPrefixFrame.noStore _ descendRead state address descendRead_noStore)
    (descendTail_prefixFrame layout _ origin _ hr.1 (by rw [hr.2]; exact hptr) (by rw [hr.2]; exact htool) address hn ht hf)

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
