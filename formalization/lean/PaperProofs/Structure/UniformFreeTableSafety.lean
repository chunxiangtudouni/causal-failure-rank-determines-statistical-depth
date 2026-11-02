module

public import PaperProofs.Structure.UniformFreeTableRAM
import Mathlib.Tactic.IntervalCases

/-! The original leading-capacity invariant at every actual Op prefix of
the metadata-plus-free phase. Final heap correctness is not used as a
substitute for these instruction-prefix proofs. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.UniformFreeTableSafety

open IndexedRAM IndexedClosureRAM AlgorithmClaims

def PrefixFrame (rom : ROM) (block : List Op) (address : Nat) : Prop :=
  ∀ (state : State) (count : Nat), count ≤ block.length →
    (execute rom (block.take count) state).heap address = state.heap address

theorem PrefixFrame.append (rom : ROM) (left right : List Op) (address : Nat)
    (hl : PrefixFrame rom left address) (hr : PrefixFrame rom right address) :
    PrefixFrame rom (left ++ right) address := by
  intro state count hc
  by_cases hleft : count ≤ left.length
  · rw [List.take_append_of_le_length hleft]
    exact hl state count hleft
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (show left.length ≤ count by omega)
    have he : extra ≤ right.length := by rw [List.length_append] at hc; omega
    rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left,
      IndexedClosureRAM.execute_append, hr _ extra he]
    simpa only [List.take_length] using hl state left.length le_rfl

theorem PrefixFrame.flatMap {α : Type*} (rom : ROM) (entries : List α) (blocks : α → List Op)
    (address : Nat) (h : ∀ entry ∈ entries, PrefixFrame rom (blocks entry) address) :
    PrefixFrame rom (entries.flatMap blocks) address := by
  induction entries with
  | nil => intro state count _; simp only [List.flatMap_nil, List.take_nil, IndexedClosureRAM.execute]
  | cons head later ih =>
    rw [List.flatMap_cons]
    exact PrefixFrame.append rom _ _ address (h head List.mem_cons_self)
      (ih (fun entry he => h entry (List.mem_cons_of_mem _ he)))

theorem clearBlock_prefixFrame (rom : ROM) (target address : Nat) (hne : address ≠ target) :
    PrefixFrame rom (UniformNormalizationRAM.clearBlock target) address := by
  intro state count hc
  change count ≤ 3 at hc
  interval_cases count <;>
    simp [UniformNormalizationRAM.clearBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute, hne]

theorem readBit_prefixFrame (rom : ROM) (N q node tool address : Nat) :
    PrefixFrame rom (UniformTreeMetadataRAM.readBit N q node tool) address := by
  intro state count hc
  change count ≤ 3 at hc
  interval_cases count <;> rfl

set_option maxRecDepth 10000 in
theorem metadataTail_prefixFrame (rom : ROM) (size base node address : Nat) (ha : address < base) :
    PrefixFrame rom (UniformTreeMetadataRAM.nodeTail size base node) address := by
  have hcard : address ≠ UniformTreeMetadataRAM.cardAddress base node := by dsimp [UniformTreeMetadataRAM.cardAddress]; omega
  have hparent : address ≠ UniformTreeMetadataRAM.parentAddress size base (node + 1) := by
    dsimp [UniformTreeMetadataRAM.parentAddress]; omega
  have hinternal : address ≠ UniformTreeMetadataRAM.internalAddress size base node := by
    dsimp [UniformTreeMetadataRAM.internalAddress]; omega
  intro state count hc
  change count ≤ 13 at hc
  interval_cases count <;>
    simp [UniformTreeMetadataRAM.nodeTail, IndexedClosureRAM.execute, Op.execute, Instruction.execute,
      hcard, hparent, hinternal]

theorem metadataNode_prefixFrame (rom : ROM) (N q size base node address : Nat) (ha : address < base) :
    PrefixFrame rom (UniformTreeMetadataRAM.nodeBlock N q size base node) address := by
  have hh : PrefixFrame rom [.base (.constant .total 0)] address := by
    intro state count hc
    change count ≤ 1 at hc
    interval_cases count <;> rfl
  have hb := PrefixFrame.flatMap rom (List.range q) (UniformTreeMetadataRAM.readBit N q node) address
    (fun tool _ => readBit_prefixFrame rom N q node tool address)
  rw [UniformTreeMetadataRAM.nodeBlock]
  exact PrefixFrame.append rom _ _ address (PrefixFrame.append rom _ _ address hh hb)
    (metadataTail_prefixFrame rom size base node address ha)

theorem metadataProgram_prefixFrame (rom : ROM) (N q size base address : Nat) (ha : address < base) :
    PrefixFrame rom (UniformTreeMetadataRAM.program N q size base) address := by
  rw [UniformTreeMetadataRAM.program]
  apply PrefixFrame.append rom _ _ address
  · apply clearBlock_prefixFrame
    dsimp [UniformTreeMetadataRAM.parentAddress]
    omega
  · exact PrefixFrame.flatMap rom _ _ address (fun node _ => metadataNode_prefixFrame rom N q size base node address ha)

theorem capacityThroughout_append (q words : Nat) (rom : PhysicalROM) (left right : List Op) (state : State)
    (hl : CapacityThroughout q words rom left state)
    (hr : CapacityThroughout q words rom right (execute rom.semantic left state)) :
    CapacityThroughout q words rom (left ++ right) state := by
  intro count hc
  by_cases hleft : count ≤ left.length
  · rw [List.take_append_of_le_length hleft]
    exact hl count hleft
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (show left.length ≤ count by omega)
    have he : extra ≤ right.length := by rw [List.length_append] at hc; omega
    rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left, IndexedClosureRAM.execute_append]
    exact hr extra he

theorem metadataProgram_capacityThroughout (q words : Nat) (rom : PhysicalROM) (N tools size base : Nat)
    (hbase : words ≤ base) (state : State) (hcapacity : CapacityPrefixBounded q words state.heap) :
    CapacityThroughout q words rom (UniformTreeMetadataRAM.program N tools size base) state := by
  intro count hc address ha
  rw [metadataProgram_prefixFrame rom.semantic N tools size base address (ha.trans_le hbase) state count hc]
  exact hcapacity address ha

theorem copyBlock_prefix_heap (rom : ROM) (source index count : Nat) (hc : count < 4) (state : State) :
    (IndexedRAM.execute rom ((IndexedCellRAM.copyBlock source 1 index).take count) state).heap = state.heap := by
  interval_cases count <;> rfl

theorem copyBlock_capacity (q size source index : Nat) (_hi : index < size) (rom : ROM)
    (state : State) (hcapacity : CapacityPrefixBounded q (size + 1) state.heap)
    (hvalue : state.heap (source + index) ≤ q) :
    CapacityPrefixBounded q (size + 1) (IndexedRAM.execute rom (IndexedCellRAM.copyBlock source 1 index) state).heap := by
  intro address ha
  rw [IndexedCellRAM.execute_copyBlock_heap]
  by_cases heq : address = 1 + index
  · rw [heq, Function.update_self]
    exact hvalue
  · rw [Function.update_of_ne heq]
    exact hcapacity address ha

theorem copyBlock_sourceBound (q size source index : Nat) (hsource : size < source) (hi : index < size) (rom : ROM)
    (state : State) (hvalues : ∀ node < size, state.heap (source + node) ≤ q) :
    ∀ node < size, (IndexedRAM.execute rom (IndexedCellRAM.copyBlock source 1 index) state).heap (source + node) ≤ q := by
  intro node hn
  rw [IndexedCellRAM.execute_copyBlock_heap, Function.update_of_ne (by omega)]
  exact hvalues node hn

theorem copyIndices_prefix_capacity (q size source : Nat) (hsource : size < source)
    (rom : ROM) (indices : List Nat) (hindices : ∀ index ∈ indices, index < size)
    (state : State) (hcapacity : CapacityPrefixBounded q (size + 1) state.heap)
    (hvalues : ∀ node < size, state.heap (source + node) ≤ q) (count : Nat)
    (hc : count ≤ (IndexedCellRAM.copyIndices source 1 indices).length) :
    CapacityPrefixBounded q (size + 1)
      (IndexedRAM.execute rom ((IndexedCellRAM.copyIndices source 1 indices).take count) state).heap := by
  induction indices generalizing state count with
  | nil => simpa only [IndexedCellRAM.copyIndices, List.flatMap_nil, List.take_nil, IndexedRAM.execute] using hcapacity
  | cons index later ih =>
    have hlen : (IndexedCellRAM.copyBlock source 1 index).length = 4 := rfl
    rw [IndexedCellRAM.copyIndices, List.flatMap_cons] at hc ⊢
    by_cases hsmall : count < 4
    · rw [List.take_append_of_le_length (by rw [hlen]; omega), copyBlock_prefix_heap rom source index count hsmall state]
      exact hcapacity
    · obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le (show 4 ≤ count by omega)
      rw [heq, List.take_append, List.take_of_length_le (by rw [hlen]; omega), hlen, Nat.add_sub_cancel_left,
        IndexedRAM.execute_append]
      apply ih (fun node hn => hindices node (List.mem_cons_of_mem _ hn)) _
        (copyBlock_capacity q size source index (hindices index List.mem_cons_self) rom state hcapacity
          (hvalues index (hindices index List.mem_cons_self)))
        (copyBlock_sourceBound q size source index hsource (hindices index List.mem_cons_self) rom state hvalues) extra
      rw [List.length_append, hlen] at hc
      simpa only [IndexedCellRAM.copyIndices] using (show extra ≤ (List.flatMap (IndexedCellRAM.copyBlock source 1) later).length by omega)

theorem copyWords_capacityThroughout (q size source : Nat) (hsource : size < source) (rom : PhysicalROM)
    (state : State) (hcapacity : CapacityPrefixBounded q (size + 1) state.heap)
    (hvalues : ∀ node < size, state.heap (source + node) ≤ q) :
    CapacityThroughout q (size + 1) rom ((IndexedCellRAM.copyWords source 1 size).map Op.base) state := by
  intro count hc
  rw [← List.map_take, execute_base]
  exact copyIndices_prefix_capacity q size source hsource rom.semantic (List.range size)
    (fun _ hm => List.mem_range.mp hm) state hcapacity hvalues count
      (by simpa only [List.length_map, IndexedCellRAM.copyWords] using hc)

theorem tag_capacityThroughout (q words : Nat) (hq : 0 < q) (rom : PhysicalROM) (state : State)
    (hcapacity : CapacityPrefixBounded q words state.heap) :
    CapacityThroughout q words rom ((IndexedCellRAM.constantBlock 0 1).map Op.base) state := by
  intro count hc address ha
  change count ≤ 3 at hc
  have htag : Function.update state.heap 0 1 address ≤ q := by
    by_cases hz : address = 0
    · rw [hz, Function.update_self]
      exact hq
    · rw [Function.update_of_ne hz]
      exact hcapacity address ha
  interval_cases count <;> first
    | simpa [IndexedCellRAM.constantBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute] using hcapacity address ha
    | simpa [IndexedCellRAM.constantBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute] using htag

theorem freeProgram_capacityThroughout (q size source : Nat) (hq : 0 < q) (hsource : size < source)
    (rom : PhysicalROM) (state : State) (hcapacity : CapacityPrefixBounded q (size + 1) state.heap)
    (hvalues : ∀ node < size, state.heap (source + node) ≤ q) :
    CapacityThroughout q (size + 1) rom (UniformFreeTableRAM.freeProgram size source) state := by
  have hc := copyWords_capacityThroughout q size source hsource rom state hcapacity hvalues
  rw [UniformFreeTableRAM.freeProgram]
  apply capacityThroughout_append q (size + 1) rom _ _ state hc
  apply tag_capacityThroughout q (size + 1) hq rom _
  simpa only [List.take_length] using hc _ le_rfl

theorem prepared_program_capacityThroughout (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    let size := (prepareNormalization q full).indexed.nodes.size
    CapacityThroughout q (size + 1) (givenTreeROM q full) (UniformFreeTableRAM.program full.length q size)
      (initial (fun _ => 0)) := by
  intro size
  let rom := givenTreeROM q full
  let start := initial (fun _ => 0)
  let metadata := UniformTreeMetadataRAM.program full.length q size (size + 1)
  let before := execute rom.semantic metadata start
  have hzero : CapacityPrefixBounded q (size + 1) start.heap := fun _ _ => Nat.zero_le _
  have hm := metadataProgram_capacityThroughout q (size + 1) rom full.length q size (size + 1) le_rfl start hzero
  have hbefore : CapacityPrefixBounded q (size + 1) before.heap := by
    have hh := hm metadata.length le_rfl
    change CapacityPrefixBounded q (size + 1) (execute rom.semantic (metadata.take metadata.length) start).heap at hh
    rw [List.take_length] at hh
    exact hh
  have hmetadata : UniformTreeMetadataRAM.MetadataCorrect q full (size + 1) before.heap :=
    UniformTreeMetadataRAM.prepared_program_metadata q full hq hlaminar (size + 1) start
  rw [UniformFreeTableRAM.program]
  apply capacityThroughout_append q (size + 1) rom _ _ start hm
  apply freeProgram_capacityThroughout q size (size + 1) hq (by omega) rom before hbefore
  intro node hn
  exact UniformTreeMetadataRAM.metadata_card_bound q full (size + 1) before.heap hmetadata ⟨node, hn⟩

end PaperProofs.Structure.LaminarTree.UniformFreeTableSafety
