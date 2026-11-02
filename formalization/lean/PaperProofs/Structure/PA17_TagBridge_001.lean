module

public import PaperProofs.Structure.UniformFreeTableSafety

/-! A17: physical copies between the old payload-then-tag workspace and
the paper interface's tag-then-payload table. Both directions execute
ordinary heap loads/stores and preserve every word outside the destination.
No representation equality between the two layouts is assumed. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17TagBridge001

open IndexedRAM IndexedClosureRAM AlgorithmClaims IndexedCellRAM

variable {Tool : Type*}

def DisjointSlots (size source target : Nat) : Prop :=
  ∀ left ≤ size, ∀ right ≤ size, source + left ≠ target + right

def TagFirstRep (cache : IndexedNodeCache Tool) (heap : Nat → Nat)
    (base : Nat) : IndexedEntry.FixedEntry cache → Prop
  | .void => heap base = 0
  | .vector capacity => heap base = 1 ∧
      ∀ node : cache.NodeId, heap (base + 1 + node.val) = capacity.get node

def toTagFirst (size source target : Nat) : List Op :=
  (copyWords source (target + 1) size ++ copyWords (source + size) target 1).map Op.base

def toTagLast (size source target : Nat) : List Op :=
  (copyWords (source + 1) target size ++ copyWords source (target + size) 1).map Op.base

theorem toTagFirst_tag (rom : ROM) (size source target : Nat)
    (hdisjoint : DisjointSlots size source target) (state : State) :
    (execute rom (toTagFirst size source target) state).heap target = state.heap (source + size) := by
  rw [toTagFirst, execute_base, IndexedRAM.execute_append]
  have hcopy := copyWords_value rom (source + size) target 1
    (by intro left hl right hr
        have hlz : left = 0 := by omega
        have hrz : right = 0 := by omega
        subst left; subst right
        simpa only [Nat.add_zero] using hdisjoint size le_rfl 0 (Nat.zero_le size))
    (IndexedRAM.execute rom (copyWords source (target + 1) size) state) 0 (by omega)
  simp only [Nat.add_zero] at hcopy
  rw [hcopy]
  apply copyWords_frame
  intro index hi
  have hh := hdisjoint size le_rfl (1 + index) (by omega)
  simpa only [Nat.add_assoc] using hh

theorem toTagFirst_payload (rom : ROM) (size source target : Nat)
    (hdisjoint : DisjointSlots size source target) (state : State)
    (index : Nat) (hi : index < size) :
    (execute rom (toTagFirst size source target) state).heap (target + 1 + index) =
      state.heap (source + index) := by
  rw [toTagFirst, execute_base, IndexedRAM.execute_append,
    copyWords_frame rom (source + size) target 1 _ (target + 1 + index) (by intro j hj; omega)]
  exact copyWords_value rom source (target + 1) size
    (by intro left hl right hr
        simpa only [Nat.add_assoc] using hdisjoint left (by omega) (1 + right) (by omega)) state index hi

theorem toTagFirst_frame (rom : ROM) (size source target : Nat) (state : State)
    (address : Nat) (hframe : ∀ index ≤ size, address ≠ target + index) :
    (execute rom (toTagFirst size source target) state).heap address = state.heap address := by
  rw [toTagFirst, execute_base, IndexedRAM.execute_append,
    copyWords_frame rom (source + size) target 1 _ address (by
      intro index hi
      have hz : index = 0 := by omega
      subst index
      exact hframe 0 (Nat.zero_le size)),
    copyWords_frame rom source (target + 1) size state address (by
      intro index hi
      simpa only [Nat.add_assoc] using hframe (1 + index) (by omega))]

theorem toTagFirst_rep (cache : IndexedNodeCache Tool) (rom : ROM) (source target : Nat)
    (hdisjoint : DisjointSlots cache.nodes.size source target) (state : State)
    (entry : IndexedEntry.FixedEntry cache) (hrep : SlotRep cache state.heap source entry) :
    TagFirstRep cache (execute rom (toTagFirst cache.nodes.size source target) state).heap target entry := by
  cases entry with
  | void => exact (toTagFirst_tag rom _ source target hdisjoint state).trans hrep
  | vector capacity =>
    exact ⟨(toTagFirst_tag rom _ source target hdisjoint state).trans hrep.1,
      fun node => (toTagFirst_payload rom _ source target hdisjoint state node.val node.isLt).trans (hrep.2 node)⟩

theorem readEntry_eq_of_rep (cache : IndexedNodeCache Tool) (slot : Nat) (heap : Nat → Nat)
    (entry : IndexedEntry.FixedEntry cache)
    (hrep : TagFirstRep cache heap (slot * (cache.nodes.size + 1)) entry) :
    readEntry cache.nodes.size slot heap = entry := by
  cases entry with
  | void => simp only [readEntry, show heap (slot * (cache.nodes.size + 1)) = 0 from hrep, ite_true]
  | vector capacity =>
    have hn : heap (slot * (cache.nodes.size + 1)) ≠ 0 := by rw [hrep.1]; omega
    rw [readEntry, ite_eq_right hn]
    apply congrArg CapacityBits.Entry.vector
    apply Vector.ext
    intro index hi
    change (Vector.ofFn _).get ⟨index, hi⟩ = capacity.get ⟨index, hi⟩
    rw [cache_get_ofFn]
    exact hrep.2 ⟨index, hi⟩

theorem toTagFirst_readEntry (cache : IndexedNodeCache Tool) (rom : ROM) (source slot : Nat)
    (hdisjoint : DisjointSlots cache.nodes.size source (slot * (cache.nodes.size + 1)))
    (state : State) (entry : IndexedEntry.FixedEntry cache) (hrep : SlotRep cache state.heap source entry) :
    readEntry cache.nodes.size slot
      (execute rom (toTagFirst cache.nodes.size source (slot * (cache.nodes.size + 1))) state).heap = entry :=
  readEntry_eq_of_rep cache slot _ entry (toTagFirst_rep cache rom source _ hdisjoint state entry hrep)

theorem rep_of_readEntry (cache : IndexedNodeCache Tool) (slot : Nat) (heap : Nat → Nat)
    (entry : IndexedEntry.FixedEntry cache) (htag : heap (slot * (cache.nodes.size + 1)) ≤ 1)
    (heq : readEntry cache.nodes.size slot heap = entry) :
    TagFirstRep cache heap (slot * (cache.nodes.size + 1)) entry := by
  cases entry with
  | void =>
    by_cases hz : heap (slot * (cache.nodes.size + 1)) = 0
    · exact hz
    · simp only [readEntry, hz, ite_false] at heq
      cases heq
  | vector capacity =>
    have hz : heap (slot * (cache.nodes.size + 1)) ≠ 0 := by
      intro hzero
      simp only [readEntry, hzero, ite_true] at heq
      cases heq
    refine ⟨by omega, ?_⟩
    have hc : Vector.ofFn (fun node : cache.NodeId => heap (slot * (cache.nodes.size + 1) + 1 + node.val)) = capacity := by
      exact CapacityBits.Entry.vector.inj (by simpa only [readEntry, hz, ite_false] using heq)
    intro node
    have hh := congrArg (fun value : IndexedCapacity cache => value.get node) hc
    simpa only [cache_get_ofFn] using hh

theorem toTagLast_tag (rom : ROM) (size source target : Nat)
    (hdisjoint : DisjointSlots size source target) (state : State) :
    (execute rom (toTagLast size source target) state).heap (target + size) = state.heap source := by
  rw [toTagLast, execute_base, IndexedRAM.execute_append]
  have hcopy := copyWords_value rom source (target + size) 1 (by
      intro left hl right hr
      have hlz : left = 0 := by omega
      have hrz : right = 0 := by omega
      subst left; subst right
      simpa only [Nat.add_zero] using hdisjoint 0 (Nat.zero_le size) size le_rfl)
    (IndexedRAM.execute rom (copyWords (source + 1) target size) state) 0 (by omega)
  simp only [Nat.add_zero] at hcopy
  rw [hcopy]
  exact copyWords_frame rom (source + 1) target size state source (by
    intro index hi
    simpa only [Nat.add_zero] using hdisjoint 0 (Nat.zero_le size) index (by omega))

theorem toTagLast_payload (rom : ROM) (size source target : Nat)
    (hdisjoint : DisjointSlots size source target) (state : State)
    (index : Nat) (hi : index < size) :
    (execute rom (toTagLast size source target) state).heap (target + index) =
      state.heap (source + 1 + index) := by
  rw [toTagLast, execute_base, IndexedRAM.execute_append,
    copyWords_frame rom source (target + size) 1 _ (target + index) (by intro j hj; omega)]
  exact copyWords_value rom (source + 1) target size (by
    intro left hl right hr
    simpa only [Nat.add_assoc] using hdisjoint (1 + left) (by omega) right (by omega)) state index hi

theorem toTagLast_frame (rom : ROM) (size source target : Nat) (state : State)
    (address : Nat) (hframe : ∀ index ≤ size, address ≠ target + index) :
    (execute rom (toTagLast size source target) state).heap address = state.heap address := by
  rw [toTagLast, execute_base, IndexedRAM.execute_append,
    copyWords_frame rom source (target + size) 1 _ address (by
      intro index hi
      have hz : index = 0 := by omega
      subst index
      simpa only [Nat.add_zero] using hframe size le_rfl),
    copyWords_frame rom (source + 1) target size state address (by intro index hi; exact hframe index (by omega))]

theorem toTagLast_rep (cache : IndexedNodeCache Tool) (rom : ROM) (source target : Nat)
    (hdisjoint : DisjointSlots cache.nodes.size source target) (state : State)
    (entry : IndexedEntry.FixedEntry cache) (hrep : TagFirstRep cache state.heap source entry) :
    SlotRep cache (execute rom (toTagLast cache.nodes.size source target) state).heap target entry := by
  cases entry with
  | void => exact (toTagLast_tag rom _ source target hdisjoint state).trans hrep
  | vector capacity =>
    exact ⟨(toTagLast_tag rom _ source target hdisjoint state).trans hrep.1,
      fun node => (toTagLast_payload rom _ source target hdisjoint state node.val node.isLt).trans (hrep.2 node)⟩

theorem toTagFirst_length (size source target : Nat) : (toTagFirst size source target).length = 4 * (size + 1) := by
  simp only [toTagFirst, List.length_map, List.length_append, copyWords_length]
  omega

theorem toTagLast_length (size source target : Nat) : (toTagLast size source target).length = 4 * (size + 1) := by
  simp only [toTagLast, List.length_map, List.length_append, copyWords_length]
  omega

theorem toTagFirst_trace_length (size source target : Nat) :
    (trace (toTagFirst size source target)).length = 38 * (size + 1) := by
  simp only [toTagFirst, trace_base_length, primitiveTrace_append, List.length_append, copyWords_trace_length]
  omega

theorem toTagLast_trace_length (size source target : Nat) :
    (trace (toTagLast size source target)).length = 38 * (size + 1) := by
  simp only [toTagLast, trace_base_length, primitiveTrace_append, List.length_append, copyWords_trace_length]
  omega

theorem copyBlock_prefix_heap (rom : ROM) (source target index count : Nat)
    (hc : count < 4) (state : State) :
    (IndexedRAM.execute rom ((copyBlock source target index).take count) state).heap = state.heap := by
  interval_cases count <;> rfl

theorem copyBlock_capacity (q words source target index : Nat) (rom : ROM)
    (hsource : source + index < words) (state : State)
    (hcapacity : CapacityPrefixBounded q words state.heap) :
    CapacityPrefixBounded q words
      (IndexedRAM.execute rom (copyBlock source target index) state).heap := by
  intro address ha
  rw [IndexedCellRAM.execute_copyBlock_heap]
  by_cases heq : address = target + index
  · rw [heq, Function.update_self]
    exact hcapacity _ hsource
  · rw [Function.update_of_ne heq]
    exact hcapacity address ha

theorem copyIndices_prefix_capacity (q words source target : Nat) (rom : ROM) (indices : List Nat)
    (hsource : ∀ index ∈ indices, source + index < words) (state : State)
    (hcapacity : CapacityPrefixBounded q words state.heap) (count : Nat)
    (hc : count ≤ (copyIndices source target indices).length) :
    CapacityPrefixBounded q words
      (IndexedRAM.execute rom ((copyIndices source target indices).take count) state).heap := by
  induction indices generalizing state count with
  | nil => simpa only [copyIndices, List.flatMap_nil, List.take_nil, IndexedRAM.execute] using hcapacity
  | cons index later ih =>
    have hlen : (copyBlock source target index).length = 4 := rfl
    rw [copyIndices, List.flatMap_cons] at hc ⊢
    by_cases hsmall : count < 4
    · rw [List.take_append_of_le_length (by rw [hlen]; omega),
        copyBlock_prefix_heap rom source target index count hsmall state]
      exact hcapacity
    · obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le (show 4 ≤ count by omega)
      rw [heq, List.take_append, List.take_of_length_le (by rw [hlen]; omega), hlen,
        Nat.add_sub_cancel_left, IndexedRAM.execute_append]
      apply ih (fun node hn => hsource node (List.mem_cons_of_mem _ hn)) _
        (copyBlock_capacity q words source target index rom (hsource index List.mem_cons_self) state hcapacity) extra
      rw [List.length_append, hlen] at hc
      simpa only [copyIndices] using (show extra ≤ (List.flatMap (copyBlock source target) later).length by omega)

theorem copyWords_capacityThroughout (q words source target size : Nat) (rom : PhysicalROM)
    (hsource : source + size ≤ words) (state : State)
    (hcapacity : CapacityPrefixBounded q words state.heap) :
    CapacityThroughout q words rom ((copyWords source target size).map Op.base) state := by
  intro count hc
  rw [← List.map_take, execute_base]
  exact copyIndices_prefix_capacity q words source target rom.semantic (List.range size)
    (by intro index hi; have := List.mem_range.mp hi; omega) state hcapacity count
    (by simpa only [List.length_map, copyWords] using hc)

theorem toTagFirst_capacityThroughout (q words size source target : Nat) (rom : PhysicalROM)
    (hsource : source + size < words) (state : State)
    (hcapacity : CapacityPrefixBounded q words state.heap) :
    CapacityThroughout q words rom (toTagFirst size source target) state := by
  rw [toTagFirst, List.map_append]
  have hl := copyWords_capacityThroughout q words source (target + 1) size rom (by omega) state hcapacity
  apply UniformFreeTableSafety.capacityThroughout_append q words rom _ _ state hl
  apply copyWords_capacityThroughout q words (source + size) target 1 rom (by omega)
  simpa only [List.take_length] using hl _ le_rfl

theorem toTagLast_capacityThroughout (q words size source target : Nat) (rom : PhysicalROM)
    (hsource : source + size < words) (state : State)
    (hcapacity : CapacityPrefixBounded q words state.heap) :
    CapacityThroughout q words rom (toTagLast size source target) state := by
  rw [toTagLast, List.map_append]
  have hl := copyWords_capacityThroughout q words (source + 1) target size rom (by omega) state hcapacity
  apply UniformFreeTableSafety.capacityThroughout_append q words rom _ _ state hl
  apply copyWords_capacityThroughout q words source (target + size) 1 rom (by omega)
  simpa only [List.take_length] using hl _ le_rfl

theorem toTagFirst_halts (rom : ROM) (size source target : Nat) (state : State) (hpc : state.pc = 0) :
    HaltingRuns rom (toTagFirst size source target) state (execute rom (toTagFirst size source target) state)
      (trace (toTagFirst size source target) ++ haltTrace) := execute_halts _ _ state hpc

theorem toTagLast_halts (rom : ROM) (size source target : Nat) (state : State) (hpc : state.pc = 0) :
    HaltingRuns rom (toTagLast size source target) state (execute rom (toTagLast size source target) state)
      (trace (toTagLast size source target) ++ haltTrace) := execute_halts _ _ state hpc

theorem toTagFirst_halting_trace_length (size source target : Nat) :
    (trace (toTagFirst size source target) ++ haltTrace).length = 38 * (size + 1) + 6 := by
  rw [List.length_append, toTagFirst_trace_length, haltTrace_length]

theorem toTagLast_halting_trace_length (size source target : Nat) :
    (trace (toTagLast size source target) ++ haltTrace).length = 38 * (size + 1) + 6 := by
  rw [List.length_append, toTagLast_trace_length, haltTrace_length]

theorem toTagFirst_code_length (size source target : Nat) :
    (haltingWords (toTagFirst size source target)).length = 20 * (size + 1) + 5 := by
  rw [haltingWords_length, toTagFirst_length]
  omega

theorem toTagLast_code_length (size source target : Nat) :
    (haltingWords (toTagLast size source target)).length = 20 * (size + 1) + 5 := by
  rw [haltingWords_length, toTagLast_length]
  omega

end PaperProofs.Structure.LaminarTree.PA17TagBridge001
