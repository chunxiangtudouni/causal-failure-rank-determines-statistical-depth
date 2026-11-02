module
public import PaperProofs.Structure.PA17_GivenWord_031a
public import PaperProofs.Structure.PA17_NormalizationSafety_004
public import PaperProofs.Structure.RawTreeOutputWords
import Mathlib.Tactic.IntervalCases

/-! Actual normalizer instruction-prefix register and access bounds.
Its capacity invariant is proved from raw prepared-tree geometry below;
it is not an extra algorithm-level safety oracle. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
namespace PaperProofs.Structure.LaminarTree.PA17GivenWord031b

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17QueryHeaderWord022 PA17GivenWord031a

structure InternalData (size : Nat) (rom : PhysicalROM) : Prop where
  access : 2 * size ≤ rom.internal.length
  bound : ∀ address < 2 * size, rom.semantic.read .internal address ≤ size

structure Layout (B heapWords q capWords size cap acc : Nat) : Prop where
  cap_access : capWords ≤ heapWords
  cap_bound : capWords ≤ B
  q_bound : q ≤ B
  size_bound : size ≤ B
  payload : cap + size ≤ capWords
  accumulator : acc + size + 1 ≤ capWords

theorem givenTreeROM_internal_word_le (q : Nat) (full : List (Finset (Fin q))) (value : Nat)
    (hv : value ∈ (givenTreeROM q full).internal) : value ≤ (prepareNormalization q full).indexed.nodes.size := by
  simp only [givenTreeROM, List.mem_append] at hv
  rcases hv with hp | hd
  · obtain ⟨node, _, rfl⟩ := List.mem_map.mp hp
    exact UniformNormalizationRAM.encodedNode_le _ _
  · obtain ⟨node, _, rfl⟩ := List.mem_map.mp hd
    exact RawTreeOutputWords.prepared_child_size_le q full node

theorem givenTreeROM_internalData (q : Nat) (full : List (Finset (Fin q))) :
    InternalData (prepareNormalization q full).indexed.nodes.size (givenTreeROM q full) := by
  have hlen : (givenTreeROM q full).internal.length = 2 * (prepareNormalization q full).indexed.nodes.size := by
    simp only [givenTreeROM, List.length_append, List.length_map, List.length_finRange]
    omega
  refine ⟨by rw [hlen], ?_⟩
  intro address ha
  apply givenTreeROM_internal_word_le q full
  change (givenTreeROM q full).internal.getD address 0 ∈ _
  rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact ha)]
  exact List.getElem_mem _

theorem queryROM_internalData (q : Nat) (full : List (Finset (Fin q))) (stage : Nat) (used : Finset (Fin q)) :
    InternalData (prepareNormalization q full).indexed.nodes.size (queryROM q full stage used) := by
  have hd := givenTreeROM_internalData q full
  exact ⟨hd.access, hd.bound⟩

theorem updatedValue_le (q capWords size cap acc node : Nat) (rom : ROM) (state : State)
    (ha : cap + node < capWords) (hc : CapacityPrefixBounded q capWords state.heap) :
    UniformNormalizationRAM.updatedValue rom size cap acc node state ≤ q := by
  unfold UniformNormalizationRAM.updatedValue
  split_ifs
  · exact hc _ ha
  · exact (Nat.min_le_left _ _).trans (hc _ ha)

theorem updateNode_numeric (B heapWords q capWords size cap acc node : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q capWords size cap acc) (hd : InternalData size rom) (hn : node < size)
    (state : State) (hi : RegistersLE (2 * B) state) (hc : CapacityPrefixBounded q capWords state.heap) :
    NumericSafe (2 * B) heapWords rom (UniformNormalizationRAM.updateNode size cap acc node) state := by
  have hpa : cap + node < capWords := by have := hl.payload; omega
  have haa : acc + node + 1 < capWords := by have := hl.accumulator; omega
  have hp := hc _ hpa
  have hac := hc _ haa
  have hq := hl.q_bound
  have hs := hl.size_bound
  have hcBound := hl.cap_bound
  have hcAccess := hl.cap_access
  have hdword := hd.bound (size + node) (by omega)
  have hdaccess : size + node < rom.internal.length := by have := hd.access; omega
  have hm := (Nat.min_le_left (state.heap (cap + node)) (state.heap (acc + node + 1))).trans hp
  constructor
  · intro count hcount register
    have hr := hi register
    change count ≤ 9 at hcount
    interval_cases count <;> cases register <;>
      simp [UniformNormalizationRAM.updateNode, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals (try split_ifs)
    all_goals omega
  · intro count hcount
    change count < 9 at hcount
    interval_cases count <;>
      simp [UniformNormalizationRAM.updateNode, IndexedClosureRAM.execute, Op.execute, Instruction.execute,
        AccessFits, PhysicalROM.words]
    all_goals omega

theorem pushParent_numeric (B heapWords q capWords size cap acc node : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q capWords size cap acc) (hd : InternalData size rom) (hn : node < size)
    (state : State) (hi : RegistersLE (2 * B) state) (hc : CapacityPrefixBounded q capWords state.heap)
    (hfresh : state.register .fresh ≤ q) :
    NumericSafe (2 * B) heapWords rom (UniformNormalizationRAM.pushParent acc node) state := by
  have hq := hl.q_bound
  have hs := hl.size_bound
  have hcBound := hl.cap_bound
  have hcAccess := hl.cap_access
  have hdword := hd.bound node (by omega)
  have hdaccess : node < rom.internal.length := by have := hd.access; omega
  have haa : acc + rom.semantic.read .internal node < capWords := by have := hl.accumulator; omega
  have ha0 : acc ≤ B := by have := hl.accumulator; omega
  have hac := hc _ haa
  constructor
  · intro count hcount register
    have hr := hi register
    change count ≤ 7 at hcount
    interval_cases count <;> cases register <;>
      simp [UniformNormalizationRAM.pushParent, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hcount
    change count < 7 at hcount
    interval_cases count <;>
      simp [UniformNormalizationRAM.pushParent, IndexedClosureRAM.execute, Op.execute, Instruction.execute,
        AccessFits, PhysicalROM.words]
    all_goals omega

theorem nodeBlock_numeric (B heapWords q capWords size cap acc node : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q capWords size cap acc) (hd : InternalData size rom) (hn : node < size)
    (state : State) (hi : RegistersLE (2 * B) state) (hc : CapacityPrefixBounded q capWords state.heap) :
    NumericSafe (2 * B) heapWords rom (UniformNormalizationRAM.nodeBlock size cap acc node) state := by
  have hu := updateNode_numeric B heapWords q capWords size cap acc node rom hl hd hn state hi hc
  have hv := updatedValue_le q capWords size cap acc node rom.semantic state (by have := hl.payload; omega) hc
  have hafter : CapacityPrefixBounded q capWords
      (execute rom.semantic (UniformNormalizationRAM.updateNode size cap acc node) state).heap := by
    rw [UniformNormalizationRAM.execute_updateNode_heap]
    exact PA17NormalizationSafety004.bounded_update q capWords state.heap hc _ _ hv
  apply NumericSafe.append _ _ rom _ _ state hu
  apply pushParent_numeric B heapWords q capWords size cap acc node rom hl hd hn _ (hu.final _ _ _ _ _) hafter
  rw [UniformNormalizationRAM.execute_updateNode_fresh]
  exact hv

theorem program_numeric_of_capacity (B heapWords q capWords size cap acc : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q capWords size cap acc) (hd : InternalData size rom)
    (state : State) (hi : RegistersLE (2 * B) state)
    (hc : CapacityThroughout q capWords rom (UniformNormalizationRAM.program size cap acc) state) :
    NumericSafe (2 * B) heapWords rom (UniformNormalizationRAM.program size cap acc) state := by
  have hclear := clearWords_numeric B heapWords acc (size + 1) rom
    (hl.accumulator.trans hl.cap_access) (hl.accumulator.trans hl.cap_bound) state hi
  rw [UniformNormalizationRAM.program] at hc ⊢
  apply NumericSafe.append _ _ rom _ _ state hclear
  apply numeric_flatMap_of_capacity (2 * B) heapWords q capWords rom
    (UniformNormalizationRAM.nodeBlock size cap acc) (List.range size) _ _ (hclear.final _ _ _ _ _)
    (capacityThroughout_right q capWords rom _ _ state hc)
  intro node hm before hregister hcapacity
  exact nodeBlock_numeric B heapWords q capWords size cap acc node rom hl hd (List.mem_range.mp hm) before hregister hcapacity

theorem prepared_program_numeric (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (B heapWords capWords cap acc : Nat)
    (hl : Layout B heapWords q capWords (prepareNormalization q full).indexed.nodes.size cap acc)
    (hdisjoint : UniformNormalizationRAM.Disjoint (prepareNormalization q full).indexed.nodes.size cap acc)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (hcard : ∀ node : (prepareNormalization q full).indexed.NodeId,
      capacity.get node ≤ ((prepareNormalization q full).indexed.decode node).card)
    (state : State) (hi : RegistersLE (2 * B) state) (hbound : CapacityPrefixBounded q capWords state.heap)
    (hagrees : ∀ node : (prepareNormalization q full).indexed.NodeId, state.heap (cap + node.val) = capacity.get node) :
    NumericSafe (2 * B) heapWords (givenTreeROM q full)
      (UniformNormalizationRAM.program (prepareNormalization q full).indexed.nodes.size cap acc) state := by
  apply program_numeric_of_capacity B heapWords q capWords _ cap acc (givenTreeROM q full) hl (givenTreeROM_internalData q full) state hi
  exact PA17NormalizationSafety004.prepared_program_capacityThroughout q full hq hlaminar capWords cap acc hdisjoint capacity hcard state hbound hagrees

end PaperProofs.Structure.LaminarTree.PA17GivenWord031b
