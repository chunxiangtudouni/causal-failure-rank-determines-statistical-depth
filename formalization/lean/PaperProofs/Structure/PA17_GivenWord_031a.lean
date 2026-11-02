module
public import PaperProofs.Structure.PA17_UniformCell_002
public import PaperProofs.Structure.PA17_QueryHeaderWord_022a
public import PaperProofs.Structure.PA17_WordBounds_023
import Mathlib.Tactic.IntervalCases

/-! Reusable actual-instruction numeric/access bounds for the two given-tree
builders. The proofs bound only values actually read, including VOID payloads. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
namespace PaperProofs.Structure.LaminarTree.PA17GivenWord031a

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17QueryHeaderWord022

def AddressBound (B heapWords address : Nat) : Prop := address < heapWords ∧ address ≤ B

theorem NumericSafe.nil (B heapWords : Nat) (rom : PhysicalROM) (state : State) (hi : RegistersLE B state) :
    NumericSafe B heapWords rom [] state := by
  constructor
  · intro count _
    simpa only [List.take_nil, IndexedClosureRAM.execute] using hi
  · intro count hc
    change count < 0 at hc
    omega

theorem constantBlock_numeric (B heapWords target value : Nat) (rom : PhysicalROM)
    (ha : AddressBound B heapWords target) (hv : value ≤ 2 * B)
    (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom ((IndexedCellRAM.constantBlock target value).map Op.base) state := by
  have haddr := ha.1
  have hbound := ha.2
  constructor
  · intro count hc register
    have hr := hi register
    change count ≤ 3 at hc
    interval_cases count <;> cases register <;>
      simp [IndexedCellRAM.constantBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hc
    change count < 3 at hc
    interval_cases count <;>
      simp [IndexedCellRAM.constantBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, haddr]

theorem clearBlock_numeric (B heapWords target : Nat) (rom : PhysicalROM)
    (ha : AddressBound B heapWords target) (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (UniformNormalizationRAM.clearBlock target) state := by
  have haddr := ha.1
  have hbound := ha.2
  constructor
  · intro count hc register
    have hr := hi register
    change count ≤ 3 at hc
    interval_cases count <;> cases register <;>
      simp [UniformNormalizationRAM.clearBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hc
    change count < 3 at hc
    interval_cases count <;>
      simp [UniformNormalizationRAM.clearBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, haddr]

theorem clearIndices_numeric (B heapWords base : Nat) (rom : PhysicalROM) (indices : List Nat)
    (ha : ∀ index ∈ indices, AddressBound B heapWords (base + index))
    (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (indices.flatMap (fun index => UniformNormalizationRAM.clearBlock (base + index))) state := by
  induction indices generalizing state with
  | nil => exact NumericSafe.nil _ _ rom state hi
  | cons head later ih =>
    rw [List.flatMap_cons]
    have hh := clearBlock_numeric B heapWords (base + head) rom (ha head List.mem_cons_self) state hi
    exact NumericSafe.append _ _ rom _ _ state hh
      (ih (fun index hm => ha index (List.mem_cons_of_mem _ hm)) _ (hh.final _ _ _ _ _))

theorem clearWords_numeric (B heapWords base count : Nat) (rom : PhysicalROM)
    (ha : base + count ≤ heapWords) (hb : base + count ≤ B)
    (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (UniformNormalizationRAM.clearWords base count) state := by
  apply clearIndices_numeric B heapWords base rom (List.range count) _ state hi
  intro index hm
  have hh := List.mem_range.mp hm
  exact ⟨by omega, by omega⟩

theorem copyBlock_numeric (B heapWords source target index : Nat) (rom : PhysicalROM)
    (hs : AddressBound B heapWords (source + index)) (ht : AddressBound B heapWords (target + index))
    (state : State) (hi : RegistersLE (2 * B) state) (hv : state.heap (source + index) ≤ 2 * B) :
    NumericSafe (2 * B) heapWords rom ((IndexedCellRAM.copyBlock source target index).map Op.base) state := by
  have hsaddr := hs.1
  have hsbound := hs.2
  have htaddr := ht.1
  have htbound := ht.2
  constructor
  · intro count hc register
    have hr := hi register
    change count ≤ 4 at hc
    interval_cases count <;> cases register <;>
      simp [IndexedCellRAM.copyBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hc
    change count < 4 at hc
    interval_cases count <;>
      simp [IndexedCellRAM.copyBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, hsaddr, htaddr]

theorem copyIndices_numeric (B heapWords size source target : Nat) (rom : PhysicalROM) (indices : List Nat)
    (hindices : ∀ index ∈ indices, index < size)
    (hs : ∀ index < size, AddressBound B heapWords (source + index))
    (ht : ∀ index < size, AddressBound B heapWords (target + index))
    (state : State) (hi : RegistersLE (2 * B) state) (hv : ∀ index < size, state.heap (source + index) ≤ 2 * B) :
    NumericSafe (2 * B) heapWords rom ((IndexedCellRAM.copyIndices source target indices).map Op.base) state := by
  induction indices generalizing state with
  | nil => exact NumericSafe.nil _ _ rom state hi
  | cons head later ih =>
    rw [IndexedCellRAM.copyIndices, List.flatMap_cons, List.map_append]
    have hhead := hindices head List.mem_cons_self
    have hh := copyBlock_numeric B heapWords source target head rom (hs head hhead) (ht head hhead) state hi (hv head hhead)
    apply NumericSafe.append _ _ rom _ _ state hh
    apply ih (fun index hm => hindices index (List.mem_cons_of_mem _ hm)) _ (hh.final _ _ _ _ _)
    intro index hindex
    rw [execute_base, IndexedCellRAM.execute_copyBlock_heap]
    by_cases heq : source + index = target + head
    · rw [heq, Function.update_self]; exact hv head hhead
    · rw [Function.update_of_ne heq]; exact hv index hindex

theorem copyWords_numeric (B heapWords size source target : Nat) (rom : PhysicalROM)
    (hsheap : source + size ≤ heapWords) (hsbound : source + size ≤ B)
    (htheap : target + size ≤ heapWords) (htbound : target + size ≤ B)
    (state : State) (hi : RegistersLE (2 * B) state) (hv : ∀ index < size, state.heap (source + index) ≤ 2 * B) :
    NumericSafe (2 * B) heapWords rom ((IndexedCellRAM.copyWords source target size).map Op.base) state := by
  exact copyIndices_numeric B heapWords size source target rom (List.range size) (fun _ hm => List.mem_range.mp hm)
    (by intro index hi; exact ⟨by omega, by omega⟩) (by intro index hi; exact ⟨by omega, by omega⟩) state hi hv

theorem minimumBlock_numeric (B heapWords work good node : Nat) (rom : PhysicalROM)
    (hw : AddressBound B heapWords (work + node)) (hg : AddressBound B heapWords (good + 1 + node))
    (state : State) (hi : RegistersLE (2 * B) state)
    (hv : state.heap (work + node) ≤ 2 * B) (hgv : state.heap (good + 1 + node) ≤ 2 * B) :
    NumericSafe (2 * B) heapWords rom (PA17UniformCell002.minimumBlock work good node) state := by
  have hwa := hw.1
  have hwb := hw.2
  have hga := hg.1
  have hgb := hg.2
  constructor
  · intro count hc register
    have hr := hi register
    have hmin := (Nat.min_le_left (state.heap (work + node)) (state.heap (good + 1 + node))).trans hv
    change count ≤ 6 at hc
    interval_cases count <;> cases register <;>
      simp [PA17UniformCell002.minimumBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hc
    change count < 6 at hc
    interval_cases count <;>
      simp [PA17UniformCell002.minimumBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, hwa, hga]

theorem tagTail_numeric (B heapWords size work good : Nat) (rom : PhysicalROM)
    (hw : AddressBound B heapWords (work + size)) (hg : AddressBound B heapWords good)
    (state : State) (hi : RegistersLE (2 * B) state)
    (hv : state.heap (work + size) ≤ 2 * B) (hgv : state.heap good ≤ 2 * B) :
    NumericSafe (2 * B) heapWords rom (PA17UniformCell002.tagTail size work good) state := by
  have hwa := hw.1
  have hwb := hw.2
  have hga := hg.1
  have hgb := hg.2
  constructor
  · intro count hc register
    have hr := hi register
    have hmin := (Nat.min_le_right (state.heap good) (state.heap (work + size))).trans hv
    change count ≤ 6 at hc
    interval_cases count <;> cases register <;>
      simp [PA17UniformCell002.tagTail, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hc
    change count < 6 at hc
    interval_cases count <;>
      simp [PA17UniformCell002.tagTail, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, hwa, hga]

theorem capacityThroughout_left (q words : Nat) (rom : PhysicalROM) (left right : List Op) (state : State)
    (hc : CapacityThroughout q words rom (left ++ right) state) : CapacityThroughout q words rom left state := by
  intro count hn
  have hh := hc count (by rw [List.length_append]; omega)
  rw [List.take_append_of_le_length hn] at hh
  exact hh

theorem capacityThroughout_right (q words : Nat) (rom : PhysicalROM) (left right : List Op) (state : State)
    (hc : CapacityThroughout q words rom (left ++ right) state) :
    CapacityThroughout q words rom right (execute rom.semantic left state) := by
  intro count hn
  have hh := hc (left.length + count) (by rw [List.length_append]; omega)
  rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left, IndexedClosureRAM.execute_append] at hh
  exact hh

theorem numeric_flatMap_of_capacity {α : Type*} (B heapWords q capWords : Nat) (rom : PhysicalROM)
    (blocks : α → List Op) (entries : List α)
    (hblock : ∀ entry ∈ entries, ∀ state : State, RegistersLE B state →
      CapacityPrefixBounded q capWords state.heap → NumericSafe B heapWords rom (blocks entry) state)
    (state : State) (hi : RegistersLE B state)
    (hc : CapacityThroughout q capWords rom (entries.flatMap blocks) state) :
    NumericSafe B heapWords rom (entries.flatMap blocks) state := by
  induction entries generalizing state with
  | nil => exact NumericSafe.nil _ _ rom state hi
  | cons head later ih =>
    rw [List.flatMap_cons] at hc ⊢
    have hh := hblock head List.mem_cons_self state hi (hc 0 (Nat.zero_le _))
    apply NumericSafe.append _ _ rom _ _ state hh
    apply ih (fun entry he => hblock entry (List.mem_cons_of_mem _ he)) _ (hh.final _ _ _ _ _)
    exact capacityThroughout_right q capWords rom _ _ state hc

end PaperProofs.Structure.LaminarTree.PA17GivenWord031a
