module
public import PaperProofs.Structure.PA17_GivenWord_031b
import Mathlib.Tactic.IntervalCases

/-! Actual heap-parent ancestor pass: all pointers are proved to stay inside
the allocated regions, including the inactive encoded-node0 iteration. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
namespace PaperProofs.Structure.LaminarTree.PA17GivenWord031c

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17QueryHeaderWord022 PA17GivenWord031a

structure Layout (B heapWords q capWords size work parents stage : Nat) : Prop where
  cap_access : capWords ≤ heapWords
  cap_bound : capWords ≤ B
  q_bound : q ≤ B
  size_bound : size ≤ B
  size_pos : 0 < size
  work_region : work + size < capWords
  parent_access : parents + size < heapWords
  parent_bound : parents + size ≤ B
  stage_access : stage < heapWords
  stage_bound : stage ≤ B
  disjoint : ∀ index < size, ∀ encoded ≤ size, work + index ≠ parents + encoded

theorem ancestor_index_lt (size : Nat) (state : State) (hs : 0 < size)
    (ha : state.register .address ≤ size) (ht : state.register .total = 1) :
    state.register .address - state.register .total < size := by omega

theorem ancestorBlock_numeric (B heapWords q capWords size work parents stage : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q capWords size work parents stage)
    (state : State) (hi : RegistersLE (2 * B) state) (hc : CapacityPrefixBounded q capWords state.heap)
    (ha : state.register .address ≤ size) (ht : state.register .total = 1)
    (hp : ∀ encoded ≤ size, state.heap (parents + encoded) ≤ size) :
    NumericSafe (2 * B) heapWords rom (PA17HeapAncestors001.ancestorBlock work parents) state := by
  have hindex := ancestor_index_lt size state hl.size_pos ha ht
  have hw : work + (state.register .address - 1) < capWords := by have := hl.work_region; omega
  have hvalue := hc _ hw
  have hparent := hp (state.register .address) ha
  have hsep : parents + state.register .address ≠ work + (state.register .address - 1) :=
    (hl.disjoint _ (by omega) _ ha).symm
  have hq := hl.q_bound
  have hs := hl.size_bound
  have hcb := hl.cap_bound
  have hch := hl.cap_access
  have hpb := hl.parent_bound
  have hph := hl.parent_access
  have hone : 1 ≤ B := by have := hl.size_pos; omega
  constructor
  · intro count hcount register
    have hr := hi register
    have hf := hi .flag
    change count ≤ 13 at hcount
    interval_cases count <;> cases register <;>
      simp [PA17HeapAncestors001.ancestorBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute, ht,
        Function.update_of_ne hsep]
    all_goals (try split_ifs)
    all_goals omega
  · intro count hcount
    change count < 13 at hcount
    interval_cases count <;>
      simp [PA17HeapAncestors001.ancestorBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute,
        ht, AccessFits]
    all_goals omega

theorem ancestorBlock_parentBound (B heapWords q capWords size work parents stage : Nat) (rom : ROM)
    (hl : Layout B heapWords q capWords size work parents stage)
    (state : State) (ha : state.register .address ≤ size) (ht : state.register .total = 1)
    (hp : ∀ encoded ≤ size, state.heap (parents + encoded) ≤ size) :
    ∀ encoded ≤ size,
      (execute rom (PA17HeapAncestors001.ancestorBlock work parents) state).heap (parents + encoded) ≤ size := by
  intro encoded he
  rw [PA17HeapAncestors001.ancestorBlock_frame rom work parents state _
    ((hl.disjoint _ (ancestor_index_lt size state hl.size_pos ha ht) encoded he).symm)]
  exact hp encoded he

theorem ancestorBlock_addressBound (B heapWords q capWords size work parents stage : Nat) (rom : ROM)
    (hl : Layout B heapWords q capWords size work parents stage)
    (state : State) (ha : state.register .address ≤ size) (ht : state.register .total = 1)
    (hp : ∀ encoded ≤ size, state.heap (parents + encoded) ≤ size) :
    (execute rom (PA17HeapAncestors001.ancestorBlock work parents) state).register .address ≤ size := by
  rw [PA17HeapAncestors001.ancestorBlock_parent]
  exact ancestorBlock_parentBound B heapWords q capWords size work parents stage rom hl state ha ht hp _ ha

theorem ancestorLoop_numeric (B heapWords q capWords size work parents stage fuel : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q capWords size work parents stage)
    (state : State) (hi : RegistersLE (2 * B) state) (hc : CapacityPrefixBounded q capWords state.heap)
    (ha : state.register .address ≤ size) (ht : state.register .total = 1)
    (hp : ∀ encoded ≤ size, state.heap (parents + encoded) ≤ size) :
    NumericSafe (2 * B) heapWords rom (PA17HeapAncestors001.ancestorLoop work parents fuel) state := by
  induction fuel generalizing state with
  | zero => exact NumericSafe.nil _ _ rom state hi
  | succ fuel ih =>
    rw [PA17HeapAncestors001.ancestorLoop, List.replicate_succ, List.flatten_cons]
    have hh := ancestorBlock_numeric B heapWords q capWords size work parents stage rom hl state hi hc ha ht hp
    apply NumericSafe.append _ _ rom _ _ state hh
    apply ih _ (hh.final _ _ _ _ _) _
      (ancestorBlock_addressBound B heapWords q capWords size work parents stage rom.semantic hl state ha ht hp)
      (by rw [PA17HeapAncestors001.ancestorBlock_one]; exact ht)
      (ancestorBlock_parentBound B heapWords q capWords size work parents stage rom.semantic hl state ha ht hp)
    intro address haddress
    exact (PA17HeapAncestors001.ancestorBlock_heap_le rom.semantic work parents state address).trans (hc address haddress)

theorem extensionInit_numeric (B heapWords q capWords size work parents stage : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q capWords size work parents stage)
    (state : State) (hi : RegistersLE (2 * B) state) (hc : CapacityPrefixBounded q capWords state.heap)
    (hs : state.heap stage ≤ size) :
    NumericSafe (2 * B) heapWords rom (PA17HeapAncestors001.extensionInit size work stage) state := by
  have hw := hc _ hl.work_region
  have hq := hl.q_bound
  have hsize := hl.size_bound
  have hcb := hl.cap_bound
  have hca := hl.cap_access
  have hsb := hl.stage_bound
  have hsa := hl.stage_access
  have hwork := hl.work_region
  have hone : 1 ≤ B := by have := hl.size_pos; omega
  constructor
  · intro count hcount register
    have hr := hi register
    change count ≤ 7 at hcount
    interval_cases count <;> cases register <;>
      simp [PA17HeapAncestors001.extensionInit, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals (try split_ifs)
    all_goals omega
  · intro count hcount
    change count < 7 at hcount
    interval_cases count <;>
      simp [PA17HeapAncestors001.extensionInit, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits]
    all_goals omega

theorem extensionTail_numeric (B heapWords q capWords size work parents stage : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q capWords size work parents stage)
    (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (PA17HeapAncestors001.extensionTail size work) state := by
  have hcb := hl.cap_bound
  have hca := hl.cap_access
  have hwork := hl.work_region
  constructor
  · intro count hcount register
    have hr := hi register
    change count ≤ 2 at hcount
    interval_cases count <;> cases register <;>
      simp [PA17HeapAncestors001.extensionTail, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hcount
    change count < 2 at hcount
    interval_cases count <;>
      simp [PA17HeapAncestors001.extensionTail, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits]
    all_goals omega

theorem extensionProgram_numeric (B heapWords q capWords size work parents stage : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q capWords size work parents stage)
    (state : State) (hi : RegistersLE (2 * B) state) (hc : CapacityPrefixBounded q capWords state.heap)
    (hs : state.heap stage ≤ size) (hp : ∀ encoded ≤ size, state.heap (parents + encoded) ≤ size) :
    NumericSafe (2 * B) heapWords rom (PA17HeapAncestors001.extensionProgram size work parents stage) state := by
  have hinit := extensionInit_numeric B heapWords q capWords size work parents stage rom hl state hi hc hs
  let start := execute rom.semantic (PA17HeapAncestors001.extensionInit size work stage) state
  have hstart := PA17HeapAncestors001.extensionInit_registers rom.semantic size work stage state
  have hloop := ancestorLoop_numeric B heapWords q capWords size work parents stage size rom hl start
    (hinit.final _ _ _ _ _) hc (by rw [hstart.1]; exact hs) hstart.2.1 hp
  have htail := extensionTail_numeric B heapWords q capWords size work parents stage rom hl _ (hloop.final _ _ _ _ _)
  rw [PA17HeapAncestors001.extensionProgram]
  apply NumericSafe.append _ _ rom _ _ state (NumericSafe.append _ _ rom _ _ state hinit hloop)
  rw [IndexedClosureRAM.execute_append]
  exact htail

end PaperProofs.Structure.LaminarTree.PA17GivenWord031c
