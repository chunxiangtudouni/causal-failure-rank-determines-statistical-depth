module

public import PaperProofs.Structure.PA17_QuerySelectionSafety_020
public import PaperProofs.Structure.PA17_QueryHeaderWord_022a
public import PaperProofs.Structure.PA17_GivenWord_031a
import Mathlib.Tactic.IntervalCases

/-! Actual selector prefix numeric/access certificates. Candidate scratch is
cleared and bounded by this run; unrelated heap/scratch values are unrestricted.
The source row uses the original q-bound, including arbitrary VOID payloads. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PA17QuerySelectWord029

open IndexedRAM IndexedClosureRAM AlgorithmClaims
open PA17QueryHeaderWord022 PA17QuerySelection010b

structure Layout (B heapWords size q countBase leafBase header rowBase childBase : Nat) : Prop where
  scratch_le : childBase + size + 3 ≤ B
  scratch_access : childBase + size + 3 ≤ heapWords
  q_le : q + 1 ≤ B
  size_pos : 0 < size
  counts : countBase + size ≤ childBase
  labels : leafBase + size ≤ childBase
  header : header + 8 ≤ childBase
  row : rowBase + (q + 2) * (size + 1) ≤ childBase

structure ParentData (size : Nat) (rom : PhysicalROM) : Prop where
  access : size ≤ rom.internal.length
  value : ∀ node < size, rom.semantic.read .internal node ≤ size

theorem queryROM_parentData (q : Nat) (full : List (Finset (Fin q))) (queryStage : Nat) (used : Finset (Fin q)) :
    ParentData (prepareNormalization q full).indexed.nodes.size (queryROM q full queryStage used) := by
  constructor
  · simp only [queryROM, givenTreeROM, List.length_append, List.length_map, List.length_finRange]
    omega
  · intro node hn
    change (givenTreeROM q full).semantic.read .internal node ≤ (prepareNormalization q full).indexed.nodes.size
    exact (UniformNormalizationRAM.givenTreeROM_parent q full ⟨node, hn⟩).trans_le
      (UniformNormalizationRAM.encodedNode_le (prepareNormalization q full).indexed _)

structure ReadValuesBound (size q countBase leafBase header rowBase : Nat) (heap : Nat → Nat) : Prop where
  row_pointer : heap header = rowBase
  budget : heap (header + 6) ≤ q + 1
  node : heap (header + 1) ≤ size
  enabled : heap (header + 7) ≤ 1
  counts : ∀ node < size, heap (countBase + node) ≤ q
  labels : ∀ node < size, heap (leafBase + node) ≤ q
  row : ∀ budget : Fin (q + 2), ∀ index ≤ size,
    heap (rowBase + budget.val * (size + 1) + index) ≤ q

def selectedPayload (size header : Nat) (heap : Nat → Nat) : Nat :=
  heap header + (size + 1) * heap (header + 6) + 1

def CandidatesLE (size childBase : Nat) (heap : Nat → Nat) : Prop :=
  ∀ encoded ≤ size, heap (childBase + encoded) ≤ size

structure PushValues (size q countBase payloadPointer payloadBase : Nat) (heap : Nat → Nat) : Prop where
  pointer : heap payloadPointer = payloadBase
  counts : ∀ node < size, heap (countBase + node) ≤ q
  payload : ∀ node < size, heap (payloadBase + node) ≤ q

theorem sourceWord_lt (size q rowBase childBase : Nat)
    (hrow : rowBase + (q + 2) * (size + 1) ≤ childBase)
    (budget : Fin (q + 2)) (index : Nat) (hi : index ≤ size) :
    rowBase + budget.val * (size + 1) + index < childBase := by
  have hm := Nat.mul_le_mul_right (size + 1) (show budget.val + 1 ≤ q + 2 from budget.isLt)
  rw [Nat.add_mul, Nat.one_mul] at hm
  omega

theorem ReadValuesBound.of_capacity (size q countBase leafBase header rowBase words : Nat)
    (heap : Nat → Nat) (hrow : heap header = rowBase) (hbudget : heap (header + 6) ≤ q + 1)
    (hnode : heap (header + 1) ≤ size) (henabled : heap (header + 7) ≤ 1)
    (hcounts : ∀ node < size, heap (countBase + node) ≤ q)
    (hlabels : ∀ node < size, heap (leafBase + node) ≤ q)
    (htable : rowBase + (q + 2) * (size + 1) ≤ words)
    (hcapacity : CapacityPrefixBounded q words heap) :
    ReadValuesBound size q countBase leafBase header rowBase heap := by
  refine ⟨hrow, hbudget, hnode, henabled, hcounts, hlabels, ?_⟩
  intro budget index hi
  exact hcapacity _ (sourceWord_lt size q rowBase words htable budget index hi)

theorem ReadValuesBound.transfer (B heapWords size q countBase leafBase header rowBase childBase : Nat)
    (hl : Layout B heapWords size q countBase leafBase header rowBase childBase)
    (heap heap' : Nat → Nat) (hv : ReadValuesBound size q countBase leafBase header rowBase heap)
    (hf : ∀ address < childBase, heap' address = heap address) :
    ReadValuesBound size q countBase leafBase header rowBase heap' := by
  constructor
  · rw [hf header (by have := hl.header; omega)]; exact hv.row_pointer
  · rw [hf (header + 6) (by have := hl.header; omega)]; exact hv.budget
  · rw [hf (header + 1) (by have := hl.header; omega)]; exact hv.node
  · rw [hf (header + 7) (by have := hl.header; omega)]; exact hv.enabled
  · intro node hn
    rw [hf _ (by have := hl.counts; omega)]; exact hv.counts node hn
  · intro node hn
    rw [hf _ (by have := hl.labels; omega)]; exact hv.labels node hn
  · intro budget index hi
    rw [hf _ (sourceWord_lt size q rowBase childBase hl.row budget index hi)]
    exact hv.row budget index hi

theorem selectedPayload_le (B heapWords size q countBase leafBase header rowBase childBase : Nat)
    (hl : Layout B heapWords size q countBase leafBase header rowBase childBase)
    (heap : Nat → Nat) (hv : ReadValuesBound size q countBase leafBase header rowBase heap) :
    selectedPayload size header heap + size ≤ childBase := by
  have ha := sourceWord_lt size q rowBase childBase hl.row
    ⟨heap (header + 6), by have := hv.budget; omega⟩ size le_rfl
  change rowBase + heap (header + 6) * (size + 1) + size < childBase at ha
  simp only [selectedPayload, hv.row_pointer, Nat.mul_comm (size + 1)]
  omega

theorem selectedPayload_values (size q countBase leafBase header rowBase : Nat)
    (heap : Nat → Nat) (hv : ReadValuesBound size q countBase leafBase header rowBase heap)
    (node : Nat) (hn : node < size) : heap (selectedPayload size header heap + node) ≤ q := by
  have hh := hv.row ⟨heap (header + 6), by have := hv.budget; omega⟩ (1 + node) (by omega)
  simpa only [selectedPayload, hv.row_pointer, Nat.mul_comm (size + 1), Nat.add_assoc] using hh

theorem selectedPayload_tag (size q countBase leafBase header rowBase : Nat)
    (heap : Nat → Nat) (hv : ReadValuesBound size q countBase leafBase header rowBase heap) :
    heap (selectedPayload size header heap - 1) ≤ q := by
  have hh := hv.row ⟨heap (header + 6), by have := hv.budget; omega⟩ 0 (Nat.zero_le _)
  simpa only [selectedPayload, Nat.add_sub_cancel, hv.row_pointer,
    Nat.mul_comm (size + 1), Nat.add_zero] using hh

theorem preludeStart_numeric (B heapWords size q countBase leafBase header rowBase childBase : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords size q countBase leafBase header rowBase childBase)
    (state : State) (hv : ReadValuesBound size q countBase leafBase header rowBase state.heap)
    (hr : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (preludeStart header) state := by
  have ha := selectedPayload_le B heapWords size q countBase leafBase header rowBase childBase hl state.heap hv
  have hh := hl.header
  have hB := hl.scratch_le
  have hH := hl.scratch_access
  have hq := hl.q_le
  have hb := hv.budget
  simp only [selectedPayload, hv.row_pointer] at ha
  constructor
  · intro k hk r
    have hreg := hr r
    change k ≤ 4 at hk
    interval_cases k <;> cases r <;>
      simp [preludeStart, IndexedClosureRAM.execute, Op.execute, Instruction.execute, hv.row_pointer]
    all_goals omega
  · intro k hk
    change k < 4 at hk
    interval_cases k <;> simp [preludeStart, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits]
    all_goals omega

theorem addOffset_register (rom : ROM) (fuel : Nat) (state : State) (r : Register) (hne : r ≠ .address) :
    (execute rom (addOffset fuel) state).register r = state.register r := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    rw [addOffset, List.replicate_succ, IndexedClosureRAM.execute]
    change (execute rom (addOffset fuel) (Op.execute rom (.base (.add .address .address .value)) state)).register r = _
    rw [ih]
    simp [Op.execute, Instruction.execute, hne]

theorem addOffset_numeric (bound heapWords : Nat) (rom : PhysicalROM) (fuel : Nat) (state : State)
    (hr : RegistersLE bound state)
    (hfinal : state.register .address + fuel * state.register .value ≤ bound) :
    NumericSafe bound heapWords rom (addOffset fuel) state := by
  constructor
  · intro k _ r
    have ht : (addOffset fuel).take k = addOffset (min k fuel) := by simp only [addOffset, List.take_replicate]
    rw [ht]
    by_cases heq : r = .address
    · subst r
      rw [(addOffset_effect rom.semantic _ state).2.2]
      have hm := Nat.mul_le_mul_right (state.register .value) (Nat.min_le_right k fuel)
      omega
    · rw [addOffset_register rom.semantic _ state r heq]
      exact hr r
  · intro k hk
    simp only [addOffset, List.getElem_replicate, AccessFits]

theorem preludeTail_numeric (B heapWords payloadPointer : Nat) (rom : PhysicalROM)
    (hp : payloadPointer ≤ B) (ha : payloadPointer < heapWords) (hone : 1 ≤ B)
    (state : State) (hr : RegistersLE (2 * B) state) (haddress : state.register .address + 1 ≤ B) :
    NumericSafe (2 * B) heapWords rom (preludeTail payloadPointer) state := by
  constructor
  · intro k hk r
    have hreg := hr r
    change k ≤ 4 at hk
    interval_cases k <;> cases r <;>
      simp [preludeTail, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals omega
  · intro k hk
    change k < 4 at hk
    interval_cases k <;> simp [preludeTail, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, ha]

theorem prelude_numeric (B heapWords size q countBase leafBase header rowBase childBase : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords size q countBase leafBase header rowBase childBase)
    (state : State) (hv : ReadValuesBound size q countBase leafBase header rowBase state.heap)
    (hr : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (prelude size header (childBase + size + 1)) state := by
  let started := execute rom.semantic (preludeStart header) state
  have h1 := preludeStart_numeric B heapWords size q countBase leafBase header rowBase childBase rom hl state hv hr
  have hp := selectedPayload_le B heapWords size q countBase leafBase header rowBase childBase hl state.heap hv
  have hB := hl.scratch_le
  have hH := hl.scratch_access
  have h2 := addOffset_numeric (2 * B) heapWords rom (size + 1) started (h1.final _ _ _ _ _)
    (by change state.heap header + (size + 1) * state.heap (header + 6) ≤ 2 * B
        unfold selectedPayload at hp; omega)
  have h3 := preludeTail_numeric B heapWords (childBase + size + 1) rom (by omega) (by omega) (by omega)
    (execute rom.semantic (addOffset (size + 1)) started) (h2.final _ _ _ _ _)
    (by rw [(addOffset_effect rom.semantic _ started).2.2]
        change state.heap header + (size + 1) * state.heap (header + 6) + 1 ≤ B
        unfold selectedPayload at hp; omega)
  simp only [prelude, List.append_assoc]
  exact NumericSafe.append _ _ _ _ _ _ h1 (NumericSafe.append _ _ _ _ _ _ h2 h3)

theorem clearWords_candidates (size childBase : Nat) (rom : ROM) (state : State) :
    CandidatesLE size childBase (execute rom (UniformNormalizationRAM.clearWords childBase (size + 1)) state).heap := by
  intro encoded he
  rw [UniformNormalizationRAM.clearWords,
    UniformNormalizationRAM.clearIndices_value rom childBase (List.range (size + 1)) state encoded
      (List.mem_range.mpr (by omega))]
  exact Nat.zero_le _

theorem clearWords_pushValues (size q countBase childBase payloadBase : Nat)
    (hcount : countBase + size ≤ childBase) (hpayload : payloadBase + size ≤ childBase)
    (rom : ROM) (state : State)
    (hv : PushValues size q countBase (childBase + size + 1) payloadBase state.heap) :
    PushValues size q countBase (childBase + size + 1) payloadBase
      (execute rom (UniformNormalizationRAM.clearWords childBase (size + 1)) state).heap := by
  have hf (address : Nat) (ha : ∀ index < size + 1, address ≠ childBase + index) :
      (execute rom (UniformNormalizationRAM.clearWords childBase (size + 1)) state).heap address = state.heap address := by
    apply UniformNormalizationRAM.clearIndices_frame
    intro index hi
    exact ha index (List.mem_range.mp hi)
  constructor
  · rw [hf _ (by intro index hi; omega)]; exact hv.pointer
  · intro node hn
    rw [hf _ (by intro index hi; omega)]; exact hv.counts node hn
  · intro node hn
    rw [hf _ (by intro index hi; omega)]; exact hv.payload node hn

theorem parentBlock_pushValues (size q countBase childBase payloadBase : Nat)
    (hcount : countBase + size ≤ childBase) (hpayload : payloadBase + size ≤ childBase)
    (rom : PhysicalROM) (hd : ParentData size rom) (node : Nat) (hn : node < size) (state : State)
    (hv : PushValues size q countBase (childBase + size + 1) payloadBase state.heap) :
    PushValues size q countBase (childBase + size + 1) payloadBase
      (execute rom.semantic (PA17QuerySelection010.parentBlock countBase (childBase + size + 1) childBase node) state).heap := by
  have hp := hd.value node hn
  constructor
  · rw [PA17QuerySelection010.parentBlock_frame _ _ _ _ _ _ _ (by omega)]; exact hv.pointer
  · intro other ho
    rw [PA17QuerySelection010.parentBlock_frame _ _ _ _ _ _ _ (by omega)]; exact hv.counts other ho
  · intro other ho
    rw [PA17QuerySelection010.parentBlock_frame _ _ _ _ _ _ _ (by omega)]; exact hv.payload other ho

theorem parentBlock_candidates (size countBase childBase : Nat)
    (rom : PhysicalROM) (hd : ParentData size rom) (node : Nat) (hn : node < size) (state : State)
    (hc : CandidatesLE size childBase state.heap) :
    CandidatesLE size childBase
      (execute rom.semantic (PA17QuerySelection010.parentBlock countBase (childBase + size + 1) childBase node) state).heap := by
  have hp := hd.value node hn
  have hv := hc (rom.semantic.read .internal node) hp
  intro encoded he
  rw [PA17QuerySelection010.parentBlock_heap]
  by_cases heq : childBase + encoded = childBase + rom.semantic.read .internal node
  · rw [heq, Function.update_self]
    split_ifs <;> omega
  · rw [Function.update_of_ne heq]
    exact hc encoded he

theorem parentBlock_numeric (B heapWords size q countBase leafBase header rowBase childBase payloadBase : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords size q countBase leafBase header rowBase childBase)
    (hd : ParentData size rom) (hpayload : payloadBase + size ≤ childBase)
    (node : Nat) (hn : node < size) (state : State)
    (hv : PushValues size q countBase (childBase + size + 1) payloadBase state.heap)
    (hc : CandidatesLE size childBase state.heap) (hr : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom
      (PA17QuerySelection010.parentBlock countBase (childBase + size + 1) childBase node) state := by
  have hp := hd.value node hn
  have hpAccess := hd.access
  have hcount := hv.counts node hn
  have hvalue := hv.payload node hn
  have hchild := hc (rom.semantic.read .internal node) hp
  have hcounts := hl.counts
  have hB := hl.scratch_le
  have hH := hl.scratch_access
  have hq := hl.q_le
  constructor
  · intro k hk r
    have hreg := hr r
    change k ≤ 17 at hk
    interval_cases k <;> cases r <;>
      simp [PA17QuerySelection010.parentBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute, hv.pointer]
    all_goals (try split_ifs)
    all_goals omega
  · intro k hk
    change k < 17 at hk
    interval_cases k <;>
      simp [PA17QuerySelection010.parentBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute,
        AccessFits, PhysicalROM.words, hv.pointer]
    all_goals omega

theorem descentInit_numeric (B heapWords size q countBase leafBase header rowBase childBase : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords size q countBase leafBase header rowBase childBase)
    (state : State) (hv : ReadValuesBound size q countBase leafBase header rowBase state.heap)
    (hr : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (descentInit header) state := by
  have hh := hl.header
  have hB := hl.scratch_le
  have hH := hl.scratch_access
  have hn := hv.node
  constructor
  · intro k hk r
    have hreg := hr r
    change k ≤ 4 at hk
    interval_cases k <;> cases r <;> simp [descentInit, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals omega
  · intro k hk
    change k < 4 at hk
    interval_cases k <;> simp [descentInit, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits]
    all_goals omega

theorem descentBlock_numeric (B heapWords size q countBase leafBase header rowBase childBase : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords size q countBase leafBase header rowBase childBase)
    (state : State) (hv : ReadValuesBound size q countBase leafBase header rowBase state.heap)
    (hc : CandidatesLE size childBase state.heap) (hr : RegistersLE (2 * B) state)
    (hn : state.register .address ≤ size) (hone : state.register .total = 1) :
    NumericSafe (2 * B) heapWords rom (block leafBase childBase) state := by
  have hnode : state.register .address - 1 < size := by have := hl.size_pos; omega
  have hlabel := hv.labels (state.register .address - 1) hnode
  have hchild := hc (state.register .address) hn
  have hlabels := hl.labels
  have hB := hl.scratch_le
  have hH := hl.scratch_access
  have hq := hl.q_le
  have hvalue := hr .value
  constructor
  · intro k hk r
    have hreg := hr r
    change k ≤ 11 at hk
    interval_cases k <;> cases r <;>
      simp [block, IndexedClosureRAM.execute, Op.execute, Instruction.execute, hone]
    all_goals (try split_ifs)
    all_goals omega
  · intro k hk
    change k < 11 at hk
    interval_cases k <;> simp [block, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, hone]
    all_goals omega

theorem descentBlock_address_le (size leafBase childBase : Nat) (rom : ROM) (state : State)
    (hc : CandidatesLE size childBase state.heap) (hn : state.register .address ≤ size) :
    (execute rom (block leafBase childBase) state).register .address ≤ size := by
  have hh := hc (state.register .address) hn
  rw [block_address]
  split_ifs <;> omega

theorem descentLoop_numeric (B heapWords size q countBase leafBase header rowBase childBase : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords size q countBase leafBase header rowBase childBase)
    (fuel : Nat) (state : State) (hv : ReadValuesBound size q countBase leafBase header rowBase state.heap)
    (hc : CandidatesLE size childBase state.heap) (hr : RegistersLE (2 * B) state)
    (hn : state.register .address ≤ size) (hone : state.register .total = 1) :
    NumericSafe (2 * B) heapWords rom (loop leafBase childBase fuel) state := by
  induction fuel generalizing state with
  | zero =>
    constructor
    · intro _ _; simpa [loop, IndexedClosureRAM.execute] using hr
    · intro k hk; simp [loop] at hk
  | succ fuel ih =>
    rw [loop, List.replicate_succ, List.flatten_cons]
    have hs := descentBlock_numeric B heapWords size q countBase leafBase header rowBase childBase rom hl state hv hc hr hn hone
    apply NumericSafe.append _ _ _ _ _ _ hs
    change NumericSafe (2 * B) heapWords rom (loop leafBase childBase fuel) _
    apply ih
    · rw [block_heap]; exact hv
    · rw [block_heap]; exact hc
    · exact hs.final _ _ _ _ _
    · exact descentBlock_address_le size leafBase childBase rom.semantic state hc hn
    · rw [block_total]; exact hone

theorem finish_numeric (B heapWords size q countBase leafBase header rowBase childBase payloadBase : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords size q countBase leafBase header rowBase childBase)
    (hpayload : payloadBase + size ≤ childBase) (state : State) (hr : RegistersLE (2 * B) state)
    (hptr : state.heap (childBase + size + 1) = payloadBase) (hone : state.register .total = 1)
    (htag : state.heap (payloadBase - 1) ≤ q) (henabled : state.heap (header + 7) ≤ 1) :
    NumericSafe (2 * B) heapWords rom (finish header (childBase + size + 1) (childBase + size + 2)) state := by
  have hB := hl.scratch_le
  have hH := hl.scratch_access
  have hh := hl.header
  have hq := hl.q_le
  have hs := hl.size_pos
  have hvalue := hr .value
  constructor
  · intro k hk r
    have hreg := hr r
    change k ≤ 12 at hk
    interval_cases k <;> cases r <;>
      simp [finish, IndexedClosureRAM.execute, Op.execute, Instruction.execute, hptr, hone]
    all_goals (try split_ifs)
    all_goals omega
  · intro k hk
    change k < 12 at hk
    interval_cases k <;>
      simp [finish, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, hptr, hone]
    all_goals omega

theorem parentNodes_numeric (B heapWords size q countBase leafBase header rowBase childBase payloadBase : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords size q countBase leafBase header rowBase childBase)
    (hd : ParentData size rom) (hpayload : payloadBase + size ≤ childBase)
    (nodes : List Nat) (hn : ∀ node ∈ nodes, node < size) (state : State)
    (hv : PushValues size q countBase (childBase + size + 1) payloadBase state.heap)
    (hc : CandidatesLE size childBase state.heap) (hr : RegistersLE (2 * B) state) :
    let ops := nodes.flatMap (PA17QuerySelection010.parentBlock countBase (childBase + size + 1) childBase)
    NumericSafe (2 * B) heapWords rom ops state ∧
      PushValues size q countBase (childBase + size + 1) payloadBase (execute rom.semantic ops state).heap ∧
      CandidatesLE size childBase (execute rom.semantic ops state).heap := by
  dsimp only
  induction nodes generalizing state with
  | nil => exact ⟨PA17GivenWord031a.NumericSafe.nil _ _ _ _ hr, hv, hc⟩
  | cons node later ih =>
    rw [List.flatMap_cons]
    have hnode := hn node List.mem_cons_self
    have hs := parentBlock_numeric B heapWords size q countBase leafBase header rowBase childBase payloadBase rom hl hd hpayload
      node hnode state hv hc hr
    have hv' := parentBlock_pushValues size q countBase childBase payloadBase hl.counts hpayload rom hd node hnode state hv
    have hc' := parentBlock_candidates size countBase childBase rom hd node hnode state hc
    have hi := ih (fun other ho => hn other (List.mem_cons_of_mem node ho)) _ hv' hc' (hs.final _ _ _ _ _)
    refine ⟨NumericSafe.append _ _ _ _ _ _ hs hi.1, ?_, ?_⟩
    · simpa only [IndexedClosureRAM.execute_append] using hi.2.1
    · simpa only [IndexedClosureRAM.execute_append] using hi.2.2

theorem parentProgram_numeric (B heapWords size q countBase leafBase header rowBase childBase payloadBase : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords size q countBase leafBase header rowBase childBase)
    (hd : ParentData size rom) (hpayload : payloadBase + size ≤ childBase) (state : State)
    (hv : PushValues size q countBase (childBase + size + 1) payloadBase state.heap)
    (hr : RegistersLE (2 * B) state) :
    let ops := PA17QuerySelection010.program size countBase (childBase + size + 1) childBase
    NumericSafe (2 * B) heapWords rom ops state ∧
      PushValues size q countBase (childBase + size + 1) payloadBase (execute rom.semantic ops state).heap ∧
      CandidatesLE size childBase (execute rom.semantic ops state).heap := by
  dsimp only
  have hB := hl.scratch_le
  have hH := hl.scratch_access
  have h1 := PA17GivenWord031a.clearWords_numeric B heapWords childBase (size + 1) rom (by omega) (by omega) state hr
  have hv' := clearWords_pushValues size q countBase childBase payloadBase hl.counts hpayload rom.semantic state hv
  have hc' := clearWords_candidates size childBase rom.semantic state
  have h2 := parentNodes_numeric B heapWords size q countBase leafBase header rowBase childBase payloadBase rom hl hd hpayload
    (List.range size).reverse (by intro node hn; exact List.mem_range.mp (List.mem_reverse.mp hn)) _ hv' hc' (h1.final _ _ _ _ _)
  refine ⟨?_, ?_, ?_⟩
  · exact NumericSafe.append _ _ _ _ _ _ h1 h2.1
  · simpa only [PA17QuerySelection010.program, PA17QuerySelection010.pushList, IndexedClosureRAM.execute_append] using h2.2.1
  · simpa only [PA17QuerySelection010.program, PA17QuerySelection010.pushList, IndexedClosureRAM.execute_append] using h2.2.2

theorem program_numeric (B heapWords size q countBase leafBase header rowBase childBase : Nat)
    (rom : PhysicalROM) (hl : Layout B heapWords size q countBase leafBase header rowBase childBase)
    (hd : ParentData size rom) (state : State)
    (hv : ReadValuesBound size q countBase leafBase header rowBase state.heap)
    (hr : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords rom (program size countBase leafBase header childBase) state := by
  let selected := selectedPayload size header state.heap
  let imported := execute rom.semantic (prelude size header (childBase + size + 1)) state
  let pushed := execute rom.semantic (PA17QuerySelection010.program size countBase (childBase + size + 1) childBase) imported
  let started := execute rom.semantic (descentInit header) pushed
  let walked := execute rom.semantic (loop leafBase childBase size) started
  have hselected : selected + size ≤ childBase :=
    selectedPayload_le B heapWords size q countBase leafBase header rowBase childBase hl state.heap hv
  have h1 := prelude_numeric B heapWords size q countBase leafBase header rowBase childBase rom hl state hv hr
  have hf1 (address : Nat) (ha : address < childBase) : imported.heap address = state.heap address := by
    have hh := PA17QuerySelectionSafety020.prelude_prefixFrame rom.semantic size header childBase address ha state
      (prelude size header (childBase + size + 1)).length le_rfl
    simpa only [List.take_length] using hh
  have hv1 : ReadValuesBound size q countBase leafBase header rowBase imported.heap :=
    hv.transfer B heapWords size q countBase leafBase header rowBase childBase hl state.heap imported.heap hf1
  have hp1 : PushValues size q countBase (childBase + size + 1) selected imported.heap := by
    constructor
    · dsimp only [imported]
      rw [prelude_heap, Function.update_self]
      rfl
    · exact hv1.counts
    · intro node hn
      rw [hf1 (selected + node) (by omega)]
      exact selectedPayload_values size q countBase leafBase header rowBase state.heap hv node hn
  have h2 := parentProgram_numeric B heapWords size q countBase leafBase header rowBase childBase selected rom hl hd hselected
    imported hp1 (h1.final _ _ _ _ _)
  have hf2 (address : Nat) (ha : address < childBase) : pushed.heap address = imported.heap address := by
    have hh := PA17QuerySelectionSafety020.parentProgram_prefixFrame rom.semantic size countBase (childBase + size + 1) childBase address ha imported
      (PA17QuerySelection010.program size countBase (childBase + size + 1) childBase).length le_rfl
    simpa only [List.take_length] using hh
  have hv2 : ReadValuesBound size q countBase leafBase header rowBase pushed.heap :=
    hv1.transfer B heapWords size q countBase leafBase header rowBase childBase hl imported.heap pushed.heap hf2
  have h3 := descentInit_numeric B heapWords size q countBase leafBase header rowBase childBase rom hl pushed hv2 (h2.1.final _ _ _ _ _)
  have hv3 : ReadValuesBound size q countBase leafBase header rowBase started.heap := by
    dsimp only [started]; rw [descentInit_heap]; exact hv2
  have hc3 : CandidatesLE size childBase started.heap := by
    dsimp only [started]; rw [descentInit_heap]; exact h2.2.2
  have hn3 : started.register .address ≤ size :=
    (descentInit_registers rom.semantic header pushed).1.trans_le hv2.node
  have hone3 : started.register .total = 1 := (descentInit_registers rom.semantic header pushed).2.1
  have h4 := descentLoop_numeric B heapWords size q countBase leafBase header rowBase childBase rom hl size started hv3 hc3
    (h3.final _ _ _ _ _) hn3 hone3
  have hcore : NumericSafe (2 * B) heapWords rom (core size countBase leafBase header childBase) state := by
    simp only [core, List.append_assoc]
    exact NumericSafe.append _ _ _ _ _ _ h1
      (NumericSafe.append _ _ _ _ _ _ h2.1 (NumericSafe.append _ _ _ _ _ _ h3 h4))
  have hcoreState : execute rom.semantic (core size countBase leafBase header childBase) state = walked := by
    simp only [core, IndexedClosureRAM.execute_append]
    rfl
  have hf4 (address : Nat) (ha : address < childBase) : walked.heap address = state.heap address := by
    rw [← hcoreState]
    have hh := PA17QuerySelectionSafety020.core_prefixFrame rom.semantic size countBase leafBase header childBase address ha state
      (core size countBase leafBase header childBase).length le_rfl
    simpa only [List.take_length] using hh
  have hptr4 : walked.heap (childBase + size + 1) = selected := by
    dsimp only [walked]
    rw [loop_heap]
    dsimp only [started]
    rw [descentInit_heap]
    exact h2.2.1.pointer
  have hone4 : walked.register .total = 1 := (loop_total rom.semantic leafBase childBase size started).trans hone3
  have htag4 : walked.heap (selected - 1) ≤ q := by
    rw [hf4 (selected - 1) (by have := hl.size_pos; omega)]
    exact selectedPayload_tag size q countBase leafBase header rowBase state.heap hv
  have henabled4 : walked.heap (header + 7) ≤ 1 := by
    rw [hf4 (header + 7) (by have := hl.header; omega)]
    exact hv.enabled
  have h5 := finish_numeric B heapWords size q countBase leafBase header rowBase childBase selected rom hl hselected walked
    (h4.final _ _ _ _ _) hptr4 hone4 htag4 henabled4
  rw [program]
  apply NumericSafe.append _ _ _ _ _ _ hcore
  rw [hcoreState]
  exact h5

theorem prepared_program_numeric (q : Nat) (full : List (Finset (Fin q))) (queryStage : Nat) (used : Finset (Fin q))
    (B heapWords countBase leafBase header rowBase childBase : Nat)
    (hl : Layout B heapWords (prepareNormalization q full).indexed.nodes.size q countBase leafBase header rowBase childBase)
    (state : State)
    (hv : ReadValuesBound (prepareNormalization q full).indexed.nodes.size q countBase leafBase header rowBase state.heap)
    (hr : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) heapWords (queryROM q full queryStage used)
      (program (prepareNormalization q full).indexed.nodes.size countBase leafBase header childBase) state :=
  program_numeric B heapWords (prepareNormalization q full).indexed.nodes.size q countBase leafBase header rowBase childBase
    (queryROM q full queryStage used) hl (queryROM_parentData q full queryStage used) state hv hr

theorem encodeTool_le (q : Nat) (tool : Option (Fin q)) : PA17LeafLabels005.encodeTool tool ≤ q := by
  cases tool with
  | none => exact Nat.zero_le _
  | some tool => exact tool.isLt

theorem prepared_program_tool_le (q : Nat) (full : List (Finset (Fin q))) (queryStage : Nat) (used : Finset (Fin q))
    (counts : IndexedCapacity (prepareNormalization q full).indexed)
    (countBase leafBase header childBase sourceSlot : Nat)
    (hcountBase : countBase + (prepareNormalization q full).indexed.nodes.size ≤ childBase)
    (hleafBase : leafBase + (prepareNormalization q full).indexed.nodes.size ≤ childBase)
    (hheader : header + 7 < childBase)
    (hsource : (sourceSlot + 1) * ((prepareNormalization q full).indexed.nodes.size + 1) ≤ childBase)
    (state : State)
    (hslot : state.heap header + ((prepareNormalization q full).indexed.nodes.size + 1) * state.heap (header + 6) =
      sourceSlot * ((prepareNormalization q full).indexed.nodes.size + 1))
    (hcounts : ∀ node : (prepareNormalization q full).indexed.NodeId, state.heap (countBase + node.val) = counts.get node)
    (hlabels : LabelsFor (prepareNormalization q full).indexed (IndexedDescent.leafTools (prepareNormalization q full).indexed) leafBase state.heap)
    (node : Option (prepareNormalization q full).indexed.NodeId)
    (hnode : state.heap (header + 1) = encodedNode (prepareNormalization q full).indexed node) :
    let cache := (prepareNormalization q full).indexed
    let result := execute (queryROM q full queryStage used).semantic (program cache.nodes.size countBase leafBase header childBase) state
    result.register .index ≤ q ∧ result.heap (childBase + cache.nodes.size + 2) ≤ q := by
  have hh := prepared_program_selectEntry q full queryStage used counts countBase leafBase header childBase sourceSlot
    hcountBase hleafBase hheader hsource state hslot hcounts hlabels node hnode
  have hbound : (if state.heap (header + 7) = 0 then 0 else
      PA17LeafLabels005.encodeTool (IndexedQuery.selectEntry (prepareNormalization q full).indexed
        (IndexedDescent.leafTools (prepareNormalization q full).indexed) counts node
        (readEntry (prepareNormalization q full).indexed.nodes.size sourceSlot state.heap))) ≤ q := by
    split_ifs
    · exact Nat.zero_le _
    · exact encodeTool_le q _
  exact ⟨hh.1.trans_le hbound, hh.2.trans_le hbound⟩

end PaperProofs.Structure.LaminarTree.PA17QuerySelectWord029
