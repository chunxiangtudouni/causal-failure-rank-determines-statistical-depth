module

public import PaperProofs.Structure.PA17_HeapAncestors_001
public import PaperProofs.Structure.PA17_TagBridge_001
public import PaperProofs.Structure.IndexedQuery
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-! Runtime budget tests on a dynamic tag-first row. The code depends only
on dimensions/layout; row pointers, counts, stage node and parents are read
from the actual heap. No physical node-card premise is used, including VOID. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PA17QueryTests009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17TagBridge001

def mask (test : Bool) (value : Nat) : Nat := if test then value else 0

theorem mask_and (left right : Bool) (value : Nat) :
    mask right (mask left value) = mask (left && right) value := by
  cases left <;> cases right <;> rfl

theorem mask_zero (test : Bool) : mask test 0 = 0 := by cases test <;> rfl

theorem mask_bit (left right : Bool) : mask right (bit left) = bit (left && right) := by
  cases left <;> cases right <;> rfl

def acceptInit (size rowPointer budget : Nat) : List Op :=
  [.base (.constant .index rowPointer), .base (.loadHeap .address .index),
   .base (.constant .index (budget * (size + 1))), .base (.add .address .address .index),
   .base (.loadHeap .value .address), .base (.constant .fresh 0),
   .base (.constant .flag 1), .base (.select .flag .value .flag .fresh)]

def acceptNode (size rowPointer countsBase budget node : Nat) : List Op :=
  [.base (.constant .index rowPointer), .base (.loadHeap .address .index),
   .base (.constant .index (budget * (size + 1) + 1 + node)),
   .base (.add .address .address .index), .base (.loadHeap .value .address),
   .base (.constant .index (countsBase + node)), .base (.loadHeap .total .index),
   .subtract .old .total .value, .base (.constant .fresh 0),
   .base (.select .flag .old .fresh .flag)]

def acceptProgram (size rowPointer countsBase budget : Nat) : List Op :=
  acceptInit size rowPointer budget ++
    (List.range size).flatMap (acceptNode size rowPointer countsBase budget)

def storeFlag (address : Nat) : List Op :=
  [.base (.constant .index address), .base (.storeHeap .index .flag)]

def badInit (nodePointer : Nat) : List Op :=
  [.base (.constant .index nodePointer), .base (.loadHeap .address .index),
   .base (.constant .old 0), .base (.select .flag .address .flag .old),
   .base (.constant .total 1)]

def badNode (size rowPointer countsBase parentBase budget : Nat) : List Op :=
  [.subtract .index .address .total,
   .base (.constant .old rowPointer), .base (.loadHeap .old .old),
   .base (.constant .value (budget * (size + 1) + 1)),
   .base (.add .old .old .value), .base (.add .index .old .index),
   .base (.loadHeap .value .index), .subtract .index .address .total,
   .base (.constant .old countsBase), .base (.add .index .old .index),
   .base (.loadHeap .fresh .index), .subtract .value .value .fresh,
   .base (.constant .old 0), .base (.select .fresh .value .flag .old),
   .base (.select .flag .address .fresh .flag),
   .base (.constant .index parentBase), .base (.add .index .index .address),
   .base (.loadHeap .address .index)]

def badLoop (size rowPointer countsBase parentBase budget fuel : Nat) : List Op :=
  (List.replicate fuel (badNode size rowPointer countsBase parentBase budget)).flatten

theorem badLoop_succ (size rowPointer countsBase parentBase budget fuel : Nat) :
    badLoop size rowPointer countsBase parentBase budget (fuel + 1) =
      badNode size rowPointer countsBase parentBase budget ++
        badLoop size rowPointer countsBase parentBase budget fuel := rfl

def badProgram (size rowPointer countsBase parentBase nodePointer budget : Nat) : List Op :=
  badInit nodePointer ++ badLoop size rowPointer countsBase parentBase budget size

def budgetProgram (size rowPointer countsBase parentBase nodePointer goodFlags badFlags budget : Nat) : List Op :=
  acceptProgram size rowPointer countsBase budget ++ storeFlag (goodFlags + budget) ++
    badProgram size rowPointer countsBase parentBase nodePointer budget ++ storeFlag (badFlags + budget)

def program (size q rowPointer countsBase parentBase nodePointer goodFlags badFlags : Nat) : List Op :=
  (List.finRange (q + 2)).flatMap
    (fun budget => budgetProgram size rowPointer countsBase parentBase nodePointer goodFlags badFlags budget.val)

theorem acceptNode_heap (rom : ROM) (size rowPointer countsBase budget node : Nat) (state : State) :
    (execute rom (acceptNode size rowPointer countsBase budget node) state).heap = state.heap := rfl

theorem acceptInit_heap (rom : ROM) (size rowPointer budget : Nat) (state : State) :
    (execute rom (acceptInit size rowPointer budget) state).heap = state.heap := rfl

theorem acceptNode_flag (rom : ROM) (size rowPointer countsBase budget node : Nat) (state : State) :
    (execute rom (acceptNode size rowPointer countsBase budget node) state).register .flag =
      mask (decide (state.heap (countsBase + node) ≤
        state.heap (state.heap rowPointer + budget * (size + 1) + 1 + node))) (state.register .flag) := by
  simp [acceptNode, IndexedClosureRAM.execute, Op.execute, Instruction.execute, mask, Nat.add_assoc, Nat.sub_eq_zero_iff_le]

theorem acceptNodes_heap (rom : ROM) (size rowPointer countsBase budget : Nat) (nodes : List Nat) (state : State) :
    (execute rom (nodes.flatMap (acceptNode size rowPointer countsBase budget)) state).heap = state.heap := by
  induction nodes generalizing state with
  | nil => rfl
  | cons head later ih => rw [List.flatMap_cons, IndexedClosureRAM.execute_append, ih, acceptNode_heap]

theorem acceptNodes_flag (rom : ROM) (size rowPointer countsBase budget : Nat) (nodes : List Nat) (state : State) :
    (execute rom (nodes.flatMap (acceptNode size rowPointer countsBase budget)) state).register .flag =
      mask (nodes.all (fun node => decide (state.heap (countsBase + node) ≤
        state.heap (state.heap rowPointer + budget * (size + 1) + 1 + node)))) (state.register .flag) := by
  induction nodes generalizing state with
  | nil => rfl
  | cons head later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append, ih, acceptNode_heap, acceptNode_flag, mask_and, List.all_cons]

theorem acceptProgram_heap (rom : ROM) (size rowPointer countsBase budget : Nat) (state : State) :
    (execute rom (acceptProgram size rowPointer countsBase budget) state).heap = state.heap := by
  rw [acceptProgram, IndexedClosureRAM.execute_append, acceptNodes_heap, acceptInit_heap]

theorem acceptProgram_flag (rom : ROM) (size rowPointer countsBase budget : Nat) (state : State) :
    (execute rom (acceptProgram size rowPointer countsBase budget) state).register .flag =
      mask ((List.range size).all (fun node => decide (state.heap (countsBase + node) ≤
        state.heap (state.heap rowPointer + budget * (size + 1) + 1 + node))))
        (if state.heap (state.heap rowPointer + budget * (size + 1)) = 0 then 0 else 1) := by
  rw [acceptProgram, IndexedClosureRAM.execute_append, acceptNodes_flag, acceptInit_heap]
  rfl

theorem acceptProgram_correct {q : Nat} (cache : IndexedNodeCache (Fin q)) (rom : ROM)
    (rowPointer countsBase budget rowBase : Nat) (counts : IndexedCapacity cache)
    (entry : IndexedEntry.FixedEntry cache) (state : State)
    (hrow : state.heap rowPointer = rowBase)
    (hcounts : ∀ node : cache.NodeId, state.heap (countsBase + node.val) = counts.get node)
    (hentry : TagFirstRep cache state.heap (rowBase + budget * (cache.nodes.size + 1)) entry) :
    (execute rom (acceptProgram cache.nodes.size rowPointer countsBase budget) state).register .flag =
      bit (IndexedQuery.accepts cache counts entry) := by
  rw [acceptProgram_flag, hrow]
  cases entry with
  | void => rw [hentry]; exact mask_zero _
  | vector capacity =>
    rw [hentry.1]
    have ht : ((List.range cache.nodes.size).all (fun node => decide
        (state.heap (countsBase + node) ≤ state.heap (rowBase + budget * (cache.nodes.size + 1) + 1 + node)))) =
        IndexedQuery.accepts cache counts (.vector capacity) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq, IndexedQuery.accepts,
        List.mem_finRange, forall_const]
      constructor
      · intro h node
        have hh := h node.val node.isLt
        rw [hcounts node, hentry.2 node] at hh
        exact hh
      · intro h index hi
        rw [hcounts ⟨index, hi⟩, hentry.2 ⟨index, hi⟩]
        exact h ⟨index, hi⟩
    rw [ht]
    cases IndexedQuery.accepts cache counts (.vector capacity) <;> rfl

theorem badNode_heap (rom : ROM) (size rowPointer countsBase parentBase budget : Nat) (state : State) :
    (execute rom (badNode size rowPointer countsBase parentBase budget) state).heap = state.heap := rfl

theorem badNode_address (rom : ROM) (size rowPointer countsBase parentBase budget : Nat) (state : State) :
    (execute rom (badNode size rowPointer countsBase parentBase budget) state).register .address =
      state.heap (parentBase + state.register .address) := rfl

theorem badNode_total (rom : ROM) (size rowPointer countsBase parentBase budget : Nat) (state : State) :
    (execute rom (badNode size rowPointer countsBase parentBase budget) state).register .total =
      state.register .total := rfl

theorem badNode_flag (rom : ROM) (size rowPointer countsBase parentBase budget : Nat) (state : State)
    (hone : state.register .total = 1) :
    (execute rom (badNode size rowPointer countsBase parentBase budget) state).register .flag =
      if state.register .address = 0 then state.register .flag else
        mask (decide (state.heap (countsBase + (state.register .address - 1)) <
          state.heap (state.heap rowPointer + budget * (size + 1) + 1 + (state.register .address - 1))))
          (state.register .flag) := by
  simp [badNode, IndexedClosureRAM.execute, Op.execute, Instruction.execute, hone, mask, Nat.add_assoc,
    Nat.sub_eq_zero_iff_le]
  split_ifs <;> omega

theorem badLoop_heap (rom : ROM) (size rowPointer countsBase parentBase budget fuel : Nat) (state : State) :
    (execute rom (badLoop size rowPointer countsBase parentBase budget fuel) state).heap = state.heap := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih => rw [badLoop_succ, IndexedClosureRAM.execute_append, ih, badNode_heap]

def chainTest {q : Nat} (cache : IndexedNodeCache (Fin q)) (counts capacity : IndexedCapacity cache)
    (fuel : Nat) : Option cache.NodeId → Bool
  | none => true
  | some node => (IndexedAncestors.parentChain cache fuel node).all
      (fun ancestor => decide (counts.get ancestor < capacity.get ancestor))

theorem badLoop_flag {q : Nat} (cache : IndexedNodeCache (Fin q)) (rom : ROM)
    (rowPointer countsBase parentBase budget rowBase fuel : Nat)
    (counts capacity : IndexedCapacity cache) (state : State) (current : Option cache.NodeId)
    (hrow : state.heap rowPointer = rowBase)
    (hcounts : ∀ node : cache.NodeId, state.heap (countsBase + node.val) = counts.get node)
    (hcapacity : ∀ node : cache.NodeId,
      state.heap (rowBase + budget * (cache.nodes.size + 1) + 1 + node.val) = capacity.get node)
    (hparents : PA17HeapAncestors001.ParentHeapFor cache parentBase state.heap)
    (hcurrent : state.register .address = encodedNode cache current) (hone : state.register .total = 1) :
    (execute rom (badLoop cache.nodes.size rowPointer countsBase parentBase budget fuel) state).register .flag =
      mask (chainTest cache counts capacity fuel current) (state.register .flag) := by
  induction fuel generalizing state current with
  | zero => cases current <;> rfl
  | succ fuel ih =>
    let after := execute rom (badNode cache.nodes.size rowPointer countsBase parentBase budget) state
    rw [badLoop_succ, IndexedClosureRAM.execute_append]
    have hheap : after.heap = state.heap := badNode_heap _ _ _ _ _ _ state
    have ht : after.register .total = 1 := (badNode_total _ _ _ _ _ _ state).trans hone
    cases current with
    | none =>
      have ha : after.register .address = encodedNode cache none := by
        rw [badNode_address, hcurrent]
        exact hparents.1
      rw [ih after none (hheap ▸ hrow) (hheap ▸ hcounts) (hheap ▸ hcapacity) (hheap ▸ hparents) ha ht]
      simp only [chainTest, mask, ite_true]
      rw [badNode_flag _ _ _ _ _ _ state hone, hcurrent]
      rfl
    | some node =>
      have ha : after.register .address = encodedNode cache (cache.parents.get node) := by
        rw [badNode_address, hcurrent]
        exact hparents.2 node
      rw [ih after (cache.parents.get node) (hheap ▸ hrow) (hheap ▸ hcounts)
        (hheap ▸ hcapacity) (hheap ▸ hparents) ha ht]
      rw [badNode_flag _ _ _ _ _ _ state hone, hcurrent]
      simp only [encodedNode, Nat.add_sub_cancel, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, ite_false, hrow, hcounts node, hcapacity node]
      cases hp : cache.parents.get node with
      | none => simp only [chainTest, IndexedAncestors.parentChain, hp, List.all_cons, List.all_nil, Bool.and_true, mask, ite_true]
      | some parent =>
        rw [mask_and]
        simp only [chainTest, IndexedAncestors.parentChain, hp, List.all_cons]

theorem badInit_heap (rom : ROM) (nodePointer : Nat) (state : State) :
    (execute rom (badInit nodePointer) state).heap = state.heap := rfl

theorem badInit_flag (rom : ROM) (nodePointer : Nat) (state : State) :
    (execute rom (badInit nodePointer) state).register .flag =
      if state.heap nodePointer = 0 then 0 else state.register .flag := rfl

theorem badInit_address (rom : ROM) (nodePointer : Nat) (state : State) :
    (execute rom (badInit nodePointer) state).register .address = state.heap nodePointer := rfl

theorem badInit_total (rom : ROM) (nodePointer : Nat) (state : State) :
    (execute rom (badInit nodePointer) state).register .total = 1 := rfl

theorem badLoop_zero (rom : ROM) (size rowPointer countsBase parentBase budget fuel : Nat) (state : State)
    (hflag : state.register .flag = 0) (hone : state.register .total = 1) :
    (execute rom (badLoop size rowPointer countsBase parentBase budget fuel) state).register .flag = 0 := by
  induction fuel generalizing state with
  | zero => exact hflag
  | succ fuel ih =>
    rw [badLoop_succ, IndexedClosureRAM.execute_append]
    apply ih
    · rw [badNode_flag _ _ _ _ _ _ state hone, hflag, mask_zero]
      split_ifs <;> rfl
    · exact (badNode_total _ _ _ _ _ _ state).trans hone

theorem badProgram_correct {q : Nat} (cache : IndexedNodeCache (Fin q)) (rom : ROM)
    (rowPointer countsBase parentBase nodePointer budget rowBase : Nat)
    (counts : IndexedCapacity cache) (entry : IndexedEntry.FixedEntry cache) (node : Option cache.NodeId)
    (state : State) (hrow : state.heap rowPointer = rowBase)
    (hcounts : ∀ target : cache.NodeId, state.heap (countsBase + target.val) = counts.get target)
    (hentry : TagFirstRep cache state.heap (rowBase + budget * (cache.nodes.size + 1)) entry)
    (hparents : PA17HeapAncestors001.ParentHeapFor cache parentBase state.heap)
    (hnode : state.heap nodePointer = encodedNode cache node)
    (hflag : state.register .flag = bit (IndexedQuery.accepts cache counts entry)) :
    (execute rom (badProgram cache.nodes.size rowPointer countsBase parentBase nodePointer budget) state).register .flag =
      bit (IndexedQuery.extensionTest cache counts node entry) := by
  rw [badProgram, IndexedClosureRAM.execute_append]
  cases entry with
  | void =>
    apply badLoop_zero
    · rw [badInit_flag, hflag]
      split_ifs <;> rfl
    · exact badInit_total rom nodePointer state
  | vector capacity =>
    cases node with
    | none =>
      apply badLoop_zero
      · rw [badInit_flag, hnode]; rfl
      · exact badInit_total rom nodePointer state
    | some node =>
      rw [badLoop_flag cache rom rowPointer countsBase parentBase budget rowBase cache.nodes.size
        counts capacity (execute rom (badInit nodePointer) state) (some node) hrow hcounts (hentry.2) hparents
        ((badInit_address rom nodePointer state).trans hnode) (badInit_total rom nodePointer state)]
      rw [badInit_flag, hnode, hflag]
      simp only [encodedNode, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
      exact mask_bit _ _

def ReadOnly : Op → Prop
  | .base (.storeHeap _ _) => False
  | _ => True

theorem readOnly_op_heap (rom : ROM) (op : Op) (h : ReadOnly op) (state : State) :
    (op.execute rom state).heap = state.heap := by
  cases op with
  | subtract target left right => rfl
  | base instruction =>
    cases instruction <;> first | rfl | exact False.elim h

theorem readOnly_heap (rom : ROM) (code : List Op) (h : ∀ op ∈ code, ReadOnly op) (state : State) :
    (execute rom code state).heap = state.heap := by
  induction code generalizing state with
  | nil => rfl
  | cons head later ih =>
    rw [IndexedClosureRAM.execute, ih (fun op ho => h op (List.mem_cons_of_mem _ ho)),
      readOnly_op_heap rom head (h head List.mem_cons_self) state]

theorem readOnly_prefixFrame (rom : ROM) (code : List Op) (h : ∀ op ∈ code, ReadOnly op) (address : Nat) :
    UniformFreeTableSafety.PrefixFrame rom code address := by
  intro state count _
  rw [readOnly_heap rom (code.take count) (fun op ho => h op (List.mem_of_mem_take ho)) state]

theorem acceptProgram_readOnly (size rowPointer countsBase budget : Nat) :
    ∀ op ∈ acceptProgram size rowPointer countsBase budget, ReadOnly op := by
  intro op ho
  simp only [acceptProgram, List.mem_append, List.mem_flatMap] at ho
  rcases ho with ho | ⟨node, _, ho⟩
  · simp only [acceptInit, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  · simp only [acceptNode, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

theorem badProgram_readOnly (size rowPointer countsBase parentBase nodePointer budget : Nat) :
    ∀ op ∈ badProgram size rowPointer countsBase parentBase nodePointer budget, ReadOnly op := by
  intro op ho
  simp only [badProgram, List.mem_append] at ho
  rcases ho with ho | ho
  · simp only [badInit, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  · obtain ⟨block, hblock, hop⟩ := List.mem_flatten.mp ho
    have heq := (List.mem_replicate.mp hblock).2
    subst block
    simp only [badNode, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

theorem storeFlag_heap (rom : ROM) (address : Nat) (state : State) :
    (execute rom (storeFlag address) state).heap = Function.update state.heap address (state.register .flag) := rfl

theorem storeFlag_flag (rom : ROM) (address : Nat) (state : State) :
    (execute rom (storeFlag address) state).register .flag = state.register .flag := rfl

theorem storeFlag_prefixFrame (rom : ROM) (target address : Nat) (hne : address ≠ target) :
    UniformFreeTableSafety.PrefixFrame rom (storeFlag target) address := by
  intro state count hc
  change count ≤ 2 at hc
  interval_cases count <;> simp [storeFlag, IndexedClosureRAM.execute, Op.execute, Instruction.execute, hne]

theorem budgetProgram_prefixFrame (rom : ROM)
    (size rowPointer countsBase parentBase nodePointer goodFlags badFlags budget address : Nat)
    (hg : address ≠ goodFlags + budget) (hb : address ≠ badFlags + budget) :
    UniformFreeTableSafety.PrefixFrame rom
      (budgetProgram size rowPointer countsBase parentBase nodePointer goodFlags badFlags budget) address := by
  rw [budgetProgram]
  exact UniformFreeTableSafety.PrefixFrame.append rom _ _ address
    (UniformFreeTableSafety.PrefixFrame.append rom _ _ address
      (UniformFreeTableSafety.PrefixFrame.append rom _ _ address
        (readOnly_prefixFrame rom _ (acceptProgram_readOnly size rowPointer countsBase budget) address)
        (storeFlag_prefixFrame rom _ address hg))
      (readOnly_prefixFrame rom _ (badProgram_readOnly size rowPointer countsBase parentBase nodePointer budget) address))
    (storeFlag_prefixFrame rom _ address hb)

structure ReadBounds (size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit : Nat) : Prop where
  row_pointer : rowPointer < protectedLimit
  node_pointer : nodePointer < protectedLimit
  counts : countsBase + size ≤ protectedLimit
  parents : parentBase + size < protectedLimit
  table : rowBase + (q + 2) * (size + 1) ≤ protectedLimit

theorem rowWord_lt (size q rowBase protectedLimit : Nat)
    (htable : rowBase + (q + 2) * (size + 1) ≤ protectedLimit)
    (budget : Fin (q + 2)) (index : Nat) (hi : index ≤ size) :
    rowBase + budget.val * (size + 1) + index < protectedLimit := by
  have hh := Nat.mul_le_mul_right (size + 1) (show budget.val + 1 ≤ q + 2 from budget.isLt)
  rw [Nat.add_mul, Nat.one_mul] at hh
  omega

structure Inputs {q : Nat} (cache : IndexedNodeCache (Fin q))
    (rowPointer countsBase parentBase nodePointer rowBase : Nat)
    (counts : IndexedCapacity cache) (row : IndexedTable.Row cache (q + 1))
    (node : Option cache.NodeId) (heap : Nat → Nat) : Prop where
  row_pointer : heap rowPointer = rowBase
  node_pointer : heap nodePointer = encodedNode cache node
  counts : ∀ target : cache.NodeId, heap (countsBase + target.val) = counts.get target
  parents : PA17HeapAncestors001.ParentHeapFor cache parentBase heap
  entries : ∀ budget : Fin (q + 2),
    TagFirstRep cache heap (rowBase + budget.val * (cache.nodes.size + 1)) (row.get budget)

theorem Inputs.transfer {q : Nat} {cache : IndexedNodeCache (Fin q)}
    {rowPointer countsBase parentBase nodePointer rowBase protectedLimit : Nat}
    {counts : IndexedCapacity cache} {row : IndexedTable.Row cache (q + 1)} {node : Option cache.NodeId}
    {old fresh : Nat → Nat}
    (hi : Inputs cache rowPointer countsBase parentBase nodePointer rowBase counts row node old)
    (hb : ReadBounds cache.nodes.size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit)
    (hf : ∀ address < protectedLimit, fresh address = old address) :
    Inputs cache rowPointer countsBase parentBase nodePointer rowBase counts row node fresh := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hf rowPointer hb.row_pointer]; exact hi.row_pointer
  · rw [hf nodePointer hb.node_pointer]; exact hi.node_pointer
  · intro target
    rw [hf _ (by have := target.isLt; have := hb.counts; omega)]
    exact hi.counts target
  · constructor
    · rw [hf parentBase (by have := hb.parents; omega)]
      exact hi.parents.1
    · intro target
      rw [hf _ (by have := target.isLt; have := hb.parents; omega)]
      exact hi.parents.2 target
  · intro budget
    have hr := hi.entries budget
    cases he : row.get budget with
    | void =>
      change fresh (rowBase + budget.val * (cache.nodes.size + 1)) = 0
      rw [hf _ (by simpa only [Nat.add_zero] using rowWord_lt _ _ _ _ hb.table budget 0 (Nat.zero_le _))]
      simpa only [he, TagFirstRep] using hr
    | vector capacity =>
      constructor
      · rw [hf _ (by simpa only [Nat.add_zero] using rowWord_lt _ _ _ _ hb.table budget 0 (Nat.zero_le _))]
        exact (he ▸ hr).1
      · intro target
        rw [hf _ (by
          simpa only [Nat.add_assoc] using rowWord_lt _ _ _ _ hb.table budget (1 + target.val)
            (by have := target.isLt; omega))]
        exact (he ▸ hr).2 target

theorem budgetProgram_inputs {q : Nat} (cache : IndexedNodeCache (Fin q)) (rom : ROM)
    (rowPointer countsBase parentBase nodePointer rowBase protectedLimit goodFlags badFlags : Nat)
    (counts : IndexedCapacity cache) (row : IndexedTable.Row cache (q + 1)) (node : Option cache.NodeId)
    (state : State) (hi : Inputs cache rowPointer countsBase parentBase nodePointer rowBase counts row node state.heap)
    (hb : ReadBounds cache.nodes.size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit)
    (hg : protectedLimit ≤ goodFlags) (hbad : protectedLimit ≤ badFlags) (budget : Nat) :
    Inputs cache rowPointer countsBase parentBase nodePointer rowBase counts row node
      (execute rom (budgetProgram cache.nodes.size rowPointer countsBase parentBase nodePointer goodFlags badFlags budget) state).heap := by
  apply hi.transfer hb
  intro address ha
  have hf := budgetProgram_prefixFrame rom cache.nodes.size rowPointer countsBase parentBase nodePointer
    goodFlags badFlags budget address (by omega) (by omega) state _ le_rfl
  simpa only [List.take_length] using hf

theorem budgetProgram_correct {q : Nat} (cache : IndexedNodeCache (Fin q)) (rom : ROM)
    (rowPointer countsBase parentBase nodePointer rowBase protectedLimit goodFlags badFlags : Nat)
    (counts : IndexedCapacity cache) (row : IndexedTable.Row cache (q + 1)) (node : Option cache.NodeId)
    (state : State) (hi : Inputs cache rowPointer countsBase parentBase nodePointer rowBase counts row node state.heap)
    (hb : ReadBounds cache.nodes.size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit)
    (hg : protectedLimit ≤ goodFlags) (_hbad : protectedLimit ≤ badFlags) (budget : Fin (q + 2))
    (hne : goodFlags + budget.val ≠ badFlags + budget.val) :
    let result := execute rom
      (budgetProgram cache.nodes.size rowPointer countsBase parentBase nodePointer goodFlags badFlags budget.val) state
    result.heap (goodFlags + budget.val) = bit (IndexedQuery.accepts cache counts (row.get budget)) ∧
      result.heap (badFlags + budget.val) = bit (IndexedQuery.extensionTest cache counts node (row.get budget)) := by
  intro result
  let accepted := execute rom (acceptProgram cache.nodes.size rowPointer countsBase budget.val) state
  let stored := execute rom (storeFlag (goodFlags + budget.val)) accepted
  let tested := execute rom (badProgram cache.nodes.size rowPointer countsBase parentBase nodePointer budget.val) stored
  let output := execute rom (storeFlag (badFlags + budget.val)) tested
  have haccept : accepted.register .flag = bit (IndexedQuery.accepts cache counts (row.get budget)) :=
    acceptProgram_correct cache rom rowPointer countsBase budget.val rowBase counts (row.get budget) state
      hi.row_pointer hi.counts (hi.entries budget)
  have hs : Inputs cache rowPointer countsBase parentBase nodePointer rowBase counts row node stored.heap := by
    apply hi.transfer hb
    intro address ha
    rw [storeFlag_heap, Function.update_of_ne (by omega), acceptProgram_heap]
  have hstored : stored.register .flag = bit (IndexedQuery.accepts cache counts (row.get budget)) :=
    (storeFlag_flag rom (goodFlags + budget.val) accepted).trans haccept
  have htest : tested.register .flag = bit (IndexedQuery.extensionTest cache counts node (row.get budget)) :=
    badProgram_correct cache rom rowPointer countsBase parentBase nodePointer budget.val rowBase counts
      (row.get budget) node stored hs.row_pointer hs.counts (hs.entries budget) hs.parents hs.node_pointer hstored
  have hreadonly : tested.heap = stored.heap :=
    readOnly_heap rom _ (badProgram_readOnly cache.nodes.size rowPointer countsBase parentBase nodePointer budget.val) stored
  have hrun : result = output := by
    dsimp only [result, output, tested, stored, accepted]
    rw [budgetProgram, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append]
  rw [hrun]
  constructor
  · rw [storeFlag_heap, Function.update_of_ne hne, hreadonly, storeFlag_heap, Function.update_self, haccept]
  · rw [storeFlag_heap, Function.update_self, htest]

theorem budgets_correct {q : Nat} (cache : IndexedNodeCache (Fin q)) (rom : ROM)
    (rowPointer countsBase parentBase nodePointer rowBase protectedLimit goodFlags badFlags : Nat)
    (counts : IndexedCapacity cache) (row : IndexedTable.Row cache (q + 1)) (node : Option cache.NodeId)
    (hb : ReadBounds cache.nodes.size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit)
    (hg : protectedLimit ≤ goodFlags) (hbad : protectedLimit ≤ badFlags)
    (hcross : ∀ left right : Fin (q + 2), goodFlags + left.val ≠ badFlags + right.val)
    (budgets : List (Fin (q + 2))) (hnodup : budgets.Nodup) (state : State)
    (hi : Inputs cache rowPointer countsBase parentBase nodePointer rowBase counts row node state.heap) :
    ∀ budget ∈ budgets,
    let result := execute rom (budgets.flatMap (fun budget =>
      budgetProgram cache.nodes.size rowPointer countsBase parentBase nodePointer goodFlags badFlags budget.val)) state
    result.heap (goodFlags + budget.val) = bit (IndexedQuery.accepts cache counts (row.get budget)) ∧
      result.heap (badFlags + budget.val) = bit (IndexedQuery.extensionTest cache counts node (row.get budget)) := by
  induction budgets generalizing state with
  | nil => intro budget hm; cases hm
  | cons head later ih =>
    let middle := execute rom
      (budgetProgram cache.nodes.size rowPointer countsBase parentBase nodePointer goodFlags badFlags head.val) state
    have hmiddle := budgetProgram_inputs cache rom rowPointer countsBase parentBase nodePointer rowBase protectedLimit
      goodFlags badFlags counts row node state hi hb hg hbad head.val
    intro budget hm
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append]
    rcases List.mem_cons.mp hm with he | hm
    · subst budget
      have hfGood := UniformFreeTableSafety.PrefixFrame.flatMap rom later
        (fun budget => budgetProgram cache.nodes.size rowPointer countsBase parentBase nodePointer goodFlags badFlags budget.val)
        (goodFlags + head.val) (by
          intro other ho
          apply budgetProgram_prefixFrame
          · intro heq
            have hh : head = other := Fin.ext (Nat.add_left_cancel heq)
            exact (List.nodup_cons.mp hnodup).1 (hh ▸ ho)
          · exact hcross head other)
      have hfBad := UniformFreeTableSafety.PrefixFrame.flatMap rom later
        (fun budget => budgetProgram cache.nodes.size rowPointer countsBase parentBase nodePointer goodFlags badFlags budget.val)
        (badFlags + head.val) (by
          intro other ho
          apply budgetProgram_prefixFrame
          · exact (hcross other head).symm
          · intro heq
            have hh : head = other := Fin.ext (Nat.add_left_cancel heq)
            exact (List.nodup_cons.mp hnodup).1 (hh ▸ ho))
      have hgframe := hfGood middle _ le_rfl
      have hbframe := hfBad middle _ le_rfl
      rw [List.take_length] at hgframe hbframe
      dsimp only [middle] at hgframe hbframe ⊢
      rw [hgframe, hbframe]
      exact budgetProgram_correct cache rom rowPointer countsBase parentBase nodePointer rowBase protectedLimit
        goodFlags badFlags counts row node state hi hb hg hbad head (hcross head head)
    · exact ih (List.nodup_cons.mp hnodup).2 middle hmiddle budget hm

theorem program_correct {q : Nat} (cache : IndexedNodeCache (Fin q)) (rom : ROM)
    (rowPointer countsBase parentBase nodePointer rowBase protectedLimit goodFlags badFlags : Nat)
    (counts : IndexedCapacity cache) (row : IndexedTable.Row cache (q + 1)) (node : Option cache.NodeId)
    (state : State) (hi : Inputs cache rowPointer countsBase parentBase nodePointer rowBase counts row node state.heap)
    (hb : ReadBounds cache.nodes.size q rowPointer countsBase parentBase nodePointer rowBase protectedLimit)
    (hg : protectedLimit ≤ goodFlags) (hbad : protectedLimit ≤ badFlags)
    (hcross : ∀ left right : Fin (q + 2), goodFlags + left.val ≠ badFlags + right.val) :
    ∀ budget : Fin (q + 2),
    let result := execute rom (program cache.nodes.size q rowPointer countsBase parentBase nodePointer goodFlags badFlags) state
    result.heap (goodFlags + budget.val) = bit (IndexedQuery.accepts cache counts (row.get budget)) ∧
      result.heap (badFlags + budget.val) = bit (IndexedQuery.extensionTest cache counts node (row.get budget)) := by
  intro budget
  exact budgets_correct cache rom rowPointer countsBase parentBase nodePointer rowBase protectedLimit goodFlags badFlags
    counts row node hb hg hbad hcross (List.finRange (q + 2)) (List.nodup_finRange _) state hi budget (List.mem_finRange budget)

theorem program_prefixFrame (rom : ROM)
    (size q rowPointer countsBase parentBase nodePointer goodFlags badFlags address : Nat)
    (hg : ∀ budget < q + 2, address ≠ goodFlags + budget)
    (hb : ∀ budget < q + 2, address ≠ badFlags + budget) :
    UniformFreeTableSafety.PrefixFrame rom
      (program size q rowPointer countsBase parentBase nodePointer goodFlags badFlags) address := by
  rw [program]
  apply UniformFreeTableSafety.PrefixFrame.flatMap
  intro budget _
  exact budgetProgram_prefixFrame rom size rowPointer countsBase parentBase nodePointer goodFlags badFlags
    budget.val address (hg budget.val budget.isLt) (hb budget.val budget.isLt)

theorem program_protected_prefix (rom : ROM)
    (size q rowPointer countsBase parentBase nodePointer goodFlags badFlags protectedLimit : Nat)
    (hg : protectedLimit ≤ goodFlags) (hb : protectedLimit ≤ badFlags) (state : State) (count : Nat)
    (hc : count ≤ (program size q rowPointer countsBase parentBase nodePointer goodFlags badFlags).length)
    (address : Nat) (ha : address < protectedLimit) :
    (execute rom ((program size q rowPointer countsBase parentBase nodePointer goodFlags badFlags).take count) state).heap address =
      state.heap address :=
  program_prefixFrame rom size q rowPointer countsBase parentBase nodePointer goodFlags badFlags address
    (by intro budget _; omega) (by intro budget _; omega) state count hc

theorem program_capacityThroughout (q words size rowPointer countsBase parentBase nodePointer goodFlags badFlags : Nat)
    (rom : PhysicalROM) (hg : words ≤ goodFlags) (hb : words ≤ badFlags) (state : State)
    (hbound : CapacityPrefixBounded q words state.heap) :
    CapacityThroughout q words rom
      (program size q rowPointer countsBase parentBase nodePointer goodFlags badFlags) state := by
  intro count hc address ha
  rw [program_protected_prefix rom.semantic size q rowPointer countsBase parentBase nodePointer goodFlags badFlags words
    hg hb state count hc address ha]
  exact hbound address ha

theorem acceptProgram_length (size rowPointer countsBase budget : Nat) :
    (acceptProgram size rowPointer countsBase budget).length = 10 * size + 8 := by
  have hn (node : Nat) : (acceptNode size rowPointer countsBase budget node).length = 10 := rfl
  simp only [acceptProgram, List.length_append, List.length_flatMap, hn, List.map_const',
    List.length_range, List.sum_replicate, Nat.nsmul_eq_mul]
  change 8 + size * 10 = 10 * size + 8
  omega

theorem badLoop_length (size rowPointer countsBase parentBase budget fuel : Nat) :
    (badLoop size rowPointer countsBase parentBase budget fuel).length = 18 * fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [badLoop_succ, List.length_append, ih]
    change 18 + 18 * fuel = 18 * (fuel + 1)
    omega

theorem budgetProgram_length (size rowPointer countsBase parentBase nodePointer goodFlags badFlags budget : Nat) :
    (budgetProgram size rowPointer countsBase parentBase nodePointer goodFlags badFlags budget).length = 28 * size + 17 := by
  simp only [budgetProgram, List.length_append, acceptProgram_length, badProgram, badLoop_length]
  change 10 * size + 8 + 2 + (5 + 18 * size) + 2 = _
  omega

theorem program_length (size q rowPointer countsBase parentBase nodePointer goodFlags badFlags : Nat) :
    (program size q rowPointer countsBase parentBase nodePointer goodFlags badFlags).length = (q + 2) * (28 * size + 17) := by
  simp only [program, List.length_flatMap, budgetProgram_length, List.map_const', List.length_finRange,
    List.sum_replicate, Nat.nsmul_eq_mul]

theorem acceptProgram_trace_length (size rowPointer countsBase budget : Nat) :
    (trace (acceptProgram size rowPointer countsBase budget)).length = 99 * size + 77 := by
  have hn (node : Nat) : (trace (acceptNode size rowPointer countsBase budget node)).length = 99 := rfl
  rw [acceptProgram, IndexedClosureRAM.trace_append, List.length_append,
    UniformNormalizationRAM.trace_flatMap_length]
  simp only [hn, List.map_const', List.length_range, List.sum_replicate, Nat.nsmul_eq_mul]
  change 77 + size * 99 = 99 * size + 77
  omega

theorem badLoop_trace_length (size rowPointer countsBase parentBase budget fuel : Nat) :
    (trace (badLoop size rowPointer countsBase parentBase budget fuel)).length = 185 * fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [badLoop_succ, IndexedClosureRAM.trace_append, List.length_append, ih]
    change 185 + 185 * fuel = 185 * (fuel + 1)
    omega

theorem budgetProgram_trace_length (size rowPointer countsBase parentBase nodePointer goodFlags badFlags budget : Nat) :
    (trace (budgetProgram size rowPointer countsBase parentBase nodePointer goodFlags badFlags budget)).length = 284 * size + 162 := by
  simp only [budgetProgram, IndexedClosureRAM.trace_append, List.length_append, acceptProgram_trace_length,
    badProgram, badLoop_trace_length]
  change 99 * size + 77 + 19 + (47 + 185 * size) + 19 = _
  omega

theorem program_trace_length (size q rowPointer countsBase parentBase nodePointer goodFlags badFlags : Nat) :
    (trace (program size q rowPointer countsBase parentBase nodePointer goodFlags badFlags)).length =
      (q + 2) * (284 * size + 162) := by
  rw [program, UniformNormalizationRAM.trace_flatMap_length]
  simp only [budgetProgram_trace_length, List.map_const', List.length_finRange, List.sum_replicate, Nat.nsmul_eq_mul]

theorem program_halting (rom : ROM)
    (size q rowPointer countsBase parentBase nodePointer goodFlags badFlags : Nat)
    (state : State) (hpc : state.pc = 0) :
    HaltingRuns rom (program size q rowPointer countsBase parentBase nodePointer goodFlags badFlags) state
      (execute rom (program size q rowPointer countsBase parentBase nodePointer goodFlags badFlags) state)
      (trace (program size q rowPointer countsBase parentBase nodePointer goodFlags badFlags) ++ haltTrace) :=
  execute_halts _ _ state hpc

theorem program_charged_bound (size q rowPointer countsBase parentBase nodePointer goodFlags badFlags : Nat)
    (hsize : 0 < size) :
    (haltingWords (program size q rowPointer countsBase parentBase nodePointer goodFlags badFlags)).length +
      (trace (program size q rowPointer countsBase parentBase nodePointer goodFlags badFlags) ++ haltTrace).length + 8 ≤
        2000 * ((q + 1) * size) := by
  rw [haltingWords_length, program_length, List.length_append, program_trace_length, haltTrace_length]
  have hq : q + 2 ≤ 2 * (q + 1) := by omega
  have hs : 284 * size + 162 ≤ 446 * size := by omega
  have hl : 28 * size + 17 ≤ 45 * size := by omega
  have hp1 := Nat.mul_le_mul hq hl
  have hp2 := Nat.mul_le_mul hq hs
  have hproduct : 0 < (q + 1) * size := Nat.mul_pos (by omega) hsize
  nlinarith [hp1, hp2]

end PaperProofs.Structure.LaminarTree.PA17QueryTests009



