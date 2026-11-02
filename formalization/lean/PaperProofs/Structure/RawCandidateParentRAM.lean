module

public import PaperProofs.Structure.RawCandidateOrderingRAM
public import PaperProofs.Structure.RawCandidatePairScan
public import PaperProofs.Structure.RawCandidateParents
public import PaperProofs.Structure.RawCandidateParentScan
public import PaperProofs.Structure.RawCandidateParentEncoding
import Mathlib.Tactic.Linarith

/-! Fixed-code parent search using the actual ordered candidate tables.
Parent cells double as the current encoded best choice.  Only a strictly
smaller eligible cardinality updates that choice, preserving first ties. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateParentRAM

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateOrderingRAM
open scoped BigOperators

def nodeCountAddress (base count : Nat) : Nat := arraySlot base count 4 0

def parentSlot (base count node : Nat) : Nat := arraySlot base count 4 node + 1

theorem parentSlot_eq (base count node : Nat) : parentSlot base count node = base + 5 + 4 * count + node := by
  unfold parentSlot arraySlot
  omega

def parentAddress : List PackingOp :=
  arrayAddress 4 1 ++ [.base (.base (.constant .index 1)), .base (.base (.add .address .address .index))]

def outerTest (exit : Nat) : List PackingOp :=
  arrayBase 4 ++ [.base (.base (.loadHeap .total .address))] ++ loadWorkspace .old 1 ++
    [.base (.subtract .flag .total .old), .base (.base (.constant .index (5 * exit))),
      .jumpIfZero .flag .index]

def initializeBestCard : List PackingOp :=
  [.base (.base (.constant .address 1)), .base (.base (.loadROM .input .total .address)),
   .base (.base (.constant .old 1)), .base (.base (.add .total .total .old))] ++ storeWorkspace 3

def initializeParent : List PackingOp :=
  [.base (.base (.constant .total 0))] ++ parentAddress ++ [.base (.base (.storeHeap .address .total))]

def initializeChild : List PackingOp := initializeBestCard ++ initializeParent ++ setWorkspace 2 0

def pairArguments : List PackingOp :=
  loadArray .value 2 1 ++ storeCell .value 1 ++ loadWorkspace .old 2 ++ storeCell .old 2

/-- A positive score is exactly strict containment, retained status, and
strict cardinality improvement.  Zero keeps both current best cells. -/
def conditionScore : List PackingOp :=
  loadCell .old 5 ++ loadCell .total 6 ++
    [.base (.base (.constant .flag 0)), .base (.base (.select .value .old .flag .total))] ++
    loadArray .old 1 2 ++
    [.base (.base (.constant .flag 0)), .base (.base (.select .value .old .value .flag))] ++
    loadArray .total 0 2 ++ loadWorkspace .old 3 ++
    [.base (.subtract .flag .old .total), .base (.base (.minimum .value .value .flag))]

def saveBestCard : List PackingOp :=
  [.base (.base (.select .total .value .total .old))] ++ storeWorkspace 3

def saveParent : List PackingOp :=
  loadArray .total 3 2 ++ parentAddress ++
    [.base (.base (.loadHeap .old .address)), .base (.base (.select .total .value .total .old)),
      .base (.base (.storeHeap .address .total))]

def innerTail (start : Nat) : List PackingOp :=
  conditionScore ++ saveBestCard ++ saveParent ++ incrementWorkspace 2 ++ jumpTo (start + 64)

def outerTail (start : Nat) : List PackingOp := incrementWorkspace 1 ++ jumpTo (start + 6)

def beforePair (start : Nat) : List PackingOp :=
  setWorkspace 1 0 ++ outerTest (start + 361) ++ initializeChild ++
    testWorkspace 2 (start + 346) ++ pairArguments

def programAt (start : Nat) : List PackingOp :=
  beforePair start ++ RawCandidatePairScan.programAt (start + 105) ++ innerTail start ++ outerTail start

theorem parentAddress_length : parentAddress.length = 20 := by
  simp only [parentAddress, List.length_append, arrayAddress_length, List.length_cons, List.length_nil]

theorem outerTest_length (exit : Nat) : (outerTest exit).length = 21 := by
  simp only [outerTest, List.length_append, arrayBase_length, loadWorkspace_length,
    List.length_cons, List.length_nil]

theorem initializeBestCard_length : initializeBestCard.length = 9 := by
  simp only [initializeBestCard, List.length_append, storeWorkspace_length,
    List.length_cons, List.length_nil]

theorem initializeParent_length : initializeParent.length = 22 := by
  simp only [initializeParent, List.length_append, parentAddress_length,
    List.length_cons, List.length_nil]

theorem initializeChild_length : initializeChild.length = 37 := by
  simp only [initializeChild, List.length_append, initializeBestCard_length, initializeParent_length]
  rfl

theorem pairArguments_length : pairArguments.length = 28 := by
  simp only [pairArguments, List.length_append, loadArray_length, loadWorkspace_length, storeCell]
  rfl

theorem conditionScore_length : conditionScore.length = 53 := by
  simp only [conditionScore, List.length_append, loadArray_length, loadWorkspace_length,
    loadCell, List.length_cons, List.length_nil]

theorem saveBestCard_length : saveBestCard.length = 6 := by
  simp only [saveBestCard, List.length_append, storeWorkspace_length, List.length_cons, List.length_nil]

theorem saveParent_length : saveParent.length = 42 := by
  simp only [saveParent, List.length_append, loadArray_length, parentAddress_length, List.length_cons, List.length_nil]

theorem innerTail_length (start : Nat) : (innerTail start).length = 116 := by
  simp only [innerTail, List.length_append, conditionScore_length, saveBestCard_length,
    saveParent_length, incrementWorkspace_length, jumpTo, List.length_cons, List.length_nil]

theorem outerTail_length (start : Nat) : (outerTail start).length = 15 := by
  simp only [outerTail, List.length_append, incrementWorkspace_length, jumpTo, List.length_cons, List.length_nil]

theorem beforePair_length (start : Nat) : (beforePair start).length = 105 := by
  simp only [beforePair, List.length_append, outerTest_length, initializeChild_length,
    testWorkspace_length, pairArguments_length, setWorkspace, storeWorkspace_length,
    List.length_cons, List.length_nil]

theorem programAt_length (start : Nat) : (programAt start).length = 361 := by
  simp only [programAt, List.length_append, beforePair_length,
    RawCandidatePairScan.programAt_length, innerTail_length, outerTail_length]

def paddingOp : PackingOp := .base (.base (.constant .value 0))

theorem append_slice (left right : List PackingOp) :
    left.length + 361 ≤ (left ++ programAt left.length ++ right).length ∧
      ∀ position < 361,
        (left ++ programAt left.length ++ right).getD (left.length + position) paddingOp =
          (programAt left.length).getD position paddingOp := by
  constructor
  · simp only [List.length_append, programAt_length]
    omega
  · intro position hp
    rw [List.getD_append (left ++ programAt left.length) right paddingOp _ (by
      simp only [List.length_append, programAt_length]; omega),
      List.getD_append_right left (programAt left.length) paddingOp _ (by omega), Nat.add_sub_cancel_left]

theorem parentAddress_runOps (rom : PhysicalROM) (state : NatState) :
    runOps rom parentAddress state =
      natExecuteOp rom (.base (.base (.add .address .address .index)))
        (natExecuteOp rom (.base (.base (.constant .index 1)))
          (RawCandidateOrderingRAM.addressed 4 1 state)) := by
  rw [parentAddress, runOps_append, arrayAddress_runOps]
  rfl

theorem parentAddress_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom parentAddress state).heap = state.heap := by
  rw [parentAddress_runOps]
  rfl

theorem parentAddress_value (rom : PhysicalROM) (state : NatState) :
    (runOps rom parentAddress state).register .address =
      parentSlot (state.heap 8) (state.heap (state.heap 8)) (state.heap (state.heap 8 + 1)) := by
  rw [parentAddress_runOps]
  simp [natExecuteOp, Op.execute, Instruction.execute, RawCandidateOrderingRAM.addressed, parentSlot]

theorem outerTest_values (rom : PhysicalROM) (exit : Nat) (state : NatState) :
    let result := runOps rom (outerTest exit) state
    result.heap = state.heap ∧ result.pc =
      (if state.heap (nodeCountAddress (state.heap 8) (state.heap (state.heap 8))) -
        state.heap (state.heap 8 + 1) = 0 then 5 * exit else state.pc + 105) ∧
      result.halted = state.halted := by
  simp only [outerTest, arrayBase, runOps_append, loadWorkspace_runOps]
  simp [RawCandidateOrderingRAM.loaded, loadCell,
    nodeCountAddress, arraySlot, runOps, natExecuteOp, natArithmetic,
    Op.execute, Instruction.execute, Nat.add_assoc]

theorem initializeBestCard_heap (q : Nat) (full : List (Finset (Fin q))) (state : NatState) :
    (runOps (rawIncidenceROM q full) initializeBestCard state).heap =
      Function.update state.heap (state.heap 8 + 3) (q + 1) := by
  simp [initializeBestCard, storeWorkspace, loadCell, runOps, natExecuteOp,
    Op.execute, Instruction.execute, raw_header_q]

theorem initializeParent_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom initializeParent state).heap = Function.update state.heap
      (parentSlot (state.heap 8) (state.heap (state.heap 8)) (state.heap (state.heap 8 + 1))) 0 := by
  simp only [initializeParent, runOps_append, parentAddress_runOps]
  simp [runOps, natExecuteOp, Op.execute, Instruction.execute, RawCandidateOrderingRAM.addressed, parentSlot]

theorem pairArguments_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom pairArguments state).heap =
      Function.update (Function.update state.heap 1
        (state.heap (arraySlot (state.heap 8) (state.heap (state.heap 8)) 2 (state.heap (state.heap 8 + 1)))))
        2 (state.heap (state.heap 8 + 2)) := by
  have h2 : state.heap 8 + 2 ≠ 1 := by omega
  simp only [pairArguments, runOps_append, loadArray_runOps, loadWorkspace_runOps]
  simp [storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute,
    RawCandidateOrderingRAM.addressed, RawCandidateOrderingRAM.loaded, h2]

def score (leftOnly rightOnly kept candidateCard bestCard : Nat) : Nat :=
  min (if kept = 0 then 0 else if leftOnly = 0 then rightOnly else 0) (bestCard - candidateCard)

theorem conditionScore_values (rom : PhysicalROM) (state : NatState) :
    let base := state.heap 8
    let count := state.heap base
    let later := state.heap (base + 2)
    let result := runOps rom conditionScore state
    result.register .value = score (state.heap 5) (state.heap 6)
      (state.heap (arraySlot base count 1 later)) (state.heap (arraySlot base count 0 later))
      (state.heap (base + 3)) ∧
      result.register .total = state.heap (arraySlot base count 0 later) ∧
      result.register .old = state.heap (base + 3) ∧ result.heap = state.heap ∧
      result.pc = state.pc + 265 ∧ result.halted = state.halted := by
  simp only [conditionScore, runOps_append, loadArray_runOps, loadWorkspace_runOps]
  simp [loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, score,
    RawCandidateOrderingRAM.addressed, RawCandidateOrderingRAM.loaded, Nat.add_assoc]

theorem saveBestCard_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom saveBestCard state).heap = Function.update state.heap (state.heap 8 + 3)
      (if state.register .value = 0 then state.register .old else state.register .total) := by
  simp [saveBestCard, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem saveBestCard_value (rom : PhysicalROM) (state : NatState) :
    (runOps rom saveBestCard state).register .value = state.register .value := by
  simp [saveBestCard, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem saveParent_heap (rom : PhysicalROM) (state : NatState) :
    let base := state.heap 8
    let count := state.heap base
    let child := state.heap (base + 1)
    let later := state.heap (base + 2)
    (runOps rom saveParent state).heap = Function.update state.heap (parentSlot base count child)
      (if state.register .value = 0 then state.heap (parentSlot base count child)
       else state.heap (arraySlot base count 3 later)) := by
  simp only [saveParent, runOps_append, loadArray_runOps, parentAddress_runOps]
  simp [runOps, natExecuteOp, Op.execute, Instruction.execute, RawCandidateOrderingRAM.addressed,
    parentSlot, Nat.add_assoc]

structure InputTables (q : Nat) (full : List (Finset (Fin q))) (base nodes : Nat)
    (order inverse : Nat → Nat) (state : NatState) : Prop where
  base_cell : state.heap 8 = base
  count_cell : state.heap base = full.length + q + 1
  node_count : state.heap (nodeCountAddress base (full.length + q + 1)) = nodes
  nodes_le : nodes ≤ full.length + q + 1
  cards : ∀ index < full.length + q + 1, state.heap (arraySlot base (full.length + q + 1) 0 index) =
    RawCandidateStableOrder.candidateCard q full index
  keeps : ∀ index < full.length + q + 1, state.heap (arraySlot base (full.length + q + 1) 1 index) =
    bit (RawCandidateOrder.keepCandidate q full index)
  ordered : ∀ node < nodes, state.heap (arraySlot base (full.length + q + 1) 2 node) = order node
  order_valid : ∀ node < nodes, order node < full.length + q + 1
  inverses : ∀ index < full.length + q + 1, state.heap (arraySlot base (full.length + q + 1) 3 index) = inverse index

theorem score_ne_zero_iff (leftOnly rightOnly kept candidateCard bestCard : Nat) :
    score leftOnly rightOnly kept candidateCard bestCard ≠ 0 ↔
      kept ≠ 0 ∧ leftOnly = 0 ∧ 0 < rightOnly ∧ candidateCard < bestCard := by
  unfold score
  by_cases hk : kept = 0 <;> by_cases hl : leftOnly = 0 <;>
    simp [hk, hl]
  omega

theorem score_candidates (q : Nat) (full : List (Finset (Fin q))) (child later best : Nat) :
    score (RawCandidateParents.candidateSupport q full child \ RawCandidateParents.candidateSupport q full later).card
      (RawCandidateParents.candidateSupport q full later \ RawCandidateParents.candidateSupport q full child).card
      (bit (RawCandidateOrder.keepCandidate q full later)) (RawCandidateStableOrder.candidateCard q full later) best ≠ 0 ↔
      (RawCandidateParentScan.eligible q full child later &&
        decide (RawCandidateStableOrder.candidateCard q full later < best)) = true := by
  rw [score_ne_zero_iff]
  have hbit : bit (RawCandidateOrder.keepCandidate q full later) ≠ 0 ↔
      RawCandidateOrder.keepCandidate q full later = true := by
    cases RawCandidateOrder.keepCandidate q full later <;> simp [bit]
  rw [hbit]
  simp only [RawCandidateParentScan.eligible, Bool.and_eq_true, decide_eq_true_eq,
    RawCandidateParentScan.strictSubset_iff_differenceCounts, and_assoc]

def ProtectedAddress (base count nodes address : Nat) : Prop :=
  8 ≤ address ∧ address ≠ base + 1 ∧ address ≠ base + 2 ∧ address ≠ base + 3 ∧
    (address < parentSlot base count 0 ∨ parentSlot base count 0 + nodes ≤ address)

theorem InputTables.transport (q : Nat) (full : List (Finset (Fin q))) (base nodes : Nat)
    (order inverse : Nat → Nat) (before after : NatState) (hlarge : 16 ≤ base)
    (tables : InputTables q full base nodes order inverse before)
    (hframe : ∀ address, ProtectedAddress base (full.length + q + 1) nodes address →
      after.heap address = before.heap address) : InputTables q full base nodes order inverse after := by
  have hb : after.heap 8 = base :=
    (hframe 8 ⟨le_rfl, by omega, by omega, by omega, Or.inl (by unfold parentSlot arraySlot; omega)⟩).trans tables.base_cell
  refine ⟨hb, ?_, ?_, tables.nodes_le, ?_, ?_, ?_, tables.order_valid, ?_⟩
  · exact (hframe base ⟨by omega, by omega, by omega, by omega,
      Or.inl (by unfold parentSlot arraySlot; omega)⟩).trans tables.count_cell
  · exact (hframe (nodeCountAddress base (full.length + q + 1))
      ⟨by unfold nodeCountAddress arraySlot; omega, by unfold nodeCountAddress arraySlot; omega,
        by unfold nodeCountAddress arraySlot; omega, by unfold nodeCountAddress arraySlot; omega,
        Or.inl (by unfold nodeCountAddress parentSlot arraySlot; omega)⟩).trans tables.node_count
  · intro index hi
    exact (hframe (arraySlot base (full.length + q + 1) 0 index)
      ⟨by unfold arraySlot; omega, by unfold arraySlot; omega, by unfold arraySlot; omega,
        by unfold arraySlot; omega, Or.inl (by unfold parentSlot arraySlot; omega)⟩).trans (tables.cards index hi)
  · intro index hi
    exact (hframe (arraySlot base (full.length + q + 1) 1 index)
      ⟨by unfold arraySlot; omega, by unfold arraySlot; omega, by unfold arraySlot; omega,
        by unfold arraySlot; omega, Or.inl (by unfold parentSlot arraySlot; omega)⟩).trans (tables.keeps index hi)
  · intro node hn
    exact (hframe (arraySlot base (full.length + q + 1) 2 node)
      ⟨by unfold arraySlot; omega, by unfold arraySlot; omega, by unfold arraySlot; omega,
        by unfold arraySlot; omega, Or.inl (by unfold parentSlot arraySlot; have ht := tables.nodes_le; omega)⟩).trans
      (tables.ordered node hn)
  · intro index hi
    exact (hframe (arraySlot base (full.length + q + 1) 3 index)
      ⟨by unfold arraySlot; omega, by unfold arraySlot; omega, by unfold arraySlot; omega,
        by unfold arraySlot; omega, Or.inl (by unfold parentSlot arraySlot; omega)⟩).trans (tables.inverses index hi)

theorem setWorkspace_heap (rom : PhysicalROM) (offset value : Nat) (state : NatState) :
    (runOps rom (setWorkspace offset value) state).heap =
      Function.update state.heap (state.heap 8 + offset) value := by
  simp [setWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem jumpTo_heap (rom : PhysicalROM) (exit : Nat) (state : NatState) :
    (runOps rom (jumpTo exit) state).heap = state.heap := by
  simp [jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem jumpTo_pc (rom : PhysicalROM) (exit : Nat) (state : NatState) :
    (runOps rom (jumpTo exit) state).pc = 5 * exit := by
  simp [jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem initializeChild_heap (q : Nat) (full : List (Finset (Fin q))) (base : Nat)
    (state : NatState) (hbase : state.heap 8 = base) (hlarge : 16 ≤ base) :
    (runOps (rawIncidenceROM q full) initializeChild state).heap =
      Function.update (Function.update (Function.update state.heap (base + 3) (q + 1))
        (parentSlot base (state.heap base) (state.heap (base + 1))) 0) (base + 2) 0 := by
  let rom := rawIncidenceROM q full
  let best := runOps rom initializeBestCard state
  let cleared := runOps rom initializeParent best
  have hb : best.heap = Function.update state.heap (base + 3) (q + 1) := by
    simpa only [hbase] using initializeBestCard_heap q full state
  have hb8 : best.heap 8 = base := by rw [hb]; simpa [show 8 ≠ base + 3 by omega] using hbase
  have hb0 : best.heap base = state.heap base := by rw [hb]; simp
  have hb1 : best.heap (base + 1) = state.heap (base + 1) := by rw [hb]; simp
  have hp := initializeParent_heap rom best
  rw [show best.heap 8 = base from hb8, hb0, hb1] at hp
  have hc8 : cleared.heap 8 = base := by
    change (runOps rom initializeParent best).heap 8 = base
    rw [hp]
    simpa [show 8 ≠ parentSlot base (state.heap base) (state.heap (base + 1)) by unfold parentSlot arraySlot; omega] using hb8
  simp only [initializeChild, runOps_append]
  change (runOps rom (setWorkspace 2 0) cleared).heap = _
  rw [setWorkspace_heap, hc8]
  change Function.update (runOps rom initializeParent best).heap (base + 2) 0 = _
  rw [hp, hb]

def updatedHeap (q : Nat) (full : List (Finset (Fin q))) (base node later : Nat)
    (inverse : Nat → Nat) (state : NatState) : Nat → Nat :=
  let value := score (state.heap 5) (state.heap 6) (bit (RawCandidateOrder.keepCandidate q full later))
    (RawCandidateStableOrder.candidateCard q full later) (state.heap (base + 3))
  Function.update (Function.update (Function.update state.heap (base + 3)
    (if value = 0 then state.heap (base + 3) else RawCandidateStableOrder.candidateCard q full later))
    (parentSlot base (full.length + q + 1) node)
    (if value = 0 then state.heap (parentSlot base (full.length + q + 1) node) else inverse later))
    (base + 2) (later + 1)

theorem innerTail_heap (q : Nat) (full : List (Finset (Fin q))) (start base nodes : Nat)
    (order inverse : Nat → Nat) (state : NatState) (hlarge : 16 ≤ base)
    (tables : InputTables q full base nodes order inverse state)
    (node later : Nat) (hnode : state.heap (base + 1) = node)
    (hlater : state.heap (base + 2) = later) (hj : later < full.length + q + 1) :
    (runOps (rawIncidenceROM q full) (innerTail start) state).heap = updatedHeap q full base node later inverse state := by
  let rom := rawIncidenceROM q full
  let conditioned := runOps rom conditionScore state
  let value := score (state.heap 5) (state.heap 6) (bit (RawCandidateOrder.keepCandidate q full later))
    (RawCandidateStableOrder.candidateCard q full later) (state.heap (base + 3))
  have hs := conditionScore_values rom state
  dsimp only at hs
  rw [tables.base_cell, tables.count_cell, hlater, tables.keeps later hj, tables.cards later hj] at hs
  rcases hs with ⟨hsv, hst, hso, hsh, _, _⟩
  let best := runOps rom saveBestCard conditioned
  have hb := saveBestCard_heap rom conditioned
  rw [show conditioned.heap = state.heap from hsh, tables.base_cell,
    show conditioned.register .value = value from hsv,
    show conditioned.register .old = state.heap (base + 3) from hso,
    show conditioned.register .total = RawCandidateStableOrder.candidateCard q full later from hst] at hb
  have hb8 : best.heap 8 = base := by
    change (runOps rom saveBestCard conditioned).heap 8 = base
    rw [hb]
    simpa [show 8 ≠ base + 3 by omega] using tables.base_cell
  have hb0 : best.heap base = full.length + q + 1 := by
    change (runOps rom saveBestCard conditioned).heap base = _
    rw [hb]
    simpa using tables.count_cell
  have hb1 : best.heap (base + 1) = node := by
    change (runOps rom saveBestCard conditioned).heap (base + 1) = _
    rw [hb]
    simpa using hnode
  have hb2 : best.heap (base + 2) = later := by
    change (runOps rom saveBestCard conditioned).heap (base + 2) = _
    rw [hb]
    simpa using hlater
  have hbInv : best.heap (arraySlot base (full.length + q + 1) 3 later) = inverse later := by
    change (runOps rom saveBestCard conditioned).heap _ = _
    rw [hb]
    simpa [show arraySlot base (full.length + q + 1) 3 later ≠ base + 3 by unfold arraySlot; omega] using tables.inverses later hj
  have hbParent : best.heap (parentSlot base (full.length + q + 1) node) = state.heap (parentSlot base (full.length + q + 1) node) := by
    change (runOps rom saveBestCard conditioned).heap _ = _
    rw [hb]
    simp [show parentSlot base (full.length + q + 1) node ≠ base + 3 by unfold parentSlot arraySlot; omega]
  have hbValue : best.register .value = value := (saveBestCard_value rom conditioned).trans hsv
  let encoded := runOps rom saveParent best
  have he := saveParent_heap rom best
  dsimp only at he
  rw [hb8, hb0, hb1, hb2, hbValue, hbParent, hbInv] at he
  have he8 : encoded.heap 8 = base := by
    change (runOps rom saveParent best).heap 8 = _
    rw [he]
    simpa [show 8 ≠ parentSlot base (full.length + q + 1) node by unfold parentSlot arraySlot; omega] using hb8
  have he2 : encoded.heap (base + 2) = later := by
    change (runOps rom saveParent best).heap (base + 2) = _
    rw [he]
    simpa [show base + 2 ≠ parentSlot base (full.length + q + 1) node by unfold parentSlot arraySlot; omega] using hb2
  let advanced := runOps rom (incrementWorkspace 2) encoded
  have ha := incrementWorkspace_heap rom 2 encoded
  rw [he8, he2] at ha
  simp only [innerTail, runOps_append]
  change (runOps rom (jumpTo (start + 64)) advanced).heap = _
  rw [jumpTo_heap]
  change (runOps rom (incrementWorkspace 2) encoded).heap = _
  rw [ha]
  change Function.update (runOps rom saveParent best).heap (base + 2) (later + 1) = _
  rw [he]
  change Function.update (Function.update (runOps rom saveBestCard conditioned).heap _ _) _ _ = _
  rw [hb]
  rfl

theorem innerTail_control (rom : PhysicalROM) (start : Nat) (state : NatState) :
    (runOps rom (innerTail start) state).pc = 5 * (start + 64) ∧
      (runOps rom (innerTail start) state).halted = state.halted := by
  constructor
  · rw [innerTail, runOps_append]
    exact jumpTo_pc _ _ _
  · exact runOps_halted _ _ _

theorem outerTail_control (rom : PhysicalROM) (start : Nat) (state : NatState) :
    (runOps rom (outerTail start) state).pc = 5 * (start + 6) ∧
      (runOps rom (outerTail start) state).halted = state.halted := by
  constructor
  · rw [outerTail, runOps_append]
    exact jumpTo_pc _ _ _
  · exact runOps_halted _ _ _

def innerLead (start : Nat) : List PackingOp :=
  conditionScore ++ saveBestCard ++ saveParent ++ incrementWorkspace 2 ++ (jumpTo (start + 64)).take 2

def outerLead (start : Nat) : List PackingOp := incrementWorkspace 1 ++ (jumpTo (start + 6)).take 2

theorem innerTail_split (start : Nat) : innerTail start = innerLead start ++ [.jumpIfZero .flag .index] := by
  simp only [innerTail, innerLead, jumpTo, List.take_succ_cons, List.take_zero,
    List.append_assoc, List.cons_append, List.nil_append]

theorem outerTail_split (start : Nat) : outerTail start = outerLead start ++ [.jumpIfZero .flag .index] := by
  simp only [outerTail, outerLead, jumpTo, List.take_succ_cons, List.take_zero,
    List.append_assoc, List.cons_append, List.nil_append]

theorem setWorkspace_length (offset value : Nat) : (setWorkspace offset value).length = 6 := by
  simp only [setWorkspace, List.length_append, storeWorkspace_length, List.length_cons, List.length_nil]

theorem innerLead_length (start : Nat) : (innerLead start).length = 115 := by
  simp only [innerLead, List.length_append, conditionScore_length, saveBestCard_length,
    saveParent_length, incrementWorkspace_length, jumpTo, List.take_succ_cons, List.take_zero,
    List.length_cons, List.length_nil]

theorem outerLead_length (start : Nat) : (outerLead start).length = 14 := by
  simp only [outerLead, List.length_append, incrementWorkspace_length, jumpTo,
    List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil]

private theorem getD_middle (left middle right : List PackingOp) (position : Nat)
    (hp : position < middle.length) :
    (left ++ middle ++ right).getD (left.length + position) paddingOp =
      middle.getD position paddingOp := by
  rw [List.getD_append (left ++ middle) right paddingOp _ (by simp; omega),
    List.getD_append_right left middle paddingOp _ (by omega), Nat.add_sub_cancel_left]

section Containing

variable (rom : PhysicalROM) (containing : List PackingOp) (start : Nat)
  (hbound : start + 361 ≤ containing.length)
  (hcode : ∀ position < 361, containing.getD (start + position) paddingOp =
    (programAt start).getD position paddingOp)

include hbound hcode

private theorem run_straight (offset : Nat) (block : List PackingOp)
    (hspan : offset + block.length ≤ 361)
    (hlocal : ∀ position < block.length,
      (programAt start).getD (offset + position) paddingOp = block.getD position paddingOp)
    (hstraight : ∀ op ∈ block, NoJump op) (state : NatState)
    (hpc : state.pc = 5 * (start + offset)) (hactive : state.halted = false) :
    natRun rom containing block.length state = runOps rom block state := by
  apply natRun_of_straight_segment rom containing block (start + offset) (by omega) ?_
    hstraight state hpc hactive
  intro position hp
  have hh := (hcode (offset + position) (by omega)).trans (hlocal position hp)
  rw [List.getD_eq_getElem containing paddingOp (by omega),
    List.getD_eq_getElem block paddingOp hp] at hh
  simpa only [Nat.add_assoc] using hh

private theorem run_branch (offset : Nat) (lead : List PackingOp) (last : PackingOp)
    (hspan : offset + lead.length + 1 ≤ 361)
    (hlocal : ∀ position < lead.length,
      (programAt start).getD (offset + position) paddingOp = lead.getD position paddingOp)
    (hlast : (programAt start).getD (offset + lead.length) paddingOp = last)
    (hstraight : ∀ op ∈ lead, NoJump op) (state : NatState)
    (hpc : state.pc = 5 * (start + offset)) (hactive : state.halted = false) :
    natRun rom containing (lead.length + 1) state = runOps rom (lead ++ [last]) state := by
  rw [runOps_append, runOps]
  apply natRun_of_segment_last rom containing lead last (start + offset) (by omega) ?_ ?_
    hstraight state hpc hactive
  · intro position hp
    have hh := (hcode (offset + position) (by omega)).trans (hlocal position hp)
    rw [List.getD_eq_getElem containing paddingOp (by omega),
      List.getD_eq_getElem lead paddingOp hp] at hh
    simpa only [Nat.add_assoc] using hh
  · have hh := (hcode (offset + lead.length) (by omega)).trans hlast
    rw [List.getD_eq_getElem containing paddingOp (by omega)] at hh
    simpa only [Nat.add_assoc] using hh

private theorem run_straight_piece (offset : Nat) (codePrefix block suffix : List PackingOp)
    (hsplit : programAt start = codePrefix ++ block ++ suffix) (hlength : codePrefix.length = offset)
    (hstraight : ∀ op ∈ block, NoJump op) (state : NatState)
    (hpc : state.pc = 5 * (start + offset)) (hactive : state.halted = false) :
    natRun rom containing block.length state = runOps rom block state := by
  have hlen : offset + block.length + suffix.length = 361 := by
    rw [← programAt_length start, hsplit, List.length_append, List.length_append, hlength]
  apply run_straight rom containing start hbound hcode offset block (by omega) ?_
    hstraight state hpc hactive
  intro position hp
  rw [hsplit]
  have hh := getD_middle codePrefix block suffix position hp
  rw [hlength] at hh
  exact hh

private theorem run_branch_piece (offset : Nat) (codePrefix lead suffix : List PackingOp) (last : PackingOp)
    (hsplit : programAt start = codePrefix ++ (lead ++ [last]) ++ suffix) (hlength : codePrefix.length = offset)
    (hstraight : ∀ op ∈ lead, NoJump op) (state : NatState)
    (hpc : state.pc = 5 * (start + offset)) (hactive : state.halted = false) :
    natRun rom containing (lead.length + 1) state = runOps rom (lead ++ [last]) state := by
  have hlen : offset + (lead.length + 1) + suffix.length = 361 := by
    rw [← programAt_length start, hsplit, List.length_append, List.length_append, hlength,
      List.length_append, List.length_singleton]
  apply run_branch rom containing start hbound hcode offset lead last (by omega) ?_ ?_
    hstraight state hpc hactive
  · intro position hp
    rw [hsplit]
    have hh := getD_middle codePrefix (lead ++ [last]) suffix position (by simp; omega)
    rw [hlength, List.getD_append lead [last] paddingOp position hp] at hh
    exact hh
  · rw [hsplit]
    have hh := getD_middle codePrefix (lead ++ [last]) suffix lead.length (by simp)
    rw [hlength, List.getD_append_right lead [last] paddingOp lead.length le_rfl,
      Nat.sub_self, List.getD_cons_zero] at hh
    exact hh

private theorem run_init (state : NatState)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false) :
    natRun rom containing 6 state = runOps rom (setWorkspace 1 0) state := by
  exact run_straight_piece rom containing start hbound hcode 0 [] (setWorkspace 1 0)
    (outerTest (start + 361) ++ initializeChild ++ testWorkspace 2 (start + 346) ++ pairArguments ++
      RawCandidatePairScan.programAt (start + 105) ++ innerTail start ++ outerTail start)
    (by simp only [programAt, beforePair, List.nil_append, List.append_assoc]) rfl
    (by simp [setWorkspace, storeWorkspace, loadCell, NoJump]) state
    (by simpa only [Nat.add_zero] using hpc) hactive

private theorem run_outerTest (state : NatState)
    (hpc : state.pc = 5 * (start + 6)) (hactive : state.halted = false) :
    natRun rom containing 21 state = runOps rom (outerTest (start + 361)) state := by
  have hs : outerTest (start + 361) = (outerTest (start + 361)).take 20 ++ [.jumpIfZero .flag .index] := rfl
  exact run_branch_piece rom containing start hbound hcode 6 (setWorkspace 1 0)
    ((outerTest (start + 361)).take 20)
    (initializeChild ++ testWorkspace 2 (start + 346) ++ pairArguments ++
      RawCandidatePairScan.programAt (start + 105) ++ innerTail start ++ outerTail start)
    (.jumpIfZero .flag .index)
    (by rw [← hs]; simp only [programAt, beforePair, List.append_assoc]) (setWorkspace_length 1 0)
    (by simp [outerTest, arrayBase, loadWorkspace, loadCell, NoJump]) state hpc hactive

private theorem run_initializeChild (state : NatState)
    (hpc : state.pc = 5 * (start + 27)) (hactive : state.halted = false) :
    natRun rom containing 37 state = runOps rom initializeChild state := by
  exact run_straight_piece rom containing start hbound hcode 27
    (setWorkspace 1 0 ++ outerTest (start + 361)) initializeChild
    (testWorkspace 2 (start + 346) ++ pairArguments ++ RawCandidatePairScan.programAt (start + 105) ++
      innerTail start ++ outerTail start)
    (by simp only [programAt, beforePair, List.append_assoc])
    (by simp only [List.length_append, setWorkspace_length, outerTest_length])
    (by simp [initializeChild, initializeBestCard, initializeParent, parentAddress, arrayAddress,
      arrayBase, setWorkspace, storeWorkspace, loadWorkspace, loadCell, NoJump]) state hpc hactive

private theorem run_innerTest (state : NatState)
    (hpc : state.pc = 5 * (start + 64)) (hactive : state.halted = false) :
    natRun rom containing 13 state = runOps rom (testWorkspace 2 (start + 346)) state := by
  have hs : testWorkspace 2 (start + 346) =
      (testWorkspace 2 (start + 346)).take 12 ++ [.jumpIfZero .flag .index] := rfl
  exact run_branch_piece rom containing start hbound hcode 64
    (setWorkspace 1 0 ++ outerTest (start + 361) ++ initializeChild)
    ((testWorkspace 2 (start + 346)).take 12)
    (pairArguments ++ RawCandidatePairScan.programAt (start + 105) ++ innerTail start ++ outerTail start)
    (.jumpIfZero .flag .index)
    (by rw [← hs]; simp only [programAt, beforePair, List.append_assoc])
    (by simp only [List.length_append, setWorkspace_length, outerTest_length, initializeChild_length])
    (by simp [testWorkspace, loadWorkspace, loadCell, NoJump]) state hpc hactive

private theorem run_pairArguments (state : NatState)
    (hpc : state.pc = 5 * (start + 77)) (hactive : state.halted = false) :
    natRun rom containing 28 state = runOps rom pairArguments state := by
  exact run_straight_piece rom containing start hbound hcode 77
    (setWorkspace 1 0 ++ outerTest (start + 361) ++ initializeChild ++ testWorkspace 2 (start + 346))
    pairArguments (RawCandidatePairScan.programAt (start + 105) ++ innerTail start ++ outerTail start)
    (by simp only [programAt, beforePair, List.append_assoc])
    (by simp only [List.length_append, setWorkspace_length, outerTest_length, initializeChild_length, testWorkspace_length])
    (by simp [pairArguments, loadArray, arrayAddress, arrayBase, loadWorkspace, loadCell, storeCell, NoJump])
    state hpc hactive

private theorem run_innerTail (state : NatState)
    (hpc : state.pc = 5 * (start + 230)) (hactive : state.halted = false) :
    natRun rom containing 116 state = runOps rom (innerTail start) state := by
  have hrun := run_branch_piece rom containing start hbound hcode 230
    (beforePair start ++ RawCandidatePairScan.programAt (start + 105)) (innerLead start)
    (outerTail start) (.jumpIfZero .flag .index)
    (by rw [← innerTail_split]; simp only [programAt, List.append_assoc])
    (by simp only [List.length_append, beforePair_length, RawCandidatePairScan.programAt_length])
    (by simp [innerLead, conditionScore, saveBestCard, saveParent, parentAddress, loadArray,
      arrayAddress, arrayBase, incrementWorkspace, storeWorkspace, loadWorkspace, loadCell, jumpTo, NoJump])
    state hpc hactive
  simpa only [innerLead_length, ← innerTail_split] using hrun

private theorem run_outerTail (state : NatState)
    (hpc : state.pc = 5 * (start + 346)) (hactive : state.halted = false) :
    natRun rom containing 15 state = runOps rom (outerTail start) state := by
  have hrun := run_branch_piece rom containing start hbound hcode 346
    (beforePair start ++ RawCandidatePairScan.programAt (start + 105) ++ innerTail start)
    (outerLead start) [] (.jumpIfZero .flag .index)
    (by rw [← outerTail_split]; simp only [programAt, List.append_nil, List.append_assoc])
    (by simp only [List.length_append, beforePair_length, RawCandidatePairScan.programAt_length, innerTail_length])
    (by simp [outerLead, incrementWorkspace, storeWorkspace, loadWorkspace, loadCell, jumpTo, NoJump])
    state hpc hactive
  simpa only [outerLead_length, ← outerTail_split] using hrun



end Containing

section PairCall

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 361 ≤ containing.length)
  (hcode : ∀ position < 361, containing.getD (start + position) paddingOp =
    (programAt start).getD position paddingOp)

include hbound hcode

private theorem pair_slice : start + 105 + 125 ≤ containing.length ∧
    ∀ position < 125, containing.getD ((start + 105) + position) paddingOp =
      (RawCandidatePairScan.programAt (start + 105)).getD position paddingOp := by
  constructor
  · omega
  · intro position hp
    have heq : programAt start = beforePair start ++ RawCandidatePairScan.programAt (start + 105) ++
        (innerTail start ++ outerTail start) := by simp only [programAt, List.append_assoc]
    have hlocal := getD_middle (beforePair start) (RawCandidatePairScan.programAt (start + 105))
      (innerTail start ++ outerTail start) position (by rw [RawCandidatePairScan.programAt_length]; exact hp)
    rw [beforePair_length, ← heq] at hlocal
    have hh := (hcode (105 + position) (by omega)).trans hlocal
    simpa only [Nat.add_assoc] using hh

private theorem pair_call (left right : Fin (full.length + q + 1)) (state : NatState)
    (hpc : state.pc = 5 * (start + 105)) (hactive : state.halted = false)
    (hl : state.heap 1 = left.val) (hr : state.heap 2 = right.val) :
    let L := (RawCandidateOrder.candidateSupports q full).getD left.val ∅
    let R := (RawCandidateOrder.candidateSupports q full).getD right.val ∅
    let result := natRun (rawIncidenceROM q full) containing
      (RawCandidatePairScan.totalSteps full.length left.val right.val q) state
    result.heap 5 = (L \ R).card ∧ result.heap 6 = (R \ L).card ∧
      (∀ address, 8 ≤ address → result.heap address = state.heap address) ∧
      result.pc = 5 * (start + 230) ∧ result.halted = false := by
  obtain ⟨hspan, hslice⟩ := pair_slice containing start hbound hcode
  have hs := RawCandidatePairScan.scan q full containing (start + 105) hspan hslice
    left right state hpc hactive hl hr
  dsimp only at hs ⊢
  rcases hs with ⟨_, _, _, h5, h6, hframe, hp, ha⟩
  refine ⟨h5, h6, ?_, ?_, ha⟩
  · intro address haddr
    exact hframe address (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · omega

end PairCall

def RowFrame (base count node : Nat) (before after : NatState) : Prop :=
  ∀ address, 8 ≤ address → address ≠ base + 2 → address ≠ base + 3 →
    address ≠ parentSlot base count node → after.heap address = before.heap address

theorem ProtectedAddress.ne_parent (base count nodes address node : Nat)
    (hp : ProtectedAddress base count nodes address) (hn : node < nodes) :
    address ≠ parentSlot base count node := by
  rcases hp with ⟨_, _, _, _, hregion⟩
  unfold parentSlot arraySlot at *
  rcases hregion with hregion | hregion <;> omega

private theorem select_score (value : Nat) (condition : Bool)
    (hcondition : value ≠ 0 ↔ condition = true) (yes no : Nat) :
    (if value = 0 then no else yes) = if condition then yes else no := by
  by_cases hv : value = 0
  · have hc : condition = false := by cases condition <;> simp_all
    simp only [hv, ite_true, hc, Bool.false_eq_true, ite_false]
  · have hc : condition = true := hcondition.mp hv
    simp only [hv, ite_false, hc, ite_true]

def innerIterationSteps (N q child later : Nat) : Nat :=
  157 + RawCandidatePairScan.totalSteps N child later q

theorem inner_iteration (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start : Nat) (hbound : start + 361 ≤ containing.length)
    (hcode : ∀ position < 361, containing.getD (start + position) paddingOp =
      (programAt start).getD position paddingOp)
    (base nodes : Nat) (order inverse : Nat → Nat) (state : NatState) (hlarge : 16 ≤ base)
    (tables : InputTables q full base nodes order inverse state)
    (node later : Nat) (hn : node < nodes) (hj : later < full.length + q + 1)
    (hnode : state.heap (base + 1) = node) (hlater : state.heap (base + 2) = later)
    (hpc : state.pc = 5 * (start + 64)) (hactive : state.halted = false) :
    let condition := RawCandidateParentScan.eligible q full (order node) later &&
      decide (RawCandidateStableOrder.candidateCard q full later < state.heap (base + 3))
    let result := natRun (rawIncidenceROM q full) containing
      (innerIterationSteps full.length q (order node) later) state
    InputTables q full base nodes order inverse result ∧ result.heap (base + 2) = later + 1 ∧
      result.heap (base + 3) = (if condition then RawCandidateStableOrder.candidateCard q full later else state.heap (base + 3)) ∧
      result.heap (parentSlot base (full.length + q + 1) node) =
        (if condition then inverse later else state.heap (parentSlot base (full.length + q + 1) node)) ∧
      RowFrame base (full.length + q + 1) node state result ∧
      result.pc = 5 * (start + 64) ∧ result.halted = false := by
  let rom := rawIncidenceROM q full
  let tested := runOps rom (testWorkspace 2 (start + 346)) state
  have ht := testWorkspace_effect rom 2 (start + 346) state
  have htestHeap : tested.heap = state.heap := ht.1
  have htestPc : tested.pc = 5 * (start + 77) := by
    have hp := ht.2.1
    rw [tables.base_cell, tables.count_cell, hlater] at hp
    simp only [Nat.sub_ne_zero_of_lt hj, ite_false, hpc] at hp
    change tested.pc = _ at hp
    omega
  have htestActive : tested.halted = false := ht.2.2.trans hactive
  let arguments := runOps rom pairArguments tested
  have hargHeap := pairArguments_heap rom tested
  rw [htestHeap, tables.base_cell, tables.count_cell, hnode, hlater, tables.ordered node hn] at hargHeap
  have hargAbove (address : Nat) (ha : 8 ≤ address) : arguments.heap address = state.heap address := by
    change (runOps rom pairArguments tested).heap address = _
    rw [hargHeap]
    simp [show address ≠ 1 by omega, show address ≠ 2 by omega]
  have argTables : InputTables q full base nodes order inverse arguments :=
    tables.transport q full base nodes order inverse state arguments hlarge
      (fun address hp => hargAbove address hp.1)
  have hargPc : arguments.pc = 5 * (start + 105) := by
    rw [show arguments = runOps rom pairArguments tested from rfl,
      runOps_pc rom pairArguments tested (by
        simp [pairArguments, loadArray, arrayAddress, arrayBase, loadWorkspace, loadCell, storeCell, NoJump]),
      pairArguments_length, htestPc]
    omega
  have hargActive : arguments.halted = false := by dsimp [arguments]; rw [runOps_halted, htestActive]
  let scanned := natRun rom containing (RawCandidatePairScan.totalSteps full.length (order node) later q) arguments
  have hs := pair_call q full containing start hbound hcode
    ⟨order node, tables.order_valid node hn⟩ ⟨later, hj⟩ arguments hargPc hargActive
    (by change (runOps rom pairArguments tested).heap 1 = _; rw [hargHeap]; simp)
    (by change (runOps rom pairArguments tested).heap 2 = _; rw [hargHeap]; simp)
  dsimp only at hs
  rcases hs with ⟨hs5, hs6, hsframe, hsp, hsa⟩
  have scanTables : InputTables q full base nodes order inverse scanned :=
    argTables.transport q full base nodes order inverse arguments scanned hlarge
      (fun address hp => hsframe address hp.1)
  have hscanAbove (address : Nat) (ha : 8 ≤ address) : scanned.heap address = state.heap address :=
    (hsframe address ha).trans (hargAbove address ha)
  have hscanNode : scanned.heap (base + 1) = node := (hscanAbove (base + 1) (by omega)).trans hnode
  have hscanLater : scanned.heap (base + 2) = later := (hscanAbove (base + 2) (by omega)).trans hlater
  have hbeforeBest : scanned.heap (base + 3) = state.heap (base + 3) := hscanAbove _ (by omega)
  have hbeforeParent : scanned.heap (parentSlot base (full.length + q + 1) node) =
      state.heap (parentSlot base (full.length + q + 1) node) := hscanAbove _ (by unfold parentSlot arraySlot; omega)
  let condition := RawCandidateParentScan.eligible q full (order node) later &&
    decide (RawCandidateStableOrder.candidateCard q full later < state.heap (base + 3))
  let value := score
    (RawCandidateParents.candidateSupport q full (order node) \ RawCandidateParents.candidateSupport q full later).card
    (RawCandidateParents.candidateSupport q full later \ RawCandidateParents.candidateSupport q full (order node)).card
    (bit (RawCandidateOrder.keepCandidate q full later)) (RawCandidateStableOrder.candidateCard q full later)
    (state.heap (base + 3))
  have hvalue : value ≠ 0 ↔ condition = true := score_candidates q full (order node) later _
  have hheap := innerTail_heap q full start base nodes order inverse scanned hlarge scanTables node later hscanNode hscanLater hj
  have hheap' : (runOps rom (innerTail start) scanned).heap =
      Function.update (Function.update (Function.update scanned.heap (base + 3)
        (if condition then RawCandidateStableOrder.candidateCard q full later else state.heap (base + 3)))
        (parentSlot base (full.length + q + 1) node)
        (if condition then inverse later else state.heap (parentSlot base (full.length + q + 1) node)))
        (base + 2) (later + 1) := by
    rw [hheap]
    unfold updatedHeap
    rw [show scanned.heap 5 = _ from hs5, show scanned.heap 6 = _ from hs6, hbeforeBest, hbeforeParent]
    change Function.update (Function.update (Function.update scanned.heap (base + 3)
      (if value = 0 then state.heap (base + 3) else RawCandidateStableOrder.candidateCard q full later))
      (parentSlot base (full.length + q + 1) node)
      (if value = 0 then state.heap (parentSlot base (full.length + q + 1) node) else inverse later)) _ _ = _
    rw [select_score value condition hvalue, select_score value condition hvalue]
  have hbody : natRun rom containing (innerIterationSteps full.length q (order node) later) state =
      runOps rom (innerTail start) scanned := by
    rw [show innerIterationSteps full.length q (order node) later =
        13 + (28 + (RawCandidatePairScan.totalSteps full.length (order node) later q + 116)) by
          unfold innerIterationSteps; omega,
      natRun_add, run_innerTest rom containing start hbound hcode state hpc hactive]
    change natRun rom containing (28 + (RawCandidatePairScan.totalSteps full.length (order node) later q + 116)) tested = _
    rw [natRun_add, run_pairArguments rom containing start hbound hcode tested htestPc htestActive, natRun_add]
    exact run_innerTail rom containing start hbound hcode scanned hsp hsa
  have hrow : RowFrame base (full.length + q + 1) node state (runOps rom (innerTail start) scanned) := by
    intro address ha h2 h3 hp
    rw [hheap']
    simp only [Function.update_of_ne h2, Function.update_of_ne hp, Function.update_of_ne h3]
    exact hscanAbove address ha
  have newTables : InputTables q full base nodes order inverse (runOps rom (innerTail start) scanned) :=
    tables.transport q full base nodes order inverse state _ hlarge (fun address hp =>
      hrow address hp.1 hp.2.2.1 hp.2.2.2.1
        (ProtectedAddress.ne_parent base _ nodes address node hp hn))
  have hc := innerTail_control rom start scanned
  dsimp only
  rw [hbody]
  refine ⟨newTables, ?_, ?_, ?_, hrow, hc.1, hc.2.trans hsa⟩
  · rw [hheap']
    simp
  · rw [hheap']
    simp [condition, show base + 3 ≠ parentSlot base (full.length + q + 1) node by unfold parentSlot arraySlot; omega]
  · rw [hheap']
    simp [condition, show parentSlot base (full.length + q + 1) node ≠ base + 2 by unfold parentSlot arraySlot; omega]

def innerScanSteps (N q child count : Nat) : Nat :=
  ∑ later ∈ Finset.range count, innerIterationSteps N q child later

theorem innerScanSteps_succ (N q child count : Nat) :
    innerScanSteps N q child (count + 1) = innerScanSteps N q child count + innerIterationSteps N q child count :=
  Finset.sum_range_succ _ _

theorem inner_scan_partial (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start : Nat) (hbound : start + 361 ≤ containing.length)
    (hcode : ∀ position < 361, containing.getD (start + position) paddingOp =
      (programAt start).getD position paddingOp)
    (base nodes : Nat) (order inverse : Nat → Nat) (state : NatState) (hlarge : 16 ≤ base)
    (tables : InputTables q full base nodes order inverse state) (node : Nat) (hn : node < nodes)
    (hnode : state.heap (base + 1) = node) (hlater : state.heap (base + 2) = 0)
    (hbest : state.heap (base + 3) = q + 1) (hparent : state.heap (parentSlot base (full.length + q + 1) node) = 0)
    (hpc : state.pc = 5 * (start + 64)) (hactive : state.halted = false)
    (count : Nat) (hwithin : count ≤ full.length + q + 1) :
    let result := natRun (rawIncidenceROM q full) containing (innerScanSteps full.length q (order node) count) state
    InputTables q full base nodes order inverse result ∧ result.heap (base + 2) = count ∧
      result.heap (base + 3) = RawCandidateParentScan.bestCard q full (order node) count ∧
      result.heap (parentSlot base (full.length + q + 1) node) = RawCandidateParentScan.bestEncoded q full inverse (order node) count ∧
      RowFrame base (full.length + q + 1) node state result ∧
      result.pc = 5 * (start + 64) ∧ result.halted = false := by
  revert hwithin
  induction count with
  | zero =>
    intro _
    simpa only [innerScanSteps, Finset.range_zero, Finset.sum_empty, natRun,
      RawCandidateParentScan.bestCard_zero, RawCandidateParentScan.bestEncoded_zero] using
      (show InputTables q full base nodes order inverse state ∧ state.heap (base + 2) = 0 ∧
        state.heap (base + 3) = q + 1 ∧ state.heap (parentSlot base (full.length + q + 1) node) = 0 ∧
        RowFrame base (full.length + q + 1) node state state ∧ state.pc = 5 * (start + 64) ∧ state.halted = false from
          ⟨tables, hlater, hbest, hparent, fun _ _ _ _ _ => rfl, hpc, hactive⟩)
  | succ count ih =>
    intro hwithin
    rcases ih (by omega) with ⟨ht, hj, hb, he, hframe, hp, ha⟩
    let previous := natRun (rawIncidenceROM q full) containing (innerScanSteps full.length q (order node) count) state
    have hnode' : previous.heap (base + 1) = node :=
      (hframe (base + 1) (by omega) (by omega) (by omega) (by unfold parentSlot arraySlot; omega)).trans hnode
    have hs := inner_iteration q full containing start hbound hcode base nodes order inverse previous hlarge ht
      node count hn (by omega) hnode' hj hp ha
    dsimp only at hs
    rw [show previous.heap (base + 3) = _ from hb,
      show previous.heap (parentSlot base (full.length + q + 1) node) = _ from he] at hs
    rcases hs with ⟨hst, hsj, hsb, hse, hsframe, hsp, hsa⟩
    have hrun : natRun (rawIncidenceROM q full) containing (innerScanSteps full.length q (order node) (count + 1)) state =
        natRun (rawIncidenceROM q full) containing (innerIterationSteps full.length q (order node) count) previous := by
      rw [innerScanSteps_succ, natRun_add]
    dsimp only
    rw [hrun]
    refine ⟨hst, hsj, ?_, ?_, ?_, hsp, hsa⟩
    · exact hsb.trans (RawCandidateParentScan.bestCard_succ q full (order node) count).symm
    · exact hse.trans (RawCandidateParentScan.bestEncoded_succ q full inverse (order node) count).symm
    · intro address haddr h2 h3 hpar
      exact (hsframe address haddr h2 h3 hpar).trans (hframe address haddr h2 h3 hpar)

def innerCompleteSteps (N q child : Nat) : Nat := innerScanSteps N q child (N + q + 1) + 13

theorem inner_scan (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start : Nat) (hbound : start + 361 ≤ containing.length)
    (hcode : ∀ position < 361, containing.getD (start + position) paddingOp =
      (programAt start).getD position paddingOp)
    (base nodes : Nat) (order inverse : Nat → Nat) (state : NatState) (hlarge : 16 ≤ base)
    (tables : InputTables q full base nodes order inverse state) (node : Nat) (hn : node < nodes)
    (hnode : state.heap (base + 1) = node) (hlater : state.heap (base + 2) = 0)
    (hbest : state.heap (base + 3) = q + 1) (hparent : state.heap (parentSlot base (full.length + q + 1) node) = 0)
    (hpc : state.pc = 5 * (start + 64)) (hactive : state.halted = false) :
    let result := natRun (rawIncidenceROM q full) containing (innerCompleteSteps full.length q (order node)) state
    InputTables q full base nodes order inverse result ∧
      result.heap (parentSlot base (full.length + q + 1) node) =
        RawCandidateParentScan.bestEncoded q full inverse (order node) (full.length + q + 1) ∧
      RowFrame base (full.length + q + 1) node state result ∧
      result.pc = 5 * (start + 346) ∧ result.halted = false := by
  let rom := rawIncidenceROM q full
  have hs := inner_scan_partial q full containing start hbound hcode base nodes order inverse state hlarge tables
    node hn hnode hlater hbest hparent hpc hactive (full.length + q + 1) le_rfl
  dsimp only at hs
  rcases hs with ⟨ht, hj, _, he, hframe, hp, ha⟩
  let previous := natRun rom containing (innerScanSteps full.length q (order node) (full.length + q + 1)) state
  have hx := testWorkspace_effect rom 2 (start + 346) previous
  have hbody : natRun rom containing (innerCompleteSteps full.length q (order node)) state =
      runOps rom (testWorkspace 2 (start + 346)) previous := by
    rw [innerCompleteSteps, natRun_add]
    exact run_innerTest rom containing start hbound hcode previous hp ha
  have newTables : InputTables q full base nodes order inverse (runOps rom (testWorkspace 2 (start + 346)) previous) :=
    ht.transport q full base nodes order inverse previous _ hlarge
      (fun address _ => congrFun hx.1 address)
  dsimp only
  rw [hbody]
  refine ⟨newTables, (congrFun hx.1 _).trans he, ?_, ?_, hx.2.2.trans ha⟩
  · intro address haddr h2 h3 hpar
    exact (congrFun hx.1 address).trans (hframe address haddr h2 h3 hpar)
  · have hxp := hx.2.1
    rw [ht.base_cell, ht.count_cell, show previous.heap (base + 2) = full.length + q + 1 from hj,
      Nat.sub_self] at hxp
    exact hxp

theorem initialize_child (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start : Nat) (hbound : start + 361 ≤ containing.length)
    (hcode : ∀ position < 361, containing.getD (start + position) paddingOp =
      (programAt start).getD position paddingOp)
    (base nodes : Nat) (order inverse : Nat → Nat) (state : NatState) (hlarge : 16 ≤ base)
    (tables : InputTables q full base nodes order inverse state) (node : Nat) (hn : node < nodes)
    (hnode : state.heap (base + 1) = node) (hpc : state.pc = 5 * (start + 27)) (hactive : state.halted = false) :
    let result := natRun (rawIncidenceROM q full) containing 37 state
    InputTables q full base nodes order inverse result ∧ result.heap (base + 1) = node ∧
      result.heap (base + 2) = 0 ∧ result.heap (base + 3) = q + 1 ∧
      result.heap (parentSlot base (full.length + q + 1) node) = 0 ∧
      RowFrame base (full.length + q + 1) node state result ∧
      result.pc = 5 * (start + 64) ∧ result.halted = false := by
  let rom := rawIncidenceROM q full
  let result := runOps rom initializeChild state
  have hheap := initializeChild_heap q full base state tables.base_cell hlarge
  rw [tables.count_cell, hnode] at hheap
  have hframe : RowFrame base (full.length + q + 1) node state result := by
    intro address ha h2 h3 hp
    change (runOps rom initializeChild state).heap address = _
    rw [hheap]
    simp only [Function.update_of_ne h2, Function.update_of_ne hp, Function.update_of_ne h3]
  have newTables : InputTables q full base nodes order inverse result :=
    tables.transport q full base nodes order inverse state result hlarge (fun address hp =>
      hframe address hp.1 hp.2.2.1 hp.2.2.2.1 (ProtectedAddress.ne_parent base _ nodes address node hp hn))
  have hresultPc : result.pc = 5 * (start + 64) := by
    rw [show result = runOps rom initializeChild state from rfl,
      runOps_pc rom initializeChild state (by
        simp [initializeChild, initializeBestCard, initializeParent, parentAddress, arrayAddress,
          arrayBase, setWorkspace, storeWorkspace, loadWorkspace, loadCell, NoJump]), initializeChild_length, hpc]
    omega
  dsimp only
  rw [run_initializeChild rom containing start hbound hcode state hpc hactive]
  refine ⟨newTables, ?_, ?_, ?_, ?_, hframe, hresultPc, (runOps_halted _ _ _).trans hactive⟩
  · rw [hheap]
    simpa [show base + 1 ≠ parentSlot base (full.length + q + 1) node by unfold parentSlot arraySlot; omega] using hnode
  · rw [hheap]
    simp
  · rw [hheap]
    simp [show base + 3 ≠ parentSlot base (full.length + q + 1) node by unfold parentSlot arraySlot; omega]
  · rw [hheap]
    simp [show parentSlot base (full.length + q + 1) node ≠ base + 2 by unfold parentSlot arraySlot; omega]

theorem outerTail_heap (rom : PhysicalROM) (start : Nat) (state : NatState) :
    (runOps rom (outerTail start) state).heap =
      Function.update state.heap (state.heap 8 + 1) (state.heap (state.heap 8 + 1) + 1) := by
  rw [outerTail, runOps_append, jumpTo_heap, incrementWorkspace_heap]

def OuterFrame (base count node : Nat) (before after : NatState) : Prop :=
  ∀ address, 8 ≤ address → address ≠ base + 1 → address ≠ base + 2 → address ≠ base + 3 →
    address ≠ parentSlot base count node → after.heap address = before.heap address

def outerIterationSteps (N q child : Nat) : Nat := 73 + innerCompleteSteps N q child

theorem outer_iteration (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start : Nat) (hbound : start + 361 ≤ containing.length)
    (hcode : ∀ position < 361, containing.getD (start + position) paddingOp =
      (programAt start).getD position paddingOp)
    (base nodes : Nat) (order inverse : Nat → Nat) (state : NatState) (hlarge : 16 ≤ base)
    (tables : InputTables q full base nodes order inverse state) (node : Nat) (hn : node < nodes)
    (hnode : state.heap (base + 1) = node) (hpc : state.pc = 5 * (start + 6)) (hactive : state.halted = false) :
    let result := natRun (rawIncidenceROM q full) containing (outerIterationSteps full.length q (order node)) state
    InputTables q full base nodes order inverse result ∧ result.heap (base + 1) = node + 1 ∧
      result.heap (parentSlot base (full.length + q + 1) node) =
        RawCandidateParentScan.bestEncoded q full inverse (order node) (full.length + q + 1) ∧
      OuterFrame base (full.length + q + 1) node state result ∧
      result.pc = 5 * (start + 6) ∧ result.halted = false := by
  let rom := rawIncidenceROM q full
  let tested := runOps rom (outerTest (start + 361)) state
  have ht := outerTest_values rom (start + 361) state
  have htestHeap : tested.heap = state.heap := ht.1
  have htestPc : tested.pc = 5 * (start + 27) := by
    have hp := ht.2.1
    rw [tables.base_cell, tables.count_cell, tables.node_count, hnode] at hp
    simp only [Nat.sub_ne_zero_of_lt hn, ite_false, hpc] at hp
    change tested.pc = _ at hp
    omega
  have htestActive : tested.halted = false := ht.2.2.trans hactive
  have testTables : InputTables q full base nodes order inverse tested :=
    tables.transport q full base nodes order inverse state tested hlarge
      (fun address _ => congrFun htestHeap address)
  let prepared := natRun rom containing 37 tested
  have hi := initialize_child q full containing start hbound hcode base nodes order inverse tested hlarge
    testTables node hn (by rw [htestHeap]; exact hnode) htestPc htestActive
  dsimp only at hi
  rcases hi with ⟨hit, hin, hij, hib, hipar, hiframe, hip, hia⟩
  let scanned := natRun rom containing (innerCompleteSteps full.length q (order node)) prepared
  have hs := inner_scan q full containing start hbound hcode base nodes order inverse prepared hlarge hit
    node hn hin hij hib hipar hip hia
  dsimp only at hs
  rcases hs with ⟨hst, hse, hsframe, hsp, hsa⟩
  have hscanNode : scanned.heap (base + 1) = node :=
    (hsframe (base + 1) (by omega) (by omega) (by omega) (by unfold parentSlot arraySlot; omega)).trans hin
  have hrow : RowFrame base (full.length + q + 1) node state scanned := by
    intro address ha h2 h3 hpar
    exact (hsframe address ha h2 h3 hpar).trans
      ((hiframe address ha h2 h3 hpar).trans (congrFun htestHeap address))
  have hheap := outerTail_heap rom start scanned
  rw [hst.base_cell, hscanNode] at hheap
  have newTables : InputTables q full base nodes order inverse (runOps rom (outerTail start) scanned) :=
    hst.transport q full base nodes order inverse scanned _ hlarge (fun address hp => by
      rw [hheap]
      exact Function.update_of_ne hp.2.1 _ _)
  have hframe : OuterFrame base (full.length + q + 1) node state (runOps rom (outerTail start) scanned) := by
    intro address ha h1 h2 h3 hpar
    rw [hheap, Function.update_of_ne h1]
    exact hrow address ha h2 h3 hpar
  have hbody : natRun rom containing (outerIterationSteps full.length q (order node)) state =
      runOps rom (outerTail start) scanned := by
    rw [show outerIterationSteps full.length q (order node) =
        21 + (37 + (innerCompleteSteps full.length q (order node) + 15)) by unfold outerIterationSteps; omega,
      natRun_add, run_outerTest rom containing start hbound hcode state hpc hactive]
    change natRun rom containing (37 + (innerCompleteSteps full.length q (order node) + 15)) tested = _
    rw [natRun_add]
    change natRun rom containing (innerCompleteSteps full.length q (order node) + 15) prepared = _
    rw [natRun_add]
    exact run_outerTail rom containing start hbound hcode scanned hsp hsa
  have hc := outerTail_control rom start scanned
  dsimp only
  rw [hbody]
  refine ⟨newTables, ?_, ?_, hframe, hc.1, hc.2.trans hsa⟩
  · rw [hheap]
    simp
  · rw [hheap]
    simpa [show parentSlot base (full.length + q + 1) node ≠ base + 1 by unfold parentSlot arraySlot; omega] using hse

def outerScanSteps (N q : Nat) (order : Nat → Nat) (count : Nat) : Nat :=
  ∑ node ∈ Finset.range count, outerIterationSteps N q (order node)

theorem outerScanSteps_succ (N q : Nat) (order : Nat → Nat) (count : Nat) :
    outerScanSteps N q order (count + 1) = outerScanSteps N q order count + outerIterationSteps N q (order count) :=
  Finset.sum_range_succ _ _

theorem outer_scan_partial (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start : Nat) (hbound : start + 361 ≤ containing.length)
    (hcode : ∀ position < 361, containing.getD (start + position) paddingOp =
      (programAt start).getD position paddingOp)
    (base nodes : Nat) (order inverse : Nat → Nat) (state : NatState) (hlarge : 16 ≤ base)
    (tables : InputTables q full base nodes order inverse state)
    (hnode : state.heap (base + 1) = 0) (hpc : state.pc = 5 * (start + 6)) (hactive : state.halted = false)
    (count : Nat) (hwithin : count ≤ nodes) :
    let result := natRun (rawIncidenceROM q full) containing (outerScanSteps full.length q order count) state
    InputTables q full base nodes order inverse result ∧ result.heap (base + 1) = count ∧
      (∀ node < count, result.heap (parentSlot base (full.length + q + 1) node) =
        RawCandidateParentScan.bestEncoded q full inverse (order node) (full.length + q + 1)) ∧
      (∀ address, ProtectedAddress base (full.length + q + 1) nodes address → result.heap address = state.heap address) ∧
      result.pc = 5 * (start + 6) ∧ result.halted = false := by
  revert hwithin
  induction count with
  | zero =>
    intro _
    simpa only [outerScanSteps, Finset.range_zero, Finset.sum_empty, natRun] using
      (show InputTables q full base nodes order inverse state ∧ state.heap (base + 1) = 0 ∧
        (∀ node < 0, state.heap (parentSlot base (full.length + q + 1) node) =
          RawCandidateParentScan.bestEncoded q full inverse (order node) (full.length + q + 1)) ∧
        (∀ address, ProtectedAddress base (full.length + q + 1) nodes address → state.heap address = state.heap address) ∧
        state.pc = 5 * (start + 6) ∧ state.halted = false from
          ⟨tables, hnode, fun _ hn => by omega, fun _ _ => rfl, hpc, hactive⟩)
  | succ count ih =>
    intro hwithin
    rcases ih (by omega) with ⟨ht, hk, hparents, hframe, hp, ha⟩
    let previous := natRun (rawIncidenceROM q full) containing (outerScanSteps full.length q order count) state
    have hs := outer_iteration q full containing start hbound hcode base nodes order inverse previous hlarge ht
      count (by omega) hk hp ha
    dsimp only at hs
    rcases hs with ⟨hst, hsk, hsp, hsframe, hspc, hsa⟩
    have hrun : natRun (rawIncidenceROM q full) containing (outerScanSteps full.length q order (count + 1)) state =
        natRun (rawIncidenceROM q full) containing (outerIterationSteps full.length q (order count)) previous := by
      rw [outerScanSteps_succ, natRun_add]
    dsimp only
    rw [hrun]
    refine ⟨hst, hsk, ?_, ?_, hspc, hsa⟩
    · intro node hn
      by_cases heq : node = count
      · subst node
        exact hsp
      · have hless : node < count := by omega
        exact (hsframe (parentSlot base (full.length + q + 1) node)
          (by unfold parentSlot arraySlot; omega) (by unfold parentSlot arraySlot; omega)
          (by unfold parentSlot arraySlot; omega) (by unfold parentSlot arraySlot; omega)
          (by unfold parentSlot arraySlot; omega)).trans (hparents node hless)
    · intro address hout
      exact (hsframe address hout.1 hout.2.1 hout.2.2.1 hout.2.2.2.1
        (ProtectedAddress.ne_parent base _ nodes address count hout (by omega))).trans (hframe address hout)

def totalSteps (N q nodes : Nat) (order : Nat → Nat) : Nat := 6 + outerScanSteps N q order nodes + 21

/-- A complete runtime parent scan.  Every comparison uses the actual q-bit
pair block and the immutable preceding-phase tables, rather than a supplied
parent value.  The result remains active for the next constructor phase. -/
theorem parents (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start : Nat) (hbound : start + 361 ≤ containing.length)
    (hcode : ∀ position < 361, containing.getD (start + position) paddingOp =
      (programAt start).getD position paddingOp)
    (base nodes : Nat) (order inverse : Nat → Nat) (state : NatState) (hlarge : 16 ≤ base)
    (tables : InputTables q full base nodes order inverse state)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false) :
    let result := natRun (rawIncidenceROM q full) containing (totalSteps full.length q nodes order) state
    InputTables q full base nodes order inverse result ∧ result.heap (base + 1) = nodes ∧
      (∀ node < nodes, result.heap (parentSlot base (full.length + q + 1) node) =
        RawCandidateParentScan.bestEncoded q full inverse (order node) (full.length + q + 1)) ∧
      (∀ address, ProtectedAddress base (full.length + q + 1) nodes address → result.heap address = state.heap address) ∧
      result.pc = 5 * (start + 361) ∧ result.halted = false := by
  let rom := rawIncidenceROM q full
  let initialized := runOps rom (setWorkspace 1 0) state
  have hinitHeap : initialized.heap = Function.update state.heap (base + 1) 0 := by
    simpa only [tables.base_cell] using setWorkspace_heap rom 1 0 state
  have initTables : InputTables q full base nodes order inverse initialized :=
    tables.transport q full base nodes order inverse state initialized hlarge (fun address hp => by
      rw [hinitHeap]
      exact Function.update_of_ne hp.2.1 _ _)
  have hik : initialized.heap (base + 1) = 0 := by rw [hinitHeap]; simp
  have hip : initialized.pc = 5 * (start + 6) := by
    rw [show initialized = runOps rom (setWorkspace 1 0) state from rfl,
      runOps_pc rom (setWorkspace 1 0) state (by simp [setWorkspace, storeWorkspace, loadCell, NoJump]),
      setWorkspace_length, hpc]
    omega
  have hia : initialized.halted = false := by dsimp [initialized]; rw [runOps_halted, hactive]
  have hs := outer_scan_partial q full containing start hbound hcode base nodes order inverse initialized hlarge initTables
    hik hip hia nodes le_rfl
  dsimp only at hs
  rcases hs with ⟨ht, hk, hparents, hframe, hp, ha⟩
  let previous := natRun rom containing (outerScanSteps full.length q order nodes) initialized
  have hx := outerTest_values rom (start + 361) previous
  have hbody : natRun rom containing (totalSteps full.length q nodes order) state =
      runOps rom (outerTest (start + 361)) previous := by
    rw [show totalSteps full.length q nodes order = 6 + (outerScanSteps full.length q order nodes + 21) by
      unfold totalSteps; omega, natRun_add, run_init rom containing start hbound hcode state hpc hactive]
    rw [natRun_add]
    exact run_outerTest rom containing start hbound hcode previous hp ha
  have newTables : InputTables q full base nodes order inverse (runOps rom (outerTest (start + 361)) previous) :=
    ht.transport q full base nodes order inverse previous _ hlarge (fun address _ => congrFun hx.1 address)
  dsimp only
  rw [hbody]
  refine ⟨newTables, (congrFun hx.1 (base + 1)).trans hk, ?_, ?_, ?_, hx.2.2.trans ha⟩
  · intro node hn
    exact (congrFun hx.1 _).trans (hparents node hn)
  · intro address hout
    rw [congrFun hx.1 address, hframe address hout, hinitHeap]
    exact Function.update_of_ne hout.2.1 _ _
  · have hxp := hx.2.1
    rw [ht.base_cell, ht.count_cell, ht.node_count, show previous.heap (base + 1) = nodes from hk,
      Nat.sub_self] at hxp
    exact hxp

theorem innerIterationSteps_le (N q child later : Nat) : innerIterationSteps N q child later ≤ 87 * q + 180 := by
  have h := RawCandidatePairScan.totalSteps_le N child later q
  unfold innerIterationSteps
  omega

theorem innerScanSteps_le (N q child count : Nat) : innerScanSteps N q child count ≤ count * (87 * q + 180) := by
  unfold innerScanSteps
  calc
    _ ≤ ∑ _later ∈ Finset.range count, (87 * q + 180) :=
      Finset.sum_le_sum (fun later _ => innerIterationSteps_le N q child later)
    _ = _ := by simp [Nat.mul_comm]

theorem outerIterationSteps_le (N q child : Nat) : outerIterationSteps N q child ≤ 266 * (N + q + 2) * (q + 1) := by
  have h := innerScanSteps_le N q child (N + q + 1)
  unfold outerIterationSteps innerCompleteSteps
  nlinarith

theorem totalSteps_le (N q nodes : Nat) (order : Nat → Nat) :
    totalSteps N q nodes order ≤ 512 * (nodes + 1) * (N + q + 2) * (q + 1) := by
  have hsum : outerScanSteps N q order nodes ≤ nodes * (266 * (N + q + 2) * (q + 1)) := by
    unfold outerScanSteps
    calc
      _ ≤ ∑ _node ∈ Finset.range nodes, (266 * (N + q + 2) * (q + 1)) :=
        Finset.sum_le_sum (fun node _ => outerIterationSteps_le N q (order node))
      _ = _ := by simp [Nat.mul_comm]
  unfold totalSteps
  nlinarith

def observedOrder (q : Nat) (full : List (Finset (Fin q))) (base : Nat) (state : NatState) (node : Nat) : Nat :=
  state.heap (arraySlot base (full.length + q + 1) 2 node)

def observedInverse (q : Nat) (full : List (Finset (Fin q))) (base : Nat) (state : NatState) (candidate : Nat) : Nat :=
  state.heap (arraySlot base (full.length + q + 1) 3 candidate)

theorem prepared_nodes_eq_retained (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    (prepareNormalization q full).indexed.nodes.size = (RawCandidateOrder.retainedCandidateIndices q full).length :=
  (RawCandidateRankPositions.sortedCandidateIndices_length q full hq).symm.trans
    (RawCandidateStableOrder.sortedCandidateIndices_perm q full).length_eq

/-- Extract only the preceding machine's real table data.  This contains
no parent value, argmin answer, or future execution assumption. -/
theorem InputTables.of_sorted (q : Nat) (full : List (Finset (Fin q))) (base sortStart : Nat)
    (before state : NatState) (sorted : RawCandidateOrderingRAM.Sorted q full base sortStart before state)
    (hq : 0 < q) :
    InputTables q full base (RawCandidateOrder.retainedCandidateIndices q full).length
      (observedOrder q full base state) (observedInverse q full base state) state := by
  refine ⟨sorted.returned.base_cell, sorted.returned.count_cell, sorted.node_count, ?_,
    sorted.tables.1, sorted.tables.2, ?_, ?_, ?_⟩
  · change ((List.range (RawCandidateOrder.candidateSupports q full).length).filter
      (RawCandidateOrder.keepSupport (RawCandidateOrder.candidateSupports q full))).length ≤ full.length + q + 1
    calc
      _ ≤ (List.range (RawCandidateOrder.candidateSupports q full).length).length := List.length_filter_le _ _
      _ = _ := by rw [List.length_range, RawCandidateOrder.candidateSupports_length]
  · intro node _
    rfl
  · intro node hn
    obtain ⟨candidate, hmem, hstored, _, _⟩ :=
      RawCandidateOrderingRAM.Sorted.support_at_position q full base sortStart before state sorted hq node hn
    change state.heap (arraySlot base (full.length + q + 1) 2 node) < _
    rw [hstored]
    exact ((RawCandidateOrder.retainedCandidateIndices_mem_iff q full candidate).mp hmem).1
  · intro candidate _
    rfl

theorem observedInverse_of_sorted (q : Nat) (full : List (Finset (Fin q))) (base sortStart : Nat)
    (before state : NatState) (sorted : RawCandidateOrderingRAM.Sorted q full base sortStart before state) :
    ∀ candidate ∈ RawCandidateOrder.retainedCandidateIndices q full,
      observedInverse q full base state candidate = RawCandidateRankPositions.lessCount q full candidate + 1 := by
  intro candidate hmem
  obtain ⟨hbound, hkeep⟩ := (RawCandidateOrder.retainedCandidateIndices_mem_iff q full candidate).mp hmem
  have h := sorted.output.inverse candidate hbound
  simpa only [observedInverse, hkeep, ite_true] using h

theorem observedOrder_support_of_sorted (q : Nat) (full : List (Finset (Fin q))) (base sortStart : Nat)
    (before state : NatState) (sorted : RawCandidateOrderingRAM.Sorted q full base sortStart before state)
    (hq : 0 < q) (child : (prepareNormalization q full).indexed.NodeId) :
    RawCandidateParents.candidateSupport q full (observedOrder q full base state child.val) =
      (prepareNormalization q full).indexed.decode child := by
  have hp : child.val < (RawCandidateOrder.retainedCandidateIndices q full).length := by
    rw [← prepared_nodes_eq_retained q full hq]
    exact child.isLt
  obtain ⟨candidate, _, hstored, _, hsupport⟩ :=
    RawCandidateOrderingRAM.Sorted.support_at_position q full base sortStart before state sorted hq child.val hp
  unfold observedOrder
  rw [hstored]
  change (RawCandidateOrder.candidateSupports q full).getD candidate ∅ = _
  calc
    _ = (prepareNormalization q full).order.getD child.val ∅ := hsupport.symm
    _ = (prepareNormalization q full).indexed.decode child := by
      rw [List.getD_eq_getElem _ _ (show child.val < (prepareNormalization q full).order.length from child.isLt)]
      change (prepareNormalization q full).order[child.val] = (prepareNormalization q full).order.toArray[child.val]
      simp only [List.getElem_toArray]

/-- Actual sorted table data plus actual parent-loop execution gives the
exact original prepared parent encoding, without a parent-correctness premise. -/
theorem parents_prepared (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (containing : List PackingOp) (start : Nat) (hbound : start + 361 ≤ containing.length)
    (hcode : ∀ position < 361, containing.getD (start + position) paddingOp =
      (programAt start).getD position paddingOp)
    (base sortStart : Nat) (before state : NatState) (hlarge : 16 ≤ base)
    (sorted : RawCandidateOrderingRAM.Sorted q full base sortStart before state)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false) :
    let nodes := (RawCandidateOrder.retainedCandidateIndices q full).length
    let result := natRun (rawIncidenceROM q full) containing
      (totalSteps full.length q nodes (observedOrder q full base state)) state
    ∀ child : (prepareNormalization q full).indexed.NodeId,
      result.heap (parentSlot base (full.length + q + 1) child.val) =
        encodedNode (prepareNormalization q full).indexed ((prepareNormalization q full).indexed.parents.get child) := by
  have tables := InputTables.of_sorted q full base sortStart before state sorted hq
  have hs := parents q full containing start hbound hcode base
    (RawCandidateOrder.retainedCandidateIndices q full).length
    (observedOrder q full base state) (observedInverse q full base state) state hlarge tables hpc hactive
  dsimp only at hs ⊢
  intro child
  have hc := hs.2.2.1 child.val (by rw [← prepared_nodes_eq_retained q full hq]; exact child.isLt)
  exact hc.trans (RawCandidateParentEncoding.bestEncoded_full_of_inverse q full hq
    (observedInverse q full base state) (observedInverse_of_sorted q full base sortStart before state sorted)
    child (observedOrder q full base state child.val)
    (observedOrder_support_of_sorted q full base sortStart before state sorted hq child))

end PaperProofs.Structure.LaminarTree.RawCandidateParentRAM
