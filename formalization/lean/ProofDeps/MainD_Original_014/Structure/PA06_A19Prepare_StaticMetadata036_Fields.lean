module

public import Structure.PA06_A19Prepare_StaticMetadata036
public import Structure.PA06_A19Prepare_BankNodeBit022

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Private actual scalar producers for the remaining five metadata segments.
The original raw card/ord cells are copied007 data; metadata output addresses
are computed from the permanent t/base/N cells. These short blocks are NOT
presented as the complete nested stage/leaf/tool loops. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (preparedSize mass Frame Protected)

def rawCardAddress (CB candidate : Nat) : Nat := CB + 532 + candidate
def rawOrdAddress (CB M node : Nat) : Nat := CB + 532 + 2 * M + node

/-- Actual copied raw inputs, not supplied cardinality/metadata answers. -/
structure RawCardData (q : Nat) (full : List (Finset (Fin q))) (CB : Nat) (state : NatState) : Prop where
  mass_cell : state.heap (CB + 528) = mass q full
  cards : ∀ candidate : Fin (mass q full),
    state.heap (rawCardAddress CB candidate.val) = RawCandidateStableOrder.candidateCard q full candidate.val
  ordered : ∀ node : (prepareNormalization q full).indexed.NodeId,
    ∃ candidate : Fin (mass q full),
      state.heap (rawOrdAddress CB (mass q full) node.val) = candidate.val ∧
      RawCandidateParents.candidateSupport q full candidate.val = (prepareNormalization q full).indexed.decode node

theorem rawCardData_of_copiedCache {q : Nat} {full : List (Finset (Fin q))}
    {before after : NatState} (entry : PA06A19PrepareCompactCandidates007.ParentEntry q full before)
    (hq : 0 < q) (CB : Nat)
    (copied : ∀ address < PA06A19PrepareControlBank017.cacheLength full.length q,
      after.heap (CB + 512 + address) = before.heap address) : RawCardData q full CB after := by
  obtain ⟨order, inverse, tables, support⟩ := entry.tables
  constructor
  · have h := copied 16 (by unfold PA06A19PrepareControlBank017.cacheLength; omega)
    have he : CB + 512 + 16 = CB + 528 := by omega
    rw [he, entry.count_cell] at h
    exact h
  · intro candidate
    let source := RawCandidateOrderingRAM.arraySlot 16 (mass q full) 0 candidate.val
    have hi : candidate.val < full.length + q + 1 := candidate.isLt
    have h := copied source (by
      exact PA06A19PrepareCompactCandidates007.candidate_array_address_lt full.length q 0 candidate.val
        (by decide) hi)
    have he : CB + 512 + source = rawCardAddress CB candidate.val := by
      unfold source RawCandidateOrderingRAM.arraySlot rawCardAddress
      omega
    rw [he, tables.cards candidate.val hi] at h
    exact h
  · intro node
    have hn : node.val < (RawCandidateOrder.retainedCandidateIndices q full).length := by
      rw [← RawCandidateParentRAM.prepared_nodes_eq_retained q full hq]
      exact node.isLt
    let candidate : Fin (mass q full) := ⟨order node.val, tables.order_valid node.val hn⟩
    refine ⟨candidate, ?_, support node⟩
    let source := RawCandidateOrderingRAM.arraySlot 16 (mass q full) 2 node.val
    have hi : node.val < full.length + q + 1 := node.isLt.trans_le (prepared_indexed_size_le q full)
    have h := copied source (by
      exact PA06A19PrepareCompactCandidates007.candidate_array_address_lt full.length q 2 node.val
        (by decide) hi)
    have he : CB + 512 + source = rawOrdAddress CB (mass q full) node.val := by
      unfold source RawCandidateOrderingRAM.arraySlot rawOrdAddress
      omega
    rw [he, tables.ordered node.val hn] at h
    exact h

/-- The true023 frame protects all raw card/ord cells. No provenance is
lost when the independently built linear children output is added. -/
theorem RawCardData.of_children_frame {q : Nat} {full : List (Finset (Fin q))}
    {CB : Nat} {before after : NatState} (data : RawCardData q full CB before)
    (frame : Frame q full CB before after) : RawCardData q full CB after := by
  have ht : preparedSize q full ≤ mass q full := prepared_indexed_size_le q full
  constructor
  · rw [frame _ (by
      unfold Protected PA06A19PrepareChildrenCache023.childrenBase PA06A19PrepareChildrenCache023.degreeBase
      constructor <;> omega)]
    exact data.mass_cell
  · intro candidate
    have hc := candidate.isLt
    rw [frame _ (by
      unfold Protected rawCardAddress PA06A19PrepareChildrenCache023.childrenBase
        PA06A19PrepareChildrenCache023.degreeBase
      constructor <;> omega)]
    exact data.cards candidate
  · intro node
    have hn : node.val < preparedSize q full := node.isLt
    obtain ⟨candidate, hord, hsupport⟩ := data.ordered node
    refine ⟨candidate, ?_, hsupport⟩
    rw [frame _ (by
      unfold Protected rawOrdAddress PA06A19PrepareChildrenCache023.childrenBase
        PA06A19PrepareChildrenCache023.degreeBase
      constructor <;> omega)]
    exact hord

/-- Get the same prepared cardinality from the original ord→card cache. -/
theorem rawCardData_node_card (q : Nat) (full : List (Finset (Fin q))) (CB : Nat) (state : NatState)
    (data : RawCardData q full CB state) (node : (prepareNormalization q full).indexed.NodeId) :
    state.heap (rawCardAddress CB (state.heap (rawOrdAddress CB (mass q full) node.val))) =
      (prepareNormalization q full).indexed.metadata.cardinalities.get node := by
  obtain ⟨candidate, hord, hsupport⟩ := data.ordered node
  rw [hord, data.cards candidate, metadata_cardinality]
  exact congrArg Finset.card hsupport

def cardProgram : List PackingOp :=
  [.base (.base (.constant .index 528)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .total .index)), .base (.base (.constant .value 2)),
   .arithmetic .multiply .total .total .value, .base (.base (.constant .index 532)),
   .base (.base (.add .index .address .index)), .base (.base (.add .index .index .total)),
   .base (.base (.add .index .index .old)), .base (.base (.loadHeap .value .index)),
   .base (.base (.constant .index 532)), .base (.base (.add .index .address .index)),
   .base (.base (.add .index .index .value)), .base (.base (.loadHeap .value .index))]

def internalFlag : List PackingOp :=
  [.base (.base (.constant .total 1)), .base (.subtract .value .value .total),
   .base (.base (.minimum .value .value .total))]

theorem cardProgram_length : cardProgram.length = 14 := rfl
theorem internalFlag_length : internalFlag.length = 3 := rfl

theorem cardProgram_noJump : ∀ op ∈ cardProgram, NoJump op := by simp [cardProgram, NoJump]

theorem cardProgram_effect (rom : PhysicalROM) (CB M node candidate value : Nat) (state : NatState)
    (hCB : state.register .address = CB) (hM : state.heap (CB + 528) = M)
    (hn : state.register .old = node) (ho : state.heap (rawOrdAddress CB M node) = candidate)
    (hv : state.heap (rawCardAddress CB candidate) = value) :
    let after := runOps rom cardProgram state
    after.register .value = value ∧ after.register .address = CB ∧ after.register .old = node ∧
      after.register .fresh = state.register .fresh ∧ after.register .flag = state.register .flag ∧ after.heap = state.heap := by
  simp [cardProgram, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
    hCB, hM, hn, rawOrdAddress, rawCardAddress, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] at ho hv ⊢
  rw [ho]
  simpa only [Nat.add_comm] using hv

theorem internalFlag_value (rom : PhysicalROM) (state : NatState) :
    (runOps rom internalFlag state).register .value = bit (decide (1 < state.register .value)) := by
  change min (state.register .value - 1) 1 = bit (decide (1 < state.register .value))
  by_cases h : 1 < state.register .value
  · have he : min (state.register .value - 1) 1 = 1 := by omega
    rw [he]
    simp [h, bit]
  · have he : min (state.register .value - 1) 1 = 0 := by omega
    rw [he]
    simp [h, bit]

inductive Field where
  | cardinality | internal | leaf | stage | tool
  deriving DecidableEq

def fieldFactor : Field → Nat
  | .cardinality => 3 | .internal => 4 | .leaf => 5 | .stage | .tool => 6

def fieldExtra (N : Nat) : Field → Nat
  | .tool => N | _ => 0

def fieldAddress (P N t : Nat) (field : Field) (index : Nat) : Nat :=
  6 + P + fieldFactor field * t + fieldExtra N field + index

def fieldPointerLead (field : Field) : List PackingOp :=
  [.base (.base (.constant .index 2)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .total .index)), .base (.base (.constant .fresh (fieldFactor field))),
   .arithmetic .multiply .total .total .fresh, .base (.base (.constant .index 6)),
   .base (.base (.add .index .address .index)), .base (.base (.loadHeap .fresh .index)),
   .base (.base (.add .total .total .fresh)), .base (.base (.constant .fresh 2)),
   .base (.base (.add .total .total .fresh))]

def fieldPointerExtra : Field → List PackingOp
  | .tool => [.base (.base (.constant .index 0)), .base (.base (.add .index .address .index)),
      .base (.base (.loadHeap .fresh .index)), .base (.base (.add .total .total .fresh))]
  | _ => []

def fieldPointer (field : Field) : List PackingOp :=
  fieldPointerLead field ++ fieldPointerExtra field ++ [.base (.base (.add .total .total .old))]

def storeField (field : Field) : List PackingOp :=
  fieldPointer field ++ [.base (.base (.storeHeap .total .value))]

theorem fieldPointer_length (field : Field) : (fieldPointer field).length = if field = .tool then 16 else 12 := by
  cases field <;> rfl

theorem storeField_length (field : Field) : (storeField field).length = if field = .tool then 17 else 13 := by
  cases field <;> rfl

theorem fieldPointer_noJump (field : Field) : ∀ op ∈ fieldPointer field, NoJump op := by
  cases field <;> simp [fieldPointer, fieldPointerLead, fieldPointerExtra, NoJump]

theorem storeField_effect (rom : PhysicalROM) (CB P N t node : Nat) (field : Field) (state : NatState)
    (hCB : state.register .address = CB) (hbase : state.heap (CB + 6) = 4 + P)
    (ht : state.heap (CB + 2) = t) (hN : state.heap (CB + 0) = N) (hn : state.register .old = node) :
    let after := runOps rom (storeField field) state
    after.register .address = CB ∧ after.register .old = node ∧
      after.register .value = state.register .value ∧ after.register .flag = state.register .flag ∧
      after.heap = Function.update state.heap (fieldAddress P N t field node) (state.register .value) := by
  have hN' : state.heap CB = N := by simpa only [Nat.add_zero] using hN
  cases field <;>
    simp [storeField, fieldPointer, fieldPointerLead, fieldPointerExtra, fieldFactor, fieldExtra,
      fieldAddress, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
      hCB, hbase, ht, hN', hn, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  all_goals congr 1; omega

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
