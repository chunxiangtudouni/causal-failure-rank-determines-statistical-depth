module

public import Structure.PA06_A19Prepare_StaticMetadata036_Fields
public import Structure.PA06_A19Prepare_StaticMetadata036_Run

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Private actual fixed Nat producers of one cardinality/internal entry.
Every stored value comes from copied007 ord/card data. These are executable
blocks for the full metadata loop; they do not assume a computed metadata
answer, and they do not yet close the outer loop or the Word refinement. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (preparedSize mass)

inductive NodeScalar where
  | cardinality | internal
  deriving DecidableEq

def scalarField : NodeScalar → Field
  | .cardinality => .cardinality | .internal => .internal

def scalarTransform : NodeScalar → List PackingOp
  | .cardinality => [] | .internal => internalFlag

def scalarProgram (scalar : NodeScalar) : List PackingOp :=
  cardProgram ++ scalarTransform scalar ++ storeField (scalarField scalar)

def scalarValue (q : Nat) (full : List (Finset (Fin q)))
    (node : (prepareNormalization q full).indexed.NodeId) : NodeScalar → Nat
  | .cardinality => (prepareNormalization q full).indexed.metadata.cardinalities.get node
  | .internal => bit ((prepareNormalization q full).indexed.metadata.isInternal.get node)

theorem scalarProgram_length (scalar : NodeScalar) :
    (scalarProgram scalar).length = if scalar = .cardinality then 27 else 30 := by
  cases scalar <;> rfl

theorem scalarProgram_noJump (scalar : NodeScalar) : ∀ op ∈ scalarProgram scalar, NoJump op := by
  cases scalar <;>
    simp [scalarProgram, scalarTransform, scalarField, cardProgram, internalFlag,
      storeField, fieldPointer, fieldPointerLead, fieldPointerExtra, NoJump]

theorem prepared_internal_bit (q : Nat) (full : List (Finset (Fin q)))
    (node : (prepareNormalization q full).indexed.NodeId) :
    bit (decide (1 < (prepareNormalization q full).indexed.metadata.cardinalities.get node)) =
      bit ((prepareNormalization q full).indexed.metadata.isInternal.get node) := by
  simp only [IndexedNodeCache.metadata, cache_get_ofFn]

theorem cardProgram_original (rom : PhysicalROM) (q : Nat) (full : List (Finset (Fin q)))
    (CB : Nat) (state : NatState) (data : RawCardData q full CB state)
    (node : (prepareNormalization q full).indexed.NodeId)
    (hCB : state.register .address = CB) (hn : state.register .old = node.val) :
    let after := runOps rom cardProgram state
    after.register .value = scalarValue q full node .cardinality ∧
      after.register .address = CB ∧ after.register .old = node.val ∧
      after.register .fresh = state.register .fresh ∧ after.register .flag = state.register .flag ∧
      after.heap = state.heap := by
  obtain ⟨candidate, hord, hsupport⟩ := data.ordered node
  have hcard : state.heap (rawCardAddress CB candidate.val) =
      (prepareNormalization q full).indexed.metadata.cardinalities.get node := by
    rw [data.cards candidate, metadata_cardinality]
    exact congrArg Finset.card hsupport
  exact cardProgram_effect rom CB (mass q full) node.val candidate.val
    (scalarValue q full node .cardinality) state hCB data.mass_cell hn hord hcard

theorem scalarProgram_effect (rom : PhysicalROM) (q : Nat) (full : List (Finset (Fin q)))
    (CB P : Nat) (scalar : NodeScalar) (state : NatState) (data : RawCardData q full CB state)
    (node : (prepareNormalization q full).indexed.NodeId)
    (hCB : state.register .address = CB) (hn : state.register .old = node.val)
    (ht : state.heap (CB + 2) = preparedSize q full)
    (hbase : state.heap (CB + 6) = 4 + P) (hN : state.heap (CB + 0) = full.length) :
    let after := runOps rom (scalarProgram scalar) state
    after.register .address = CB ∧ after.register .old = node.val ∧
      after.register .flag = state.register .flag ∧
      after.heap = Function.update state.heap
        (fieldAddress P full.length (preparedSize q full) (scalarField scalar) node.val)
        (scalarValue q full node scalar) := by
  let card := runOps rom cardProgram state
  have hc := cardProgram_original rom q full CB state data node hCB hn
  have hct : card.heap (CB + 2) = preparedSize q full := by rw [hc.2.2.2.2.2]; exact ht
  have hcb : card.heap (CB + 6) = 4 + P := by rw [hc.2.2.2.2.2]; exact hbase
  have hcn : card.heap (CB + 0) = full.length := by rw [hc.2.2.2.2.2]; exact hN
  cases scalar with
  | cardinality =>
    have hs := storeField_effect rom CB P full.length (preparedSize q full) node.val .cardinality card
      hc.2.1 hcb hct hcn hc.2.2.1
    simp only [scalarProgram, scalarTransform, scalarField, List.append_nil, runOps_append]
    refine ⟨hs.1, hs.2.1, hs.2.2.2.1.trans hc.2.2.2.2.1, ?_⟩
    rw [hs.2.2.2.2, hc.2.2.2.2.2, hc.1]
  | internal =>
    let flagged := runOps rom internalFlag card
    have hf : flagged.register .address = CB ∧ flagged.register .old = node.val ∧
        flagged.register .flag = state.register .flag ∧ flagged.heap = state.heap :=
      ⟨hc.2.1, hc.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2⟩
    have hfv : flagged.register .value = scalarValue q full node .internal := by
      rw [internalFlag_value, hc.1]
      exact prepared_internal_bit q full node
    have hs := storeField_effect rom CB P full.length (preparedSize q full) node.val .internal flagged
      hf.1 (by rw [hf.2.2.2]; exact hbase) (by rw [hf.2.2.2]; exact ht)
      (by rw [hf.2.2.2]; exact hN) hf.2.1
    simp only [scalarProgram, scalarTransform, scalarField, runOps_append]
    refine ⟨hs.1, hs.2.1, hs.2.2.2.1.trans hf.2.2.1, ?_⟩
    rw [hs.2.2.2.2, hf.2.2.2, hfv]

/-- The real fetched27/30-op segment, with original semantic output and
ordinary heap frame. Its incoming arbitrary registers are not restricted. -/
theorem scalar_nat_run (rom : PhysicalROM) (left right : List PackingOp)
    (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat) (scalar : NodeScalar)
    (state : NatState) (data : RawCardData q full CB state)
    (node : (prepareNormalization q full).indexed.NodeId)
    (hCB : state.register .address = CB) (hn : state.register .old = node.val)
    (ht : state.heap (CB + 2) = preparedSize q full)
    (hbase : state.heap (CB + 6) = 4 + P) (hN : state.heap (CB + 0) = full.length)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    let after := natRun rom (left ++ scalarProgram scalar ++ right) (scalarProgram scalar).length state
    after.register .address = CB ∧ after.register .old = node.val ∧
      after.register .flag = state.register .flag ∧
      after.heap = Function.update state.heap
        (fieldAddress P full.length (preparedSize q full) (scalarField scalar) node.val)
        (scalarValue q full node scalar) ∧
      after.pc = 5 * (left.length + (scalarProgram scalar).length) ∧ after.halted = false := by
  rw [straight_run rom left (scalarProgram scalar) right (scalarProgram_noJump scalar) state hpc ha]
  have h := scalarProgram_effect rom q full CB P scalar state data node hCB hn ht hbase hN
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, ?_, ?_⟩
  · rw [runOps_pc rom _ state (scalarProgram_noJump scalar), hpc]
    omega
  · exact (runOps_halted rom _ state).trans ha

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
