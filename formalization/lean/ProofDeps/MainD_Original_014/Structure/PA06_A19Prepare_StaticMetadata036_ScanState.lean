module

public import Structure.PA06_A19Prepare_StaticMetadata036_ScanProgram

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! True footprint and loop states for the complete191-op scan. Source
cache/headers are preserved by actual allowed-write proofs. The reference
raw heap is only a proof invariant; it is not a runtime answer input. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (preparedSize mass loadRel storeRel setRel incrementRel)

structure ScanInput (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat) (state : NatState) : Prop where
  address : state.register .address = CB
  raw : RawCardData q full CB state
  stages : state.heap (CB + 0) = full.length
  tools : state.heap (CB + 1) = q
  nodes : state.heap (CB + 2) = preparedSize q full
  base : state.heap (CB + 6) = 4 + P

def ScanAllowed (q : Nat) (full : List (Finset (Fin q))) (CB P address : Nat) : Prop :=
  address = CB + 19 ∨ address = CB + 20 ∨ address = CB + 21 ∨
  (fieldAddress P full.length (preparedSize q full) .leaf 0 ≤ address ∧
    address < fieldAddress P full.length (preparedSize q full) .leaf 0 + preparedSize q full) ∨
  (fieldAddress P full.length (preparedSize q full) .tool 0 ≤ address ∧
    address < fieldAddress P full.length (preparedSize q full) .tool 0 + q)

def ScanFrame (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat) (before after : NatState) : Prop :=
  ∀ address, ¬ ScanAllowed q full CB P address → after.heap address = before.heap address

theorem ScanFrame.refl (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat) (state : NatState) :
    ScanFrame q full CB P state state := fun _ _ => rfl

theorem ScanFrame.trans {q : Nat} {full : List (Finset (Fin q))} {CB P : Nat} {a b c : NatState}
    (hab : ScanFrame q full CB P a b) (hbc : ScanFrame q full CB P b c) : ScanFrame q full CB P a c :=
  fun address hn => (hbc address hn).trans (hab address hn)

theorem scan_regions_below_control (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full)) :
    fieldAddress P full.length (preparedSize q full) .leaf 0 + preparedSize q full ≤ CB ∧
      fieldAddress P full.length (preparedSize q full) .tool 0 + q ≤ CB := by
  simp only [fieldAddress, fieldFactor, fieldExtra, mass] at *
  omega

theorem ScanInput.of_frame {q : Nat} {full : List (Finset (Fin q))} {CB P : Nat}
    {before after : NatState} (input : ScanInput q full CB P before)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
    (frame : ScanFrame q full CB P before after) (hCB : after.register .address = CB) : ScanInput q full CB P after := by
  have below := scan_regions_below_control q full CB P hlayout
  have preserve (address : Nat) (ha : CB ≤ address)
      (h19 : address ≠ CB + 19) (h20 : address ≠ CB + 20) (h21 : address ≠ CB + 21) :
      after.heap address = before.heap address := by
    apply frame
    unfold ScanAllowed
    omega
  refine ⟨hCB, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rw [preserve _ (by omega) (by omega) (by omega) (by omega)]
      exact input.raw.mass_cell
    · intro candidate
      rw [preserve _ (by unfold rawCardAddress; omega) (by unfold rawCardAddress; omega)
        (by unfold rawCardAddress; omega) (by unfold rawCardAddress; omega)]
      exact input.raw.cards candidate
    · intro node
      obtain ⟨candidate, hord, hsupport⟩ := input.raw.ordered node
      refine ⟨candidate, ?_, hsupport⟩
      rw [preserve _ (by unfold rawOrdAddress; omega) (by unfold rawOrdAddress; omega)
        (by unfold rawOrdAddress; omega) (by unfold rawOrdAddress; omega)]
      exact hord
  · rw [preserve _ (by omega) (by omega) (by omega) (by omega)]
    exact input.stages
  · rw [preserve _ (by omega) (by omega) (by omega) (by omega)]
    exact input.tools
  · rw [preserve _ (by omega) (by omega) (by omega) (by omega)]
    exact input.nodes
  · rw [preserve _ (by omega) (by omega) (by omega) (by omega)]
    exact input.base

def originalLeaf (q : Nat) (full : List (Finset (Fin q)))
    (node : (prepareNormalization q full).indexed.NodeId) : Nat :=
  match (IndexedDescent.leafTools (prepareNormalization q full).indexed).get node with
  | none => 0 | some tool => tool.val + 1

def singletonIndex (q : Nat) (full : List (Finset (Fin q))) (tool : Fin q) : Nat :=
  (IndexedStaticMetadata.singletonNode q full tool).val

structure LeafOuterReady (q : Nat) (full : List (Finset (Fin q))) (CB P row pc : Nat) (state : NatState) : Prop where
  input : ScanInput q full CB P state
  node_cell : state.heap (CB + 19) = row
  leaves : ∀ node : (prepareNormalization q full).indexed.NodeId, node.val < row →
    state.heap (fieldAddress P full.length (preparedSize q full) .leaf node.val) = originalLeaf q full node
  tools : ∀ tool : Fin q, singletonIndex q full tool < row →
    state.heap (fieldAddress P full.length (preparedSize q full) .tool tool.val) = singletonIndex q full tool + 1
  pc : state.pc = pc
  active : state.halted = false

structure LeafInnerReady (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat) (reference : NatState)
    (node : (prepareNormalization q full).indexed.NodeId) (upto pc : Nat) (state : NatState) : Prop where
  input : ScanInput q full CB P state
  node_cell : state.heap (CB + 19) = node.val
  tool_cell : state.heap (CB + 20) = upto
  card_cell : state.heap (CB + 21) = (prepareNormalization q full).indexed.metadata.cardinalities.get node
  row_leaf : state.heap (fieldAddress P full.length (preparedSize q full) .leaf node.val) =
    scanWinner (fun tool => scanMatch (rawIncidenceROM q full) reference.heap CB (mass q full) node.val tool) upto
  leaves : ∀ earlier : (prepareNormalization q full).indexed.NodeId, earlier.val < node.val →
    state.heap (fieldAddress P full.length (preparedSize q full) .leaf earlier.val) = originalLeaf q full earlier
  tools : ∀ tool : Fin q, singletonIndex q full tool < node.val →
    state.heap (fieldAddress P full.length (preparedSize q full) .tool tool.val) = singletonIndex q full tool + 1
  row_tools : ∀ tool : Fin q, tool.val < upto → singletonIndex q full tool = node.val →
    state.heap (fieldAddress P full.length (preparedSize q full) .tool tool.val) = node.val + 1
  pc : state.pc = pc
  active : state.halted = false

theorem scanMatch_stable (q : Nat) (full : List (Finset (Fin q))) (CB : Nat) (before after : NatState)
    (first : RawCardData q full CB before) (second : RawCardData q full CB after)
    (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q) :
    scanMatch (rawIncidenceROM q full) before.heap CB (mass q full) node.val tool.val =
      scanMatch (rawIncidenceROM q full) after.heap CB (mass q full) node.val tool.val := by
  have hf := scanMatch_iff_singleton q full CB before first node tool
  have hs := scanMatch_iff_singleton q full CB after second node tool
  cases hfirst : scanMatch (rawIncidenceROM q full) before.heap CB (mass q full) node.val tool.val <;>
    cases hsecond : scanMatch (rawIncidenceROM q full) after.heap CB (mass q full) node.val tool.val <;>
    simp_all

theorem scanMatch_iff_index (q : Nat) (full : List (Finset (Fin q))) (CB : Nat) (state : NatState)
    (data : RawCardData q full CB state) (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q) :
    scanMatch (rawIncidenceROM q full) state.heap CB (mass q full) node.val tool.val = true ↔
      singletonIndex q full tool = node.val := by
  rw [scanMatch_iff_singleton q full CB state data node tool]
  constructor
  · intro hdecode
    have heq : IndexedStaticMetadata.singletonNode q full tool = node :=
      prepared_indexed_decode_injective q full ((IndexedStaticMetadata.singletonNode_decode q full tool).trans hdecode.symm)
    exact congrArg Fin.val heq
  · intro heq
    have hn : node = IndexedStaticMetadata.singletonNode q full tool := Fin.ext heq.symm
    rw [hn]
    exact IndexedStaticMetadata.singletonNode_decode q full tool

/-- Concrete effects of all non-query loop bodies. -/
theorem scanBoundedTest_pc (rom : PhysicalROM) (CB size count bound counter exit : Nat) (state : NatState)
    (hCB : state.register .address = CB) (hs : state.heap (CB + bound) = size)
    (hc : state.heap (CB + counter) = count) :
    (runOps rom (scanBoundedTest bound counter exit) state).pc =
      if size - count = 0 then 5 * exit else state.pc + 45 := by
  simp [scanBoundedTest, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute, hCB, hs, hc, Nat.add_assoc]

theorem scanArguments_effect (rom : PhysicalROM) (CB node tool : Nat) (state : NatState)
    (hCB : state.register .address = CB) (hn : state.heap (CB + 19) = node)
    (ht : state.heap (CB + 20) = tool) :
    let after := runOps rom scanArguments state
    after.register .old = node ∧ after.register .fresh = tool ∧ after.register .address = CB ∧ after.heap = state.heap := by
  simp [scanArguments, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute, hCB, hn, ht]

theorem scanInnerTail_effect (rom : PhysicalROM) (CB tool start : Nat) (state : NatState)
    (hCB : state.register .address = CB) (ht : state.heap (CB + 20) = tool) :
    let after := runOps rom (scanInnerTail start) state
    after.register .address = CB ∧ after.heap = Function.update state.heap (CB + 20) (tool + 1) ∧
      after.pc = 5 * (start + 51) ∧ after.halted = state.halted := by
  simp [scanInnerTail, incrementRel, loadRel, storeRel, jumpTo, runOps, natExecuteOp,
    Op.execute, Instruction.execute, hCB, ht]

theorem scanOuterTail_effect (rom : PhysicalROM) (CB node start : Nat) (state : NatState)
    (hCB : state.register .address = CB) (hn : state.heap (CB + 19) = node) :
    let after := runOps rom (scanOuterTail start) state
    after.register .address = CB ∧ after.heap = Function.update state.heap (CB + 19) (node + 1) ∧
      after.pc = 5 * (start + 4) ∧ after.halted = state.halted := by
  simp [scanOuterTail, incrementRel, loadRel, storeRel, jumpTo, runOps, natExecuteOp,
    Op.execute, Instruction.execute, hCB, hn]

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
