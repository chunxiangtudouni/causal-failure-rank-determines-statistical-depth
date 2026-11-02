module

public import Structure.PA06_A19Prepare_StaticMetadata036_NodeScalars

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Private actual matched-singleton writer. Producer CB19/20 hold the
actually saved node/tool indices; CB16..18 belongs to initialUsed037.
No AST slot is touched. This runs AFTER actual DP/fullBuild and BEFORE
initialUsed037/finalHeader033. Full outer scanning and Word remain open. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (preparedSize mass loadRel storeRel)

def cacheLeafArguments : List PackingOp := storeRel .old 19 ++ storeRel .fresh 20

def recordSingleton : List PackingOp :=
  loadRel .old 19 ++ loadRel .value 20 ++
    [.base (.base (.constant .total 1)), .base (.base (.add .value .value .total))] ++ storeField .leaf ++
  loadRel .old 20 ++ loadRel .value 19 ++
    [.base (.base (.constant .total 1)), .base (.base (.add .value .value .total))] ++ storeField .tool

theorem cacheLeafArguments_length : cacheLeafArguments.length = 6 := rfl
theorem recordSingleton_length : recordSingleton.length = 46 := rfl

theorem cacheLeafArguments_noJump : ∀ op ∈ cacheLeafArguments, NoJump op := by
  simp [cacheLeafArguments, storeRel, NoJump]

theorem recordSingleton_noJump : ∀ op ∈ recordSingleton, NoJump op := by
  simp [recordSingleton, loadRel, storeField, fieldPointer, fieldPointerLead, fieldPointerExtra, NoJump]

theorem cacheLeafArguments_effect (rom : PhysicalROM) (CB node tool : Nat) (state : NatState)
    (hCB : state.register .address = CB) (hn : state.register .old = node)
    (ht : state.register .fresh = tool) :
    let after := runOps rom cacheLeafArguments state
    after.register .address = CB ∧ after.register .old = node ∧ after.register .fresh = tool ∧
      after.heap = Function.update (Function.update state.heap (CB + 19) node) (CB + 20) tool := by
  simp [cacheLeafArguments, storeRel, runOps, natExecuteOp, Op.execute, Instruction.execute, hCB, hn, ht]

/-- One genuine match writes two original ordinary metadata cells. All
inputs are actual dimension/control values; no leaf or tool answer is given. -/
theorem recordSingleton_effect (rom : PhysicalROM) (CB P N q t node tool : Nat) (state : NatState)
    (hCB : state.register .address = CB) (hbase : state.heap (CB + 6) = 4 + P)
    (ht : state.heap (CB + 2) = t) (hN : state.heap (CB + 0) = N)
    (hn : state.heap (CB + 19) = node) (htool : state.heap (CB + 20) = tool)
    (hnode : node < t) (htoolBound : tool < q)
    (hlayout : CB = 4 + P + 4096 * (N + q + 1 + t)) :
    let after := runOps rom recordSingleton state
    after.register .address = CB ∧ after.heap =
      Function.update (Function.update state.heap (fieldAddress P N t .leaf node) (tool + 1))
        (fieldAddress P N t .tool tool) (node + 1) := by
  have hbelow : fieldAddress P N t .leaf node < CB := by
    change 6 + P + 5 * t + node < CB
    omega
  have hN' : state.heap CB = N := by simpa only [Nat.add_zero] using hN
  simp (disch := omega) [recordSingleton, loadRel, storeField, fieldPointer,
    fieldPointerLead, fieldPointerExtra, fieldFactor, fieldExtra, fieldAddress,
    runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
    hCB, hbase, ht, hN', hn, htool, Function.update_apply,
    Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] at hbelow ⊢
  congr 1
  · congr 1
    omega
  · omega

/-- This condition comes from the actual card getter and022 bit query.
It is a finite semantic implication, not an extra original-caller oracle. -/
theorem singleton_of_card_bit (q : Nat) (full : List (Finset (Fin q)))
    (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q)
    (hcard : (prepareNormalization q full).indexed.metadata.cardinalities.get node = 1)
    (hbit : bit (decide (tool ∈ (prepareNormalization q full).indexed.decode node)) = 1) :
    (prepareNormalization q full).indexed.decode node = {tool} := by
  have hmem : tool ∈ (prepareNormalization q full).indexed.decode node := by
    by_contra h
    simp [h, bit] at hbit
  have hsmall : ((prepareNormalization q full).indexed.decode node).card ≤ 1 := by
    rw [← metadata_cardinality]
    omega
  exact Finset.eq_singleton_iff_unique_mem.mpr
    ⟨hmem, fun other hother => (Finset.card_le_one.mp hsmall) other hother tool hmem⟩

/-- Exact original leaf/tool lookup correspondence, including q=1 and
singleton stages duplicated in the raw input. No retained-ID arithmetic is used. -/
theorem singleton_original_labels (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q)
    (hdecode : (prepareNormalization q full).indexed.decode node = {tool}) :
    (match (IndexedDescent.leafTools (prepareNormalization q full).indexed).get node with
      | none => 0 | some found => found.val + 1) = tool.val + 1 ∧
      node.val + 1 = ((IndexedStaticMetadata.buildPositive q full hq).toolNodes.get tool).val + 1 := by
  constructor
  · rw [IndexedDescent.leafTools_get, hdecode, IndexedDescent.singletonTool_singleton]
  · have heq : node = (IndexedStaticMetadata.buildPositive q full hq).toolNodes.get tool :=
      prepared_indexed_decode_injective q full
        (hdecode.trans (IndexedStaticMetadata.buildPositive_tool_decode q full hq tool).symm)
    rw [heq]

/-- Real fetched46-op matched writer with exact original semantic labels;
this only handles a genuine matched singleton. The scanning loop still has
to establish each call and cover all node/tool entries. -/
theorem singleton_nat_run (rom : PhysicalROM) (left right : List PackingOp)
    (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (CB P : Nat) (state : NatState)
    (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q)
    (hCB : state.register .address = CB) (hbase : state.heap (CB + 6) = 4 + P)
    (ht : state.heap (CB + 2) = preparedSize q full) (hN : state.heap (CB + 0) = full.length)
    (hn : state.heap (CB + 19) = node.val) (htool : state.heap (CB + 20) = tool.val)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
    (hdecode : (prepareNormalization q full).indexed.decode node = {tool})
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    let after := natRun rom (left ++ recordSingleton ++ right) 46 state
    after.register .address = CB ∧
      after.heap (fieldAddress P full.length (preparedSize q full) .leaf node.val) =
        (match (IndexedDescent.leafTools (prepareNormalization q full).indexed).get node with
          | none => 0 | some found => found.val + 1) ∧
      after.heap (fieldAddress P full.length (preparedSize q full) .tool tool.val) =
        ((IndexedStaticMetadata.buildPositive q full hq).toolNodes.get tool).val + 1 ∧
      (∀ address, address ≠ fieldAddress P full.length (preparedSize q full) .leaf node.val →
        address ≠ fieldAddress P full.length (preparedSize q full) .tool tool.val →
        after.heap address = state.heap address) ∧
      after.pc = 5 * (left.length + 46) ∧ after.halted = false := by
  have hrun := straight_run rom left recordSingleton right recordSingleton_noJump state hpc ha
  rw [recordSingleton_length] at hrun
  rw [hrun]
  have h := recordSingleton_effect rom CB P full.length q (preparedSize q full) node.val tool.val state
    hCB hbase ht hN hn htool node.isLt tool.isLt hlayout
  have labels := singleton_original_labels q full hq node tool hdecode
  have hne : fieldAddress P full.length (preparedSize q full) .leaf node.val ≠
      fieldAddress P full.length (preparedSize q full) .tool tool.val := by
    have hn' : node.val < preparedSize q full := node.isLt
    change 6 + P + 5 * preparedSize q full + node.val ≠
      6 + P + 6 * preparedSize q full + full.length + tool.val
    omega
  refine ⟨h.1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.2, Function.update_of_ne hne, Function.update_self, labels.1]
  · rw [h.2, Function.update_self, labels.2]
  · intro address hleaf htool'
    rw [h.2, Function.update_of_ne htool', Function.update_of_ne hleaf]
  · rw [runOps_pc rom _ state recordSingleton_noJump, hpc, recordSingleton_length]
    omega
  · exact (runOps_halted rom _ state).trans ha

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
