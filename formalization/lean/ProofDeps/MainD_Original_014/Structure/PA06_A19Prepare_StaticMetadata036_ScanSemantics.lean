module

public import Structure.PA06_A19Prepare_StaticMetadata036_LeafTool

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Complete finite Nat leaf/tool scan semantics from actual raw ROM and
copied ord/card cells. No prepared-tree, singleton-node, or lookup answer is
an algorithm input. The following file links the same reads to fixed code;
these pure semantics alone are not a machine-running-time claim. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (preparedSize mass)

/-- Exactly the root/stage/singleton arithmetic branches of frozen022 raw32.
Every stage bit is read from original raw incidence, not a dense node ROM. -/
def rawCandidateBit (rom : PhysicalROM) (candidate tool : Nat) : Nat :=
  let N := rom.semantic.read .input 0
  let q := rom.semantic.read .input 1
  if candidate = 0 then 1 else if candidate ≤ N then
    rom.semantic.read .input (2 + (candidate - 1) * q + tool)
  else bit (decide (candidate - N - 1 = tool))

def scanMatch (rom : PhysicalROM) (heap : Nat → Nat) (CB M node tool : Nat) : Bool :=
  let candidate := heap (rawOrdAddress CB M node)
  decide (heap (rawCardAddress CB candidate) = 1) && decide (rawCandidateBit rom candidate tool = 1)

/-- Last matching encoded index. This recursion performs the full indicated
finite scan; it does not call findNodeId/prepareNormalization. -/
def scanWinner (test : Nat → Bool) : Nat → Nat
  | 0 => 0
  | upto + 1 => if test upto then upto + 1 else scanWinner test upto

def leafScan (rom : PhysicalROM) (heap : Nat → Nat) (CB M tools node : Nat) : Nat :=
  scanWinner (fun tool => scanMatch rom heap CB M node tool) tools

def toolScan (rom : PhysicalROM) (heap : Nat → Nat) (CB M nodes tool : Nat) : Nat :=
  scanWinner (fun node => scanMatch rom heap CB M node tool) nodes

def scanLeafWords (rom : PhysicalROM) (heap : Nat → Nat) (CB M nodes tools : Nat) : List Nat :=
  (List.range nodes).map (leafScan rom heap CB M tools)

def scanToolWords (rom : PhysicalROM) (heap : Nat → Nat) (CB M nodes tools : Nat) : List Nat :=
  (List.range tools).map (toolScan rom heap CB M nodes)

theorem rawCandidateBit_eq (q : Nat) (full : List (Finset (Fin q)))
    (candidate : Fin (mass q full)) (tool : Fin q) :
    rawCandidateBit (rawIncidenceROM q full) candidate.val tool.val =
      bit (decide (tool ∈ RawCandidateParents.candidateSupport q full candidate.val)) := by
  unfold RawCandidateParents.candidateSupport
  rw [← RawCandidateIncidenceRAM.support_eq_candidateSupports_getD]
  by_cases hr : candidate.val = 0
  · simp [rawCandidateBit, RawCandidateIncidenceRAM.support, hr, bit]
  · by_cases hs : candidate.val ≤ full.length
    · simp only [rawCandidateBit, raw_header_N, raw_header_q, hr, ite_false, hs, ite_true,
        RawCandidateIncidenceRAM.support, dite_false, dite_true]
      exact raw_bit q full ⟨candidate.val - 1, by omega⟩ tool
    · simp [rawCandidateBit, raw_header_N, RawCandidateIncidenceRAM.support,
        hr, hs, Fin.ext_iff, eq_comm]

theorem scanWinner_none (test : Nat → Bool) (upto : Nat)
    (hnone : ∀ index < upto, test index = false) : scanWinner test upto = 0 := by
  revert hnone
  induction upto with
  | zero => intro _; rfl
  | succ upto ih =>
    intro hnone
    rw [scanWinner, hnone upto (by omega)]
    exact ih (fun index hi => hnone index (by omega))

theorem scanWinner_unique (test : Nat → Bool) (upto key : Nat) (hkey : key < upto)
    (hunique : ∀ index < upto, test index = true ↔ index = key) : scanWinner test upto = key + 1 := by
  revert hkey hunique
  induction upto with
  | zero => intro hkey _; omega
  | succ upto ih =>
    intro hkey hunique
    by_cases heq : upto = key
    · rw [scanWinner, (hunique upto (by omega)).mpr heq]
      simp only [heq]
      exact ite_eq_left True.intro
    · have hfalse : test upto = false := by
        cases ht : test upto with
        | false => rfl
        | true => exact False.elim (heq ((hunique upto (by omega)).mp ht))
      rw [scanWinner, hfalse]
      exact ih (by omega) (fun index hi => hunique index (by omega))

/-- The true raw scan predicate is equivalent to the singleton support.
The equivalence is proved from actual cached card/ord data. -/
theorem scanMatch_iff_singleton (q : Nat) (full : List (Finset (Fin q))) (CB : Nat)
    (state : NatState) (data : RawCardData q full CB state)
    (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q) :
    scanMatch (rawIncidenceROM q full) state.heap CB (mass q full) node.val tool.val = true ↔
      (prepareNormalization q full).indexed.decode node = {tool} := by
  obtain ⟨candidate, hord, hsupport⟩ := data.ordered node
  have hcard := rawCardData_node_card q full CB state data node
  have hbit : rawCandidateBit (rawIncidenceROM q full)
      (state.heap (rawOrdAddress CB (mass q full) node.val)) tool.val =
      bit (decide (tool ∈ (prepareNormalization q full).indexed.decode node)) := by
    rw [hord, rawCandidateBit_eq, hsupport]
  simp only [scanMatch, Bool.and_eq_true, decide_eq_true_eq, hcard, hbit]
  constructor
  · rintro ⟨hc, hb⟩
    exact singleton_of_card_bit q full node tool hc hb
  · intro hdecode
    constructor
    · rw [metadata_cardinality, hdecode]
      simp
    · simp [hdecode, bit]

/-- Every actual input tool has exactly one original singleton node. The
answer is derived here from the formal normalization, not passed to a scan. -/
theorem singleton_node_exists_unique (q : Nat) (full : List (Finset (Fin q))) (tool : Fin q) :
    ∃! node : (prepareNormalization q full).indexed.NodeId,
      (prepareNormalization q full).indexed.decode node = {tool} := by
  refine ⟨IndexedStaticMetadata.singletonNode q full tool,
    IndexedStaticMetadata.singletonNode_decode q full tool, ?_⟩
  intro node hn
  exact prepared_indexed_decode_injective q full
    (hn.trans (IndexedStaticMetadata.singletonNode_decode q full tool).symm)

/-- Complete leaf scan, including internal-node zero labels. -/
theorem leafScan_original (q : Nat) (full : List (Finset (Fin q))) (CB : Nat)
    (state : NatState) (data : RawCardData q full CB state)
    (node : (prepareNormalization q full).indexed.NodeId) :
    leafScan (rawIncidenceROM q full) state.heap CB (mass q full) q node.val =
      (match (IndexedDescent.leafTools (prepareNormalization q full).indexed).get node with
        | none => 0 | some tool => tool.val + 1) := by
  cases hleaf : (IndexedDescent.leafTools (prepareNormalization q full).indexed).get node with
  | none =>
    change scanWinner _ q = 0
    apply scanWinner_none
    intro tool ht
    cases hm : scanMatch (rawIncidenceROM q full) state.heap CB (mass q full) node.val tool with
    | false => rfl
    | true =>
      have hdecode := (scanMatch_iff_singleton q full CB state data node ⟨tool, ht⟩).mp hm
      have hs : (IndexedDescent.leafTools (prepareNormalization q full).indexed).get node =
          some (⟨tool, ht⟩ : Fin q) := by
        rw [IndexedDescent.leafTools_get, hdecode, IndexedDescent.singletonTool_singleton]
      rw [hleaf] at hs
      cases hs
  | some tool =>
    change scanWinner _ q = tool.val + 1
    apply scanWinner_unique _ q tool.val tool.isLt
    intro index hi
    have hdecode : (prepareNormalization q full).indexed.decode node = {tool} :=
      IndexedDescent.singletonTool_spec _ tool (by simpa only [IndexedDescent.leafTools_get] using hleaf)
    rw [scanMatch_iff_singleton q full CB state data node ⟨index, hi⟩]
    constructor
    · intro hother
      have heq : tool = (⟨index, hi⟩ : Fin q) := Finset.singleton_inj.mp (hdecode.symm.trans hother)
      exact (congrArg Fin.val heq).symm
    · intro heq
      have htool : (⟨index, hi⟩ : Fin q) = tool := Fin.ext heq
      rw [htool]
      exact hdecode

/-- Complete tool scan: its unique matching node is proved to be the
original buildPositive singleton lookup, including repeated singleton stages. -/
theorem toolScan_original (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (CB : Nat)
    (state : NatState) (data : RawCardData q full CB state) (tool : Fin q) :
    toolScan (rawIncidenceROM q full) state.heap CB (mass q full) (preparedSize q full) tool.val =
      ((IndexedStaticMetadata.buildPositive q full hq).toolNodes.get tool).val + 1 := by
  let target := (IndexedStaticMetadata.buildPositive q full hq).toolNodes.get tool
  change scanWinner _ (preparedSize q full) = target.val + 1
  apply scanWinner_unique _ (preparedSize q full) target.val target.isLt
  intro index hi
  rw [scanMatch_iff_singleton q full CB state data ⟨index, hi⟩ tool]
  constructor
  · intro hdecode
    have heq : (⟨index, hi⟩ : (prepareNormalization q full).indexed.NodeId) = target :=
      prepared_indexed_decode_injective q full
        (hdecode.trans (IndexedStaticMetadata.buildPositive_tool_decode q full hq tool).symm)
    exact congrArg Fin.val heq
  · intro heq
    have hnode : (⟨index, hi⟩ : (prepareNormalization q full).indexed.NodeId) = target := Fin.ext heq
    rw [hnode]
    exact IndexedStaticMetadata.buildPositive_tool_decode q full hq tool

theorem scan_output_lengths (rom : PhysicalROM) (heap : Nat → Nat) (CB M nodes tools : Nat) :
    (scanLeafWords rom heap CB M nodes tools).length = nodes ∧
      (scanToolWords rom heap CB M nodes tools).length = tools := by
  simp [scanLeafWords, scanToolWords]

/-- Every output index has the exact original value; both finite scans are
complete, rather than only a matched-pair correctness statement. -/
theorem complete_leaf_tool_scan (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (CB : Nat) (state : NatState) (data : RawCardData q full CB state) :
    (∀ node : (prepareNormalization q full).indexed.NodeId,
      (scanLeafWords (rawIncidenceROM q full) state.heap CB (mass q full) (preparedSize q full) q)[node.val]'(by
        simpa only [scanLeafWords, List.length_map, List.length_range] using node.isLt) =
        (match (IndexedDescent.leafTools (prepareNormalization q full).indexed).get node with
          | none => 0 | some tool => tool.val + 1)) ∧
    (∀ tool : Fin q,
      (scanToolWords (rawIncidenceROM q full) state.heap CB (mass q full) (preparedSize q full) q)[tool.val]'(by
        simpa only [scanToolWords, List.length_map, List.length_range] using tool.isLt) =
        ((IndexedStaticMetadata.buildPositive q full hq).toolNodes.get tool).val + 1) := by
  constructor
  · intro node
    simp only [scanLeafWords, List.getElem_map, List.getElem_range]
    exact leafScan_original q full CB state data node
  · intro tool
    simp only [scanToolWords, List.getElem_map, List.getElem_range]
    exact toolScan_original q full hq CB state data tool

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
