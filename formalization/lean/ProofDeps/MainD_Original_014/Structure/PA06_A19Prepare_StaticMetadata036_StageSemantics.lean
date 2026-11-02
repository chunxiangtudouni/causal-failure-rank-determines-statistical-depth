module

public import Structure.PA06_A19Prepare_StaticMetadata036_ScanRun

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Complete streaming stage×node×tool support matching on raw incidence.
Empty and duplicate stages use the same executable scan. Neither a stage
map nor a support set is an algorithm input; original supports occur only
in the proof of exact output correspondence. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (preparedSize mass)

def rawStageBit (rom : PhysicalROM) (stage tool : Nat) : Nat :=
  rom.semantic.read .input (2 + stage * rom.semantic.read .input 1 + tool)

def stageMatchTools (rom : PhysicalROM) (heap : Nat → Nat) (CB M stage node : Nat) : Nat → Bool
  | 0 => true
  | upto + 1 => stageMatchTools rom heap CB M stage node upto &&
      decide (rawStageBit rom stage upto = rawCandidateBit rom (heap (rawOrdAddress CB M node)) upto)

def stageScan (rom : PhysicalROM) (heap : Nat → Nat) (CB M nodes tools stage : Nat) : Nat :=
  scanWinner (fun node => stageMatchTools rom heap CB M stage node tools) nodes

def scanStageWords (rom : PhysicalROM) (heap : Nat → Nat) (CB M nodes tools stages : Nat) : List Nat :=
  (List.range stages).map (stageScan rom heap CB M nodes tools)

theorem stageMatchTools_iff (rom : PhysicalROM) (heap : Nat → Nat) (CB M stage node upto : Nat) :
    stageMatchTools rom heap CB M stage node upto = true ↔
      ∀ tool < upto, rawStageBit rom stage tool = rawCandidateBit rom (heap (rawOrdAddress CB M node)) tool := by
  induction upto with
  | zero => simp [stageMatchTools]
  | succ upto ih =>
    rw [stageMatchTools, Bool.and_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro ⟨previous, last⟩ tool ht
      by_cases hp : tool < upto
      · exact previous tool hp
      · have heq : tool = upto := by omega
        simpa only [heq] using last
    · intro all
      exact ⟨fun tool ht => all tool (by omega), all upto (by omega)⟩

theorem rawNodeBit_eq_decode (q : Nat) (full : List (Finset (Fin q))) (CB : Nat) (state : NatState)
    (data : RawCardData q full CB state) (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q) :
    rawCandidateBit (rawIncidenceROM q full) (state.heap (rawOrdAddress CB (mass q full) node.val)) tool.val =
      bit (decide (tool ∈ (prepareNormalization q full).indexed.decode node)) := by
  obtain ⟨candidate, hord, hsupport⟩ := data.ordered node
  rw [hord, rawCandidateBit_eq, hsupport]

/-- All real raw bit comparisons hold exactly when the two supports agree. -/
theorem stageMatchTools_iff_support (q : Nat) (full : List (Finset (Fin q))) (CB : Nat) (state : NatState)
    (data : RawCardData q full CB state) (stage : Fin full.length)
    (node : (prepareNormalization q full).indexed.NodeId) :
    stageMatchTools (rawIncidenceROM q full) state.heap CB (mass q full) stage.val node.val q = true ↔
      (prepareNormalization q full).indexed.decode node = full[stage.val] := by
  rw [stageMatchTools_iff]
  constructor
  · intro agrees
    ext tool
    have h := agrees tool.val tool.isLt
    rw [rawStageBit, raw_header_q, raw_bit q full stage tool,
      rawNodeBit_eq_decode q full CB state data node tool] at h
    by_cases hs : tool ∈ full[stage.val] <;>
      by_cases hn : tool ∈ (prepareNormalization q full).indexed.decode node <;> simp_all [bit]
  · intro hdecode tool ht
    rw [rawStageBit, raw_header_q, raw_bit q full stage ⟨tool, ht⟩,
      rawNodeBit_eq_decode q full CB state data node ⟨tool, ht⟩, hdecode]

theorem prepared_support_nonempty (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (node : (prepareNormalization q full).indexed.NodeId) :
    ((prepareNormalization q full).indexed.decode node).Nonempty := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  exact nodeFamily_nonempty_nodes full _ (prepared_indexed_node_mem q full node)

/-- Full stage map, including empty stages and repeated copies of the same
support, equals the original optional indexed lookup with zero encoding. -/
theorem stageScan_original (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (CB : Nat)
    (state : NatState) (data : RawCardData q full CB state) (stage : Fin full.length) :
    stageScan (rawIncidenceROM q full) state.heap CB (mass q full) (preparedSize q full) q stage.val =
      encodedNode (prepareNormalization q full).indexed
        ((IndexedStaticMetadata.buildPositive q full hq).stageNodes.get stage) := by
  cases hstage : (IndexedStaticMetadata.buildPositive q full hq).stageNodes.get stage with
  | none =>
    change scanWinner _ (preparedSize q full) = 0
    apply scanWinner_none
    intro index hi
    cases hm : stageMatchTools (rawIncidenceROM q full) state.heap CB (mass q full) stage.val index q with
    | false => rfl
    | true =>
      have hdecode := (stageMatchTools_iff_support q full CB state data stage ⟨index, hi⟩).mp hm
      have hempty := (IndexedStaticMetadata.buildPositive_stage_none_iff q full hq stage).mp hstage
      have hnonempty := prepared_support_nonempty q full hq ⟨index, hi⟩
      rw [hdecode, hempty] at hnonempty
      simp at hnonempty
  | some target =>
    change scanWinner _ (preparedSize q full) = target.val + 1
    apply scanWinner_unique _ (preparedSize q full) target.val target.isLt
    intro index hi
    rw [stageMatchTools_iff_support q full CB state data stage ⟨index, hi⟩]
    have hdecode := ((IndexedStaticMetadata.buildPositive_stage_some_iff q full hq stage target).mp hstage).2
    constructor
    · intro hother
      have heq : (⟨index, hi⟩ : (prepareNormalization q full).indexed.NodeId) = target :=
        prepared_indexed_decode_injective q full (hother.trans hdecode.symm)
      exact congrArg Fin.val heq
    · intro heq
      have hn : (⟨index, hi⟩ : (prepareNormalization q full).indexed.NodeId) = target := Fin.ext heq
      rw [hn]
      exact hdecode

theorem complete_stage_scan (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (CB : Nat)
    (state : NatState) (data : RawCardData q full CB state) :
    (scanStageWords (rawIncidenceROM q full) state.heap CB (mass q full) (preparedSize q full) q full.length).length = full.length ∧
    ∀ stage : Fin full.length,
      (scanStageWords (rawIncidenceROM q full) state.heap CB (mass q full) (preparedSize q full) q full.length)[stage.val]'(by
        simpa only [scanStageWords, List.length_map, List.length_range] using stage.isLt) =
      encodedNode (prepareNormalization q full).indexed
        ((IndexedStaticMetadata.buildPositive q full hq).stageNodes.get stage) := by
  constructor
  · simp [scanStageWords]
  · intro stage
    simp only [scanStageWords, List.getElem_map, List.getElem_range]
    exact stageScan_original q full hq CB state data stage

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
