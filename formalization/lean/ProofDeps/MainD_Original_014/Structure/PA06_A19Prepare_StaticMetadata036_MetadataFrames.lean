module

public import Structure.PA06_A19Prepare_StaticMetadata036_CardsRun

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Actual cross-phase footprint adapters for all nine metadata segments.
These prove preservation across the real producers; no phase-order prose
or free restored heap replaces the frame equations. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (preparedSize mass)

theorem ScanInput.of_high_eq {q : Nat} {full : List (Finset (Fin q))} {CB P : Nat} {before after : NatState}
    (input : ScanInput q full CB P before) (hheap : ∀ address, CB ≤ address → after.heap address = before.heap address)
    (hCB : after.register .address = CB) : ScanInput q full CB P after := by
  refine ⟨hCB, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rw [hheap _ (by omega)]; exact input.raw.mass_cell
    · intro candidate
      rw [hheap _ (by unfold rawCardAddress; omega)]
      exact input.raw.cards candidate
    · intro node
      obtain ⟨candidate, hord, hsupport⟩ := input.raw.ordered node
      refine ⟨candidate, ?_, hsupport⟩
      rw [hheap _ (by unfold rawOrdAddress; omega)]
      exact hord
  · rw [hheap _ (by omega)]; exact input.stages
  · rw [hheap _ (by omega)]; exact input.tools
  · rw [hheap _ (by omega)]; exact input.nodes
  · rw [hheap _ (by omega)]; exact input.base

def MetadataAllowed (q : Nat) (full : List (Finset (Fin q))) (CB P address : Nat) : Prop :=
  (CB + 19 ≤ address ∧ address < CB + 25) ∨
    (6 + P ≤ address ∧ address < 6 + P + (6 * preparedSize q full + full.length + q))

def MetadataFrame (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat) (before after : NatState) : Prop :=
  ∀ address, ¬ MetadataAllowed q full CB P address → after.heap address = before.heap address

theorem metadata_frame_of_chain (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat)
    (a b c d e : NatState)
    (adj : ∀ address, address < 6 + P ∨ 6 + P + 3 * preparedSize q full ≤ address → b.heap address = a.heap address)
    (cards : CardsFrame q full CB P b c) (leaves : ScanFrame q full CB P c d) (stages : StageFrame q full CB P d e) :
    MetadataFrame q full CB P a e := by
  intro address hn
  have hadj : address < 6 + P ∨ 6 + P + 3 * preparedSize q full ≤ address := by
    unfold MetadataAllowed at hn
    omega
  have hc : ¬ CardsAllowed q full CB P address := by
    unfold MetadataAllowed at hn
    simp only [CardsAllowed, fieldAddress, fieldFactor, fieldExtra]
    omega
  have hl : ¬ ScanAllowed q full CB P address := by
    unfold MetadataAllowed at hn
    simp only [ScanAllowed, fieldAddress, fieldFactor, fieldExtra]
    omega
  have hs : ¬ StageAllowed q full CB P address := by
    unfold MetadataAllowed at hn
    simp only [StageAllowed, fieldAddress, fieldFactor, fieldExtra]
    omega
  rw [stages address hs, leaves address hl, cards address hc, adj address hadj]

/-- Real later footprints preserve the entire original adjacency prefix. -/
theorem adjacency_preserved (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full)
    (CB P : Nat) (a b c d : NatState) (written : AdjacencyWritten q full P a)
    (cards : CardsFrame q full CB P a b) (leaves : ScanFrame q full CB P b c) (stages : StageFrame q full CB P c d)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full)) : AdjacencyWritten q full P d := by
  have ht : 0 < preparedSize q full := by
    have h := PA06A19PrepareControlBank017.treeSize_pos full hq
    simpa only [treeSize, Nat.ne_of_gt hq, ite_false] using h
  have hbelow : 6 + P + 3 * preparedSize q full ≤ CB := by
    rw [hlayout]
    exact adjacency_below_control (mass q full) (preparedSize q full) P ht
  have preserve (position : Nat) (hp : position < 3 * preparedSize q full) :
      d.heap (6 + P + position) = a.heap (6 + P + position) := by
    have hc : ¬ CardsAllowed q full CB P (6 + P + position) := by
      simp only [CardsAllowed, fieldAddress, fieldFactor, fieldExtra]
      omega
    have hlf : ¬ ScanAllowed q full CB P (6 + P + position) := by
      simp only [ScanAllowed, fieldAddress, fieldFactor, fieldExtra]
      omega
    have hs : ¬ StageAllowed q full CB P (6 + P + position) := by
      simp only [StageAllowed, fieldAddress, fieldFactor, fieldExtra]
      omega
    rw [stages _ hs, leaves _ hlf, cards _ hc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Nat.add_zero (6 + P), preserve 0 (by omega)]
    exact written.1
  · intro node hn
    have he : 7 + P + node = 6 + P + (1 + node) := by omega
    rw [he, preserve (1 + node) (by omega), ← he]
    exact written.2.1 node hn
  · intro node hn
    have he : 7 + P + preparedSize q full + node = 6 + P + (1 + preparedSize q full + node) := by omega
    rw [he, preserve _ (by omega), ← he]
    exact written.2.2.1 node hn
  · intro index hi
    rw [RawTreeSerialization.givenTreeROM_children_length q full hq hl] at hi
    change index < preparedSize q full - 1 at hi
    have he : 7 + P + 2 * preparedSize q full + index = 6 + P + (1 + 2 * preparedSize q full + index) := by omega
    rw [he, preserve _ (by omega), ← he]
    exact written.2.2.2 index (by simpa only [RawTreeSerialization.givenTreeROM_children_length q full hq hl] using hi)

/-- Cardinality/internal values survive both later real producer frames. -/
theorem scalars_preserved (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat) (a b c : NatState)
    (values : ∀ node : (prepareNormalization q full).indexed.NodeId,
      a.heap (fieldAddress P full.length (preparedSize q full) .cardinality node.val) =
        (prepareNormalization q full).indexed.metadata.cardinalities.get node ∧
      a.heap (fieldAddress P full.length (preparedSize q full) .internal node.val) =
        bit ((prepareNormalization q full).indexed.metadata.isInternal.get node))
    (leaves : ScanFrame q full CB P a b) (stages : StageFrame q full CB P b c)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full)) :
    ∀ node : (prepareNormalization q full).indexed.NodeId,
      c.heap (fieldAddress P full.length (preparedSize q full) .cardinality node.val) =
        (prepareNormalization q full).indexed.metadata.cardinalities.get node ∧
      c.heap (fieldAddress P full.length (preparedSize q full) .internal node.val) =
        bit ((prepareNormalization q full).indexed.metadata.isInternal.get node) := by
  intro node
  have below := scan_regions_below_control q full CB P hlayout
  have hn : node.val < preparedSize q full := node.isLt
  have preserve (field : Field) (hf : field = .cardinality ∨ field = .internal) :
      c.heap (fieldAddress P full.length (preparedSize q full) field node.val) =
        a.heap (fieldAddress P full.length (preparedSize q full) field node.val) := by
    have hl : ¬ ScanAllowed q full CB P (fieldAddress P full.length (preparedSize q full) field node.val) := by
      rcases hf with rfl | rfl <;> simp only [ScanAllowed, fieldAddress, fieldFactor, fieldExtra] at * <;> omega
    have hs : ¬ StageAllowed q full CB P (fieldAddress P full.length (preparedSize q full) field node.val) := by
      rcases hf with rfl | rfl <;> simp only [StageAllowed, fieldAddress, fieldFactor, fieldExtra] at * <;> omega
    rw [stages _ hs, leaves _ hl]
  rw [preserve .cardinality (Or.inl rfl), preserve .internal (Or.inr rfl)]
  exact values node

/-- The stage-only footprint preserves every leaf and every tool field. -/
theorem lookup_preserved (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat) (a b : NatState)
    (frame : StageFrame q full CB P a b)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full)) :
    (∀ node : (prepareNormalization q full).indexed.NodeId,
      b.heap (fieldAddress P full.length (preparedSize q full) .leaf node.val) =
        a.heap (fieldAddress P full.length (preparedSize q full) .leaf node.val)) ∧
    (∀ tool : Fin q, b.heap (fieldAddress P full.length (preparedSize q full) .tool tool.val) =
      a.heap (fieldAddress P full.length (preparedSize q full) .tool tool.val)) := by
  have below := scan_regions_below_control q full CB P hlayout
  constructor
  · intro node
    have hn : node.val < preparedSize q full := node.isLt
    apply frame
    simp only [StageAllowed, fieldAddress, fieldFactor, fieldExtra] at *
    omega
  · intro tool
    have ht := tool.isLt
    apply frame
    simp only [StageAllowed, fieldAddress, fieldFactor, fieldExtra] at *
    omega

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
