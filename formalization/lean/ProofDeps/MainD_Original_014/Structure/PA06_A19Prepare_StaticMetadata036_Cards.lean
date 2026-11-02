module

public import Structure.PA06_A19Prepare_StaticMetadata036_CompleteSpec

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Fixed84-op cardinality/internal outer loop, reusing both already stated
actual scalar programs. Only producerCB19 is used. It rereads real ord/card
cells rather than assuming the corresponding original metadata values. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (preparedSize mass loadRel storeRel setRel incrementRel)

def cardsBody : List PackingOp :=
  loadRel .old 19 ++ scalarProgram .cardinality ++ scalarProgram .internal

def cardsTail (start : Nat) : List PackingOp := incrementRel 19 ++ jumpTo (start + 4)

def cardsProgramAt (start : Nat) : List PackingOp :=
  setRel 19 0 ++ scanBoundedTest 2 19 (start + 84) ++ cardsBody ++ cardsTail start

theorem cardsBody_length : cardsBody.length = 60 := rfl
theorem cardsProgramAt_length (start : Nat) : (cardsProgramAt start).length = 84 := rfl

theorem cardsBody_noJump : ∀ op ∈ cardsBody, NoJump op := by
  simp [cardsBody, loadRel, scalarProgram, scalarTransform, scalarField, cardProgram,
    internalFlag, storeField, fieldPointer, fieldPointerLead, fieldPointerExtra, NoJump]

/-- Every original raw-cache read is above a real ordinary metadata store. -/
theorem RawCardData.of_below_write {q : Nat} {full : List (Finset (Fin q))} {CB address value : Nat}
    {before after : NatState} (data : RawCardData q full CB before) (haddress : address < CB)
    (hh : after.heap = Function.update before.heap address value) : RawCardData q full CB after := by
  constructor
  · rw [hh, Function.update_of_ne (by omega)]
    exact data.mass_cell
  · intro candidate
    rw [hh, Function.update_of_ne (by unfold rawCardAddress; omega)]
    exact data.cards candidate
  · intro node
    obtain ⟨candidate, hord, hsupport⟩ := data.ordered node
    refine ⟨candidate, ?_, hsupport⟩
    rw [hh, Function.update_of_ne (by unfold rawOrdAddress; omega)]
    exact hord

theorem cardsBody_effect (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat)
    (node : (prepareNormalization q full).indexed.NodeId) (before : NatState)
    (input : ScanInput q full CB P before) (hnode : before.heap (CB + 19) = node.val)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full)) :
    let after := runOps (rawIncidenceROM q full) cardsBody before
    after.register .address = CB ∧ after.heap = Function.update
      (Function.update before.heap (fieldAddress P full.length (preparedSize q full) .cardinality node.val)
        ((prepareNormalization q full).indexed.metadata.cardinalities.get node))
      (fieldAddress P full.length (preparedSize q full) .internal node.val)
        (bit ((prepareNormalization q full).indexed.metadata.isInternal.get node)) := by
  let rom := rawIncidenceROM q full
  let loaded := runOps rom (loadRel .old 19) before
  have loadedHeap : loaded.heap = before.heap := rfl
  have loadedOld : loaded.register .old = node.val := by
    simp [loaded, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute, input.address, hnode]
  let first := runOps rom (scalarProgram .cardinality) loaded
  have loadedRaw : RawCardData q full CB loaded :=
    RawCardData.of_children_frame input.raw (fun _ _ => rfl)
  have firstEffect := scalarProgram_effect rom q full CB P .cardinality loaded loadedRaw node input.address loadedOld
    input.nodes input.base input.stages
  have firstHeap : first.heap = Function.update before.heap
      (fieldAddress P full.length (preparedSize q full) .cardinality node.val)
      ((prepareNormalization q full).indexed.metadata.cardinalities.get node) := by
    simpa only [scalarField, scalarValue, loadedHeap] using firstEffect.2.2.2
  have below := scan_regions_below_control q full CB P hlayout
  have hn : node.val < preparedSize q full := node.isLt
  have hcard : fieldAddress P full.length (preparedSize q full) .cardinality node.val < CB := by
    simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
    omega
  have firstData : RawCardData q full CB first :=
    RawCardData.of_below_write input.raw hcard firstHeap
  have firstT : first.heap (CB + 2) = preparedSize q full := by
    rw [firstHeap, Function.update_of_ne (by omega)]
    exact input.nodes
  have firstBase : first.heap (CB + 6) = 4 + P := by
    rw [firstHeap, Function.update_of_ne (by omega)]
    exact input.base
  have firstN : first.heap (CB + 0) = full.length := by
    rw [firstHeap, Function.update_of_ne (by omega)]
    exact input.stages
  have secondEffect := scalarProgram_effect rom q full CB P .internal first firstData node firstEffect.1 firstEffect.2.1
    firstT firstBase firstN
  have secondHeap : (runOps rom (scalarProgram .internal) first).heap = Function.update
      (Function.update before.heap (fieldAddress P full.length (preparedSize q full) .cardinality node.val)
        ((prepareNormalization q full).indexed.metadata.cardinalities.get node))
      (fieldAddress P full.length (preparedSize q full) .internal node.val)
        (bit ((prepareNormalization q full).indexed.metadata.isInternal.get node)) := by
    simpa only [scalarField, scalarValue, firstHeap] using secondEffect.2.2.2
  simp only [cardsBody, runOps_append]
  exact ⟨secondEffect.1, by simpa only [rom, first, loaded] using secondHeap⟩

def CardsAllowed (q : Nat) (full : List (Finset (Fin q))) (CB P address : Nat) : Prop :=
  address = CB + 19 ∨
  (fieldAddress P full.length (preparedSize q full) .cardinality 0 ≤ address ∧
    address < fieldAddress P full.length (preparedSize q full) .cardinality 0 + preparedSize q full) ∨
  (fieldAddress P full.length (preparedSize q full) .internal 0 ≤ address ∧
    address < fieldAddress P full.length (preparedSize q full) .internal 0 + preparedSize q full)

def CardsFrame (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat) (before after : NatState) : Prop :=
  ∀ address, ¬ CardsAllowed q full CB P address → after.heap address = before.heap address

theorem CardsFrame.refl (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat) (state : NatState) :
    CardsFrame q full CB P state state := fun _ _ => rfl

theorem CardsFrame.trans {q : Nat} {full : List (Finset (Fin q))} {CB P : Nat} {a b c : NatState}
    (hab : CardsFrame q full CB P a b) (hbc : CardsFrame q full CB P b c) : CardsFrame q full CB P a c :=
  fun address hn => (hbc address hn).trans (hab address hn)

theorem cards_regions_below_control (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full)) :
    fieldAddress P full.length (preparedSize q full) .cardinality 0 + preparedSize q full ≤ CB ∧
      fieldAddress P full.length (preparedSize q full) .internal 0 + preparedSize q full ≤ CB := by
  have below := scan_regions_below_control q full CB P hlayout
  simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
  omega

theorem ScanInput.of_cardsFrame {q : Nat} {full : List (Finset (Fin q))} {CB P : Nat}
    {before after : NatState} (input : ScanInput q full CB P before)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
    (frame : CardsFrame q full CB P before after) (hCB : after.register .address = CB) : ScanInput q full CB P after := by
  have below := cards_regions_below_control q full CB P hlayout
  have preserve (address : Nat) (ha : CB ≤ address) (h19 : address ≠ CB + 19) : after.heap address = before.heap address := by
    apply frame
    unfold CardsAllowed
    omega
  refine ⟨hCB, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rw [preserve _ (by omega) (by omega)]
      exact input.raw.mass_cell
    · intro candidate
      rw [preserve _ (by unfold rawCardAddress; omega) (by unfold rawCardAddress; omega)]
      exact input.raw.cards candidate
    · intro node
      obtain ⟨candidate, hord, hsupport⟩ := input.raw.ordered node
      refine ⟨candidate, ?_, hsupport⟩
      rw [preserve _ (by unfold rawOrdAddress; omega) (by unfold rawOrdAddress; omega)]
      exact hord
  · rw [preserve _ (by omega) (by omega)]; exact input.stages
  · rw [preserve _ (by omega) (by omega)]; exact input.tools
  · rw [preserve _ (by omega) (by omega)]; exact input.nodes
  · rw [preserve _ (by omega) (by omega)]; exact input.base

structure CardsReady (q : Nat) (full : List (Finset (Fin q))) (CB P upto pc : Nat) (state : NatState) : Prop where
  input : ScanInput q full CB P state
  node_cell : state.heap (CB + 19) = upto
  values : ∀ node : (prepareNormalization q full).indexed.NodeId, node.val < upto →
    state.heap (fieldAddress P full.length (preparedSize q full) .cardinality node.val) =
      (prepareNormalization q full).indexed.metadata.cardinalities.get node ∧
    state.heap (fieldAddress P full.length (preparedSize q full) .internal node.val) =
      bit ((prepareNormalization q full).indexed.metadata.isInternal.get node)
  pc : state.pc = pc
  active : state.halted = false

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
