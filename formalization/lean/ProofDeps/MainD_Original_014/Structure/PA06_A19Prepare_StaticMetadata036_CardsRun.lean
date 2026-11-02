module

public import Structure.PA06_A19Prepare_StaticMetadata036_CardsChunks

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Complete actual84-op node loop for cardinalities and internal bits.
Every iteration executes both existing scalar producers and a real backjump.
The total13+80t includes both exhausted/initial loop-control paths. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (preparedSize mass loadRel storeRel setRel)

def cardsPairHeap (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat)
    (node : (prepareNormalization q full).indexed.NodeId) (heap : Nat → Nat) : Nat → Nat :=
  Function.update (Function.update (Function.update heap
    (fieldAddress P full.length (preparedSize q full) .cardinality node.val)
      ((prepareNormalization q full).indexed.metadata.cardinalities.get node))
    (fieldAddress P full.length (preparedSize q full) .internal node.val)
      (bit ((prepareNormalization q full).indexed.metadata.isInternal.get node))) (CB + 19) (node.val + 1)

theorem cards_pair_ready (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat)
    (node : (prepareNormalization q full).indexed.NodeId) (pointer : Nat) (before after : NatState)
    (ready : CardsReady q full CB P node.val pointer before)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
    (hh : after.heap = cardsPairHeap q full CB P node before.heap)
    (hCB : after.register .address = CB) (hpc : after.pc = pointer) (ha : after.halted = false) :
    CardsReady q full CB P (node.val + 1) pointer after ∧ CardsFrame q full CB P before after := by
  have frame : CardsFrame q full CB P before after := by
    intro address hn
    have h19 : address ≠ CB + 19 := by unfold CardsAllowed at hn; omega
    have hcard : address ≠ fieldAddress P full.length (preparedSize q full) .cardinality node.val := by
      have hnode : node.val < preparedSize q full := node.isLt
      simp only [CardsAllowed, fieldAddress, fieldFactor, fieldExtra] at hn ⊢
      omega
    have hint : address ≠ fieldAddress P full.length (preparedSize q full) .internal node.val := by
      have hnode : node.val < preparedSize q full := node.isLt
      simp only [CardsAllowed, fieldAddress, fieldFactor, fieldExtra] at hn ⊢
      omega
    rw [hh]
    simp [cardsPairHeap, h19, hcard, hint]
  have below := cards_regions_below_control q full CB P hlayout
  have card_before_internal (left right : (prepareNormalization q full).indexed.NodeId) :
      fieldAddress P full.length (preparedSize q full) .cardinality left.val <
        fieldAddress P full.length (preparedSize q full) .internal right.val := by
    have hleft : left.val < preparedSize q full := left.isLt
    simp only [fieldAddress, fieldFactor, fieldExtra]
    omega
  refine ⟨?_, frame⟩
  constructor
  · exact ScanInput.of_cardsFrame ready.input hlayout frame hCB
  · rw [hh]
    simp only [cardsPairHeap, Function.update_self]
  · intro earlier he
    have hn : earlier.val < preparedSize q full := earlier.isLt
    have hnode : node.val < preparedSize q full := node.isLt
    have hcard : fieldAddress P full.length (preparedSize q full) .cardinality earlier.val < CB := by
      simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
      omega
    have hint : fieldAddress P full.length (preparedSize q full) .internal earlier.val < CB := by
      simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
      omega
    have hcardControl : fieldAddress P full.length (preparedSize q full) .cardinality earlier.val ≠ CB + 19 := by
      omega
    have hintControl : fieldAddress P full.length (preparedSize q full) .internal earlier.val ≠ CB + 19 := by
      omega
    have hcardCross : fieldAddress P full.length (preparedSize q full) .cardinality earlier.val ≠
        fieldAddress P full.length (preparedSize q full) .internal node.val :=
      ne_of_lt (card_before_internal earlier node)
    have hintCross : fieldAddress P full.length (preparedSize q full) .internal earlier.val ≠
        fieldAddress P full.length (preparedSize q full) .cardinality node.val :=
      (ne_of_lt (card_before_internal node earlier)).symm
    by_cases hprev : earlier.val < node.val
    · have previous := ready.values earlier hprev
      have hcardIndex : fieldAddress P full.length (preparedSize q full) .cardinality earlier.val ≠
          fieldAddress P full.length (preparedSize q full) .cardinality node.val := by
        simp only [fieldAddress]
        omega
      have hintIndex : fieldAddress P full.length (preparedSize q full) .internal earlier.val ≠
          fieldAddress P full.length (preparedSize q full) .internal node.val := by
        simp only [fieldAddress]
        omega
      rw [hh]
      simpa [cardsPairHeap, hcardControl, hintControl, hcardCross, hintCross, hcardIndex, hintIndex] using previous
    · have heq : earlier = node := Fin.ext (by omega)
      subst earlier
      rw [hh]
      simp [cardsPairHeap, hcardControl, hintControl, hcardCross]
  · exact hpc
  · exact ha

section Actual
variable (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat)
  (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
  (containing : List PackingOp) (start : Nat) (code : CardsCodeAt containing start)

include hlayout code

theorem cards_iteration (node : (prepareNormalization q full).indexed.NodeId) (before : NatState)
    (ready : CardsReady q full CB P node.val (5 * (start + 4)) before) :
    let after := natRun (rawIncidenceROM q full) containing 80 before
    CardsReady q full CB P (node.val + 1) (5 * (start + 4)) after ∧ CardsFrame q full CB P before after := by
  let rom := rawIncidenceROM q full
  let tested := runOps rom (scanBoundedTest 2 19 (start + 84)) before
  have htPC : tested.pc = 5 * (start + 13) := by
    rw [scanBoundedTest_pc rom CB (preparedSize q full) node.val 2 19 (start + 84) before
      ready.input.address ready.input.nodes ready.node_cell, ite_eq_right (by have hn : node.val < preparedSize q full := node.isLt; omega), ready.pc]
    omega
  have htActive : tested.halted = false := (runOps_halted rom _ before).trans ready.active
  have testedHeap : tested.heap = before.heap := rfl
  have testedNode : tested.heap (CB + 19) = node.val := by
    rw [testedHeap]
    exact ready.node_cell
  let stored := runOps rom cardsBody tested
  have testedInput : ScanInput q full CB P tested :=
    ScanInput.of_frame ready.input hlayout (fun _ _ => rfl) ready.input.address
  have body := cardsBody_effect q full CB P node tested testedInput testedNode hlayout
  have bodyHeap : stored.heap = Function.update
      (Function.update before.heap (fieldAddress P full.length (preparedSize q full) .cardinality node.val)
        ((prepareNormalization q full).indexed.metadata.cardinalities.get node))
      (fieldAddress P full.length (preparedSize q full) .internal node.val)
        (bit ((prepareNormalization q full).indexed.metadata.isInternal.get node)) := by
    simpa only [testedHeap] using body.2
  have below := cards_regions_below_control q full CB P hlayout
  have hn : node.val < preparedSize q full := node.isLt
  have hcard : fieldAddress P full.length (preparedSize q full) .cardinality node.val < CB := by
    simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
    omega
  have hint : fieldAddress P full.length (preparedSize q full) .internal node.val < CB := by
    simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
    omega
  have storedNode : stored.heap (CB + 19) = node.val := by
    rw [bodyHeap, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact ready.node_cell
  have storedPC : stored.pc = 5 * (start + 73) := by
    rw [runOps_pc rom _ tested cardsBody_noJump, htPC, cardsBody_length]
    omega
  have storedActive : stored.halted = false := (runOps_halted rom _ tested).trans htActive
  let after := runOps rom (cardsTail start) stored
  have tail : after.register .address = CB ∧
      after.heap = Function.update stored.heap (CB + 19) (node.val + 1) ∧
      after.pc = 5 * (start + 4) ∧ after.halted = stored.halted := by
    simpa only [after, cardsTail] using
      (stageTail_effect rom CB node.val 19 (start + 4) stored body.1 storedNode)
  have hh : after.heap = cardsPairHeap q full CB P node before.heap := by
    rw [tail.2.1, bodyHeap]
    rfl
  have next := cards_pair_ready q full CB P node (5 * (start + 4)) before after ready hlayout hh
    tail.1 tail.2.2.1 ((tail.2.2.2).trans storedActive)
  have testedRun : natRun (rawIncidenceROM q full) containing 9 before = tested :=
    cards_chunk_run rom containing start code .test before ready.pc ready.active
  have bodyRun : natRun (rawIncidenceROM q full) containing 60 tested = stored :=
    cards_chunk_run rom containing start code .body tested htPC htActive
  have tailRun : natRun (rawIncidenceROM q full) containing 11 stored = after :=
    cards_chunk_run rom containing start code .tail stored storedPC storedActive
  rw [show (80 : Nat) = 9 + 60 + 11 by decide, natRun_add, natRun_add,
    testedRun, bodyRun, tailRun]
  exact next

theorem cards_scan_partial (before : NatState) (ready : CardsReady q full CB P 0 (5 * (start + 4)) before)
    (count : Nat) (hc : count ≤ preparedSize q full) :
    let after := natRun (rawIncidenceROM q full) containing (80 * count) before
    CardsReady q full CB P count (5 * (start + 4)) after ∧ CardsFrame q full CB P before after := by
  revert hc
  induction count with
  | zero =>
    intro _
    exact ⟨ready, CardsFrame.refl q full CB P before⟩
  | succ count ih =>
    intro hc
    obtain ⟨previousReady, previousFrame⟩ := ih (by omega)
    let previous := natRun (rawIncidenceROM q full) containing (80 * count) before
    have within : count < preparedSize q full := by omega
    have next := cards_iteration q full CB P hlayout containing start code ⟨count, within⟩ previous previousReady
    rw [Nat.mul_succ, natRun_add]
    exact ⟨next.1, previousFrame.trans next.2⟩

end Actual

/-- Full concrete cardinality/internal producer. No corresponding original
metadata values or loop-completion premise is supplied to this theorem. -/
theorem cards_build (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat)
    (containing : List PackingOp) (start : Nat) (code : CardsCodeAt containing start)
    (before : NatState) (input : ScanInput q full CB P before)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
    (hpc : before.pc = 5 * start) (ha : before.halted = false) :
    let after := natRun (rawIncidenceROM q full) containing (13 + 80 * preparedSize q full) before
    ScanInput q full CB P after ∧
      (∀ node : (prepareNormalization q full).indexed.NodeId,
        after.heap (fieldAddress P full.length (preparedSize q full) .cardinality node.val) =
          (prepareNormalization q full).indexed.metadata.cardinalities.get node ∧
        after.heap (fieldAddress P full.length (preparedSize q full) .internal node.val) =
          bit ((prepareNormalization q full).indexed.metadata.isInternal.get node)) ∧
      CardsFrame q full CB P before after ∧ after.register .address = CB ∧
      after.pc = 5 * (start + 84) ∧ after.halted = false := by
  let rom := rawIncidenceROM q full
  let initialized := runOps rom (setRel 19 0) before
  have hh : initialized.heap = Function.update before.heap (CB + 19) 0 := by
    simpa only [initialized, input.address] using PA06A19PrepareChildrenCache023.setRel_heap rom 19 0 before
  have frame : CardsFrame q full CB P before initialized := by
    intro address hn
    have h19 : address ≠ CB + 19 := by unfold CardsAllowed at hn; omega
    rw [hh, Function.update_of_ne h19]
  have initPC : initialized.pc = 5 * (start + 4) := by
    rw [runOps_pc rom _ before (by simp [setRel, storeRel, NoJump]), hpc,
      show (setRel 19 0).length = 4 from rfl]
    omega
  have initActive : initialized.halted = false := (runOps_halted rom _ before).trans ha
  have ready : CardsReady q full CB P 0 (5 * (start + 4)) initialized := by
    refine ⟨ScanInput.of_cardsFrame input hlayout frame input.address, ?_, ?_, initPC, initActive⟩
    · rw [hh, Function.update_self]
    · intro node hn
      omega
  have scan := cards_scan_partial q full CB P hlayout containing start code initialized ready (preparedSize q full) le_rfl
  let scanned := natRun rom containing (80 * preparedSize q full) initialized
  let after := runOps rom (scanBoundedTest 2 19 (start + 84)) scanned
  have endPC : after.pc = 5 * (start + 84) := by
    rw [scanBoundedTest_pc rom CB (preparedSize q full) (preparedSize q full) 2 19 (start + 84) scanned
      scan.1.input.address scan.1.input.nodes scan.1.node_cell, Nat.sub_self, ite_eq_left rfl]
  have endActive : after.halted = false := (runOps_halted rom _ scanned).trans scan.1.active
  have endFrame : CardsFrame q full CB P scanned after := fun _ _ => rfl
  have initRun : natRun rom containing 4 before = initialized :=
    cards_chunk_run rom containing start code .initialize before
      (by simpa only [cardsChunkOffset, Nat.add_zero] using hpc) ha
  have scannedRun : natRun rom containing (4 + 80 * preparedSize q full) before = scanned :=
    (natRun_add rom containing 4 (80 * preparedSize q full) before).trans
      (congrArg (natRun rom containing (80 * preparedSize q full)) initRun)
  have endTestRun : natRun rom containing 9 scanned = after :=
    cards_chunk_run rom containing start code .test scanned scan.1.pc scan.1.active
  have actual : natRun (rawIncidenceROM q full) containing (13 + 80 * preparedSize q full) before = after := by
    change natRun rom containing (13 + 80 * preparedSize q full) before = after
    rw [show 13 + 80 * preparedSize q full = 4 + 80 * preparedSize q full + 9 by omega]
    exact (natRun_add rom containing (4 + 80 * preparedSize q full) 9 before).trans
      ((congrArg (natRun rom containing 9) scannedRun).trans endTestRun)
  rw [actual]
  have endInput : ScanInput q full CB P after :=
    ScanInput.of_cardsFrame scan.1.input hlayout endFrame scan.1.input.address
  refine ⟨endInput, ?_, (frame.trans scan.2).trans endFrame, scan.1.input.address, endPC, endActive⟩
  intro node
  exact scan.1.values node node.isLt

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
