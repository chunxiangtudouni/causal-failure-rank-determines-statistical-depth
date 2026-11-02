module

public import Structure.PA06_A19Prepare_AfterParents085_Layout

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED actual Header104 and Sequence134 in the fixed patched
program.  Parent, ordinal and card inputs are the one preceding081 output;
all relocated bank/cache inputs are produced by these two actual blocks. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareAfterParents085

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM CompactControllerClaims
open PA06A19PrepareRuntimeLayout026 (sequence sequenceClock)
open PA06A19PrepareRuntimeSequence041
open PA06A19PrepareBankData042
open PA06A19PrepareRawHeader039Body (headerClock wordRun_add)

structure RelocatedData (q : Nat) (full : List (Finset (Fin q)))
    (state : WordState (bits q full)) : Prop where
  header : PA06A19PrepareRuntimePacked016.Header q state.heap
  scalars : PA06A19PreparePreBuild044.ScalarData q full state
  copiedOrd : CopiedOrdData q full (controlBase q full) state
  copiedCards : CopiedCardData q full (controlBase q full) state
  input : PA06A19PrepareChildrenCache023.InputData q full (controlBase q full)
    (PA06A19PrepareRuntimeHeader019.natView state)

private theorem header_sequence_local (whole leftHeader rightHeader leftSequence rightSequence : List PackingOp)
    (leftHeaderLength : leftHeader.length = 1206) (leftSequenceLength : leftSequence.length = 1310)
    (headerLayout : leftHeader ++ PA06A19PrepareRawHeader039Body.headerProgram leftHeader.length ++ rightHeader = whole)
    (sequenceLayout : leftSequence ++ sequence leftSequence.length ++ rightSequence = whole)
    (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (before : WordState (bits q full))
    (parents : PA06A19PrepareCompactParents035Entry.WordParents q full before)
    (ordinal : PA06A19PrepareCompactParents035Ord.OrdData q full before)
    (cards : PA06A19PrepareCompactParents035Cards.CardData q full before)
    (certificate : WordsFit (bits q full) (packingCode whole) ∧ Fits (bits q full) (5 * whole.length)) :
    let steps := headerClock full.length q + sequenceClock full.length q
    let after := packingRun (controllerInput q full used) whole steps before
    RelocatedData q full after ∧ after.pc.toNat = 5 * 1444 ∧ after.halted = false ∧
      (∀ count < steps, PA06A19PrepareInitialUsed037.Fetched (allocation q full)
        (controllerInput q full used) whole
        (packingRun (controllerInput q full used) whole count before)) := by
  let rom := controllerInput q full used
  let M := full.length + q + 1
  let t := treeSize q full
  let middle := packingRun rom whole (headerClock full.length q) before
  have hpc : before.pc.toNat = 5 * leftHeader.length := by
    simpa only [leftHeaderLength, PA06A19PrepareCompactParents035Entry.inputStart,
      PA06A19PrepareCompactCandidates007.inputStart_eq] using parents.2.1
  have header := PA06A19PrepareRawHeader039Body.embedded_header q full used t hq
    leftHeader rightHeader before hpc parents.1
    (by rw [headerLayout]; exact certificate.2)
    (by rw [headerLayout]; exact certificate.1)
  dsimp only at header
  rw [headerLayout, leftHeaderLength] at header
  rcases header with ⟨middlePC, middleActive, middleHeader, frame, headerSafe⟩
  have headerFrame : ∀ point : BitVec (bits q full), 16 ≤ point.toNat →
      middle.heap point = before.heap point := frame
  have middleOrd := PA06A19PrepareCompactParents035Ord.ord_data_frame q full before middle frame ordinal
  have middleCards := PA06A19PrepareCompactParents035Cards.card_data_frame q full before middle frame cards
  have sourceFit (address : Nat)
      (ha : address < PA06A19PrepareCompactWord008.linearLimit full.length q) :
      Fits (bits q full) address := ha.trans (PA06A19PrepareCompactArrays018.linearLimit_fits full.length q)
  have sourceFrame (address : Nat) (h16 : 16 ≤ address)
      (ha : address < PA06A19PrepareCompactWord008.linearLimit full.length q) :
      middle.heap (BitVec.ofNat (bits q full) address) = before.heap (BitVec.ofNat (bits q full) address) := by
    apply frame
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (sourceFit address ha)]
    exact h16
  have small16 : 16 < PA06A19PrepareCompactWord008.linearLimit full.length q := by
    unfold PA06A19PrepareCompactWord008.linearLimit
    omega
  have nodeBound : 20 + 4 * M < PA06A19PrepareCompactWord008.linearLimit full.length q := by
    dsimp only [M, PA06A19PrepareCompactWord008.linearLimit]
    omega
  have hM : (middle.heap (BitVec.ofNat (bits q full) 16)).toNat = M := by
    rw [sourceFrame 16 (by decide) small16]
    exact parents.2.2.2.1
  have htree : t = (prepareNormalization q full).indexed.nodes.size := by
    dsimp only [t, treeSize]
    rw [ite_eq_right (Nat.ne_of_gt hq)]
  have nodeAddress : RawCandidateParentRAM.nodeCountAddress 16 M = 20 + 4 * M := by
    unfold RawCandidateParentRAM.nodeCountAddress RawCandidateOrderingRAM.arraySlot
    omega
  have ht : (middle.heap (BitVec.ofNat (bits q full) (20 + 4 * M))).toNat = t := by
    rw [sourceFrame _ (by omega) nodeBound, ← nodeAddress]
    exact parents.2.2.2.2.1.trans htree.symm
  have sequencePC : middle.pc.toNat = 5 * leftSequence.length := by
    rw [leftSequenceLength]
    exact middlePC
  have hcode : WordsFit (bits q full)
      (packingCode (leftSequence ++ sequence leftSequence.length ++ rightSequence)) := by
    rw [sequenceLayout]
    exact certificate.1
  have hend : Fits (bits q full)
      (5 * (leftSequence ++ sequence leftSequence.length ++ rightSequence).length) := by
    rw [sequenceLayout]
    exact certificate.2
  have data := embedded_sequence_data q full used hq leftSequence rightSequence middle
    sequencePC middleActive hM ht middleHeader hcode hend
  have bank := embedded_bankData_pair q full used hq leftSequence rightSequence middle
    sequencePC middleActive hM ht middleHeader hcode hend
  have extra := embedded_extra_bankData q full used hq leftSequence rightSequence middle
    sequencePC middleActive hM ht middleHeader hcode hend
  have children := embedded_children_input q full used hq leftSequence rightSequence before middle
    parents headerFrame sequencePC middleActive middleHeader hcode hend
  have copiedOrd := embedded_copied_ord q full used hq leftSequence rightSequence middle middleOrd
    sequencePC middleActive hM ht middleHeader hcode hend
  have copiedCards := embedded_copied_cards q full used hq leftSequence rightSequence middle middleCards
    sequencePC middleActive hM ht middleHeader hcode hend
  have finalHeader := embedded_sequence_header q full used hq leftSequence rightSequence middle
    sequencePC middleActive hM ht middleHeader hcode hend
  rw [sequenceLayout] at data bank extra children copiedOrd copiedCards finalHeader
  have first : ∀ count < headerClock full.length q,
      PA06A19PrepareInitialUsed037.Fetched (allocation q full) rom whole
        (packingRun rom whole count before) := headerSafe
  have second : ∀ count < sequenceClock full.length q,
      PA06A19PrepareInitialUsed037.Fetched (allocation q full) rom whole
        (packingRun rom whole count middle) := by
    intro count bound
    have safe := embedded_sequence_prefix_access q full used hq leftSequence rightSequence middle
      sequencePC middleActive hM ht middleHeader hcode hend count bound
    rw [sequenceLayout] at safe
    exact safe
  have allSafe : ∀ count < headerClock full.length q + sequenceClock full.length q,
      PA06A19PrepareInitialUsed037.Fetched (allocation q full) rom whole
        (packingRun rom whole count before) := by
    intro count bound
    by_cases early : count < headerClock full.length q
    · exact first count early
    · have split : count = headerClock full.length q + (count - headerClock full.length q) := by omega
      have safe := second (count - headerClock full.length q) (by omega)
      rw [split, wordRun_add]
      exact safe
  dsimp only
  refine ⟨?_, ?_, ?_, allSafe⟩
  · rw [wordRun_add]
    exact ⟨finalHeader, ⟨bank.1, bank.2, extra.1, extra.2⟩, copiedOrd, copiedCards, children⟩
  · rw [wordRun_add]
    have pcEnd := data.2.1
    rw [leftSequenceLength] at pcEnd
    exact pcEnd
  · rw [wordRun_add]
    exact data.1


theorem header_sequence (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (before : WordState (bits q full))
    (parents : PA06A19PrepareCompactParents035Entry.WordParents q full before)
    (ordinal : PA06A19PrepareCompactParents035Ord.OrdData q full before)
    (cards : PA06A19PrepareCompactParents035Cards.CardData q full before) :
    let steps := headerClock full.length q + sequenceClock full.length q
    let after := packingRun (controllerInput q full used) program steps before
    RelocatedData q full after ∧ after.pc.toNat = 5 * 1444 ∧ after.halted = false ∧
      Safe q full used before steps := by
  simpa only [Safe] using
    (header_sequence_local PA06A19PrepareAllQCode082.program headerLeft headerRight
      sequenceLeft sequenceRight headerLeft_length sequenceLeft_length header_layout sequence_layout
      q full used hq before parents ordinal cards
      (PA06A19PrepareAllQCode082.selected_certificate full.length q))

end PaperProofs.Structure.LaminarTree.PA06A19PrepareAfterParents085
