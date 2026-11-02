module

public import Structure.PA06_A19Prepare_AllQPositive087_Front
public import Structure.PA06_A19Prepare_StrongBuilder075
public import Structure.PA06_A19Prepare_ActiveSuffix076_Run

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED positive body in ONE fixed all-q program. The actual
patched raw front, strong builder and active suffix select one witness
each, and every subsequent segment starts at the preceding actual state.
The positive skip and global HALT have not yet run in this component. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareAllQPositive087

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawIncidenceLaminarRAM RawTreePreprocessingClaims CompactControllerClaims
open PA06A19PrepareAllQCode082 (program patchedPrefix builderFront right bodyEnd)
open PA06A19PrepareInitialUsed037 (Fetched)
open PA06A19PrepareRawHeader039Body (wordRun_add)

private theorem positive_body_local (whole frontCode builtPrefix tail : List PackingOp) (endpoint : Nat)
    (prefixLength : frontCode.length = 1639)
    (builtLength : builtPrefix.length = frontCode.length + (PSTRBuildLower.CounterInit.builderCode frontCode.length).length)
    (builderLayout : frontCode ++ PSTRBuildLower.CounterInit.builderCode frontCode.length ++
      PA06A19PrepareRawActive076.bodyTail tail = whole)
    (suffixLayout : PA06A19PrepareActiveSuffix076.program builtPrefix tail = whole)
    (endpointEq : builtPrefix.length + 691 = endpoint)
    (entryRoom : builtPrefix.length ≤ whole.length)
    (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (frontWitness : ∃ firstClock ≤ PA06A19PreparePreBuild044.clockBound q full,
      let after := packingRun (controllerInput q full used) whole firstClock (natInitial.toWord (bits q full))
      PA06A19PreparePreBuild044.Data q full after ∧
        PA06A19PrepareStaticMetadata036.RawCardData q full (PA06A19PreparePreBuild044.controlBase q full)
          (PA06A19PrepareRuntimeHeader019.natView after) ∧
        after.pc.toNat = 5 * 1639 ∧ after.halted = false ∧
        ∀ count < firstClock, Fetched (allocation q full) (controllerInput q full used) whole
          (packingRun (controllerInput q full used) whole count (natInitial.toWord (bits q full))))
    (certificate : WordsFit (bits q full) (packingCode whole) ∧ Fits (bits q full) (5 * whole.length)) :
    ∃ firstClock ≤ PA06A19PreparePreBuild044.clockBound q full,
    ∃ builderClock ≤ PA06A19PreparePostDP055.builderClockBound q full,
    ∃ metadataClock ≤ PA06A19PrepareStaticMetadata036.metadataNatBound full.length q
        (PA06A19PrepareChildrenCache023.preparedSize q full),
      let total := firstClock + builderClock +
        (metadataClock + PA06A19PrepareInitialUsed037.clock q + 24)
      let rom := controllerInput q full used
      let after := packingRun rom whole total (natInitial.toWord (bits q full))
      HeapRepresents q full (capacity q full) ⟨0, used, false⟩ after.heap ∧
        after.halted = false ∧ after.pc.toNat = 5 * endpoint ∧
        ∀ count < total, Fetched (allocation q full) rom whole
          (packingRun rom whole count (natInitial.toWord (bits q full))) := by
  let rom := controllerInput q full used
  let initial := natInitial.toWord (bits q full)
  obtain ⟨firstClock, firstBound, firstPost⟩ := frontWitness
  dsimp only at firstPost
  rcases firstPost with ⟨firstData, firstRaw, firstPC, firstActive, firstPrefixes⟩
  let first := packingRun rom whole firstClock initial
  have firstPCWord : first.pc = BitVec.ofNat (bits q full) (5 * frontCode.length) := by
    rw [prefixLength]
    have self : first.pc = BitVec.ofNat (bits q full) first.pc.toNat := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have firstPCNat : first.pc.toNat = 5 * 1639 := firstPC
    rw [firstPCNat] at self
    exact self
  have builderCall := PA06A19PrepareStrongBuilder075.builder_run q full used hq hl first firstData firstRaw
    frontCode (PA06A19PrepareRawActive076.bodyTail tail) firstPCWord firstActive
    (by rw [builderLayout]; exact certificate.1)
    (by rw [builderLayout]; exact certificate.2)
  rw [builderLayout] at builderCall
  obtain ⟨builderClock, builderBound, builderPost⟩ := builderCall
  dsimp only at builderPost
  rcases builderPost with ⟨builtData, builtPC, builtActive, _cacheFrame, builderPrefixes⟩
  let built := packingRun rom whole builderClock first
  have builtPCWord : built.pc = BitVec.ofNat (bits q full) (5 * builtPrefix.length) := by
    rw [builtLength]
    exact builtPC
  have builtEntryFit : Fits (bits q full) (5 * builtPrefix.length) :=
    (Nat.mul_le_mul_left 5 entryRoom).trans_lt certificate.2
  have builtPCNat : built.pc.toNat = 5 * builtPrefix.length := by
    rw [builtPCWord, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt builtEntryFit
  have suffixCall := PA06A19PrepareActiveSuffix076.suffix_run builtPrefix tail
    q full used hq hl built builtData builtPCNat builtActive
    (by rw [suffixLayout]; exact certificate.1)
    (by rw [suffixLayout]; exact certificate.2)
  rw [suffixLayout] at suffixCall
  obtain ⟨metadataClock, metadataBound, suffixPost⟩ := suffixCall
  dsimp only at suffixPost
  rcases suffixPost with ⟨represents, active, exitPC, _address, suffixPrefixes⟩
  let suffixClock := metadataClock + PA06A19PrepareInitialUsed037.clock q + 24
  have builderRun : packingRun rom whole (firstClock + builderClock) initial = built :=
    wordRun_add rom whole firstClock builderClock initial
  have fullPrefixes := PA06A19PrepareCompletion060Canonical.fetched_add (allocation q full) rom whole initial
    firstClock builderClock firstPrefixes builderPrefixes
  have allPrefixes := PA06A19PrepareCompletion060Canonical.fetched_add (allocation q full) rom whole initial
    (firstClock + builderClock) suffixClock fullPrefixes (by
      intro count hc
      rw [builderRun]
      exact suffixPrefixes count hc)
  have completeRun : packingRun rom whole (firstClock + builderClock + suffixClock) initial =
      packingRun rom whole suffixClock built := by
    rw [wordRun_add rom whole (firstClock + builderClock) suffixClock initial, builderRun]
  refine ⟨firstClock, firstBound, builderClock, builderBound, metadataClock, metadataBound, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_, allPrefixes⟩
  · rw [completeRun]
    exact represents
  · rw [completeRun]
    exact active
  · rw [completeRun]
    simpa only [endpointEq] using exitPC

theorem positive_body (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full) :
    ∃ firstClock ≤ PA06A19PreparePreBuild044.clockBound q full,
    ∃ builderClock ≤ PA06A19PreparePostDP055.builderClockBound q full,
    ∃ metadataClock ≤ PA06A19PrepareStaticMetadata036.metadataNatBound full.length q
        (PA06A19PrepareChildrenCache023.preparedSize q full),
      let total := firstClock + builderClock +
        (metadataClock + PA06A19PrepareInitialUsed037.clock q + 24)
      let rom := controllerInput q full used
      let after := packingRun rom program total (natInitial.toWord (bits q full))
      HeapRepresents q full (capacity q full) ⟨0, used, false⟩ after.heap ∧
        after.halted = false ∧ after.pc.toNat = 5 * bodyEnd ∧
        ∀ count < total, Fetched (allocation q full) rom program
          (packingRun rom program count (natInitial.toWord (bits q full))) := by
  exact positive_body_local program patchedPrefix builderFront right bodyEnd
    PA06A19PrepareAllQCode082.patchedPrefix_length
    (by simp only [PA06A19PrepareAllQCode082.builderFront, List.length_append,
      PA06A19PrepareAllQCode082.patchedPrefix_length, PA06A19PrepareCodeFit052.builderProgram])
    PA06A19PrepareAllQCode082.builder_layout PA06A19PrepareAllQCode082.suffix_layout
    (by rw [PA06A19PrepareAllQCode082.builderFront_length]; rfl)
    (by
      rw [PA06A19PrepareAllQCode082.builderFront_length, PA06A19PrepareAllQCode082.program_length]
      unfold PA06A19PrepareAllQCode082.finalEnd PA06A19PrepareAllQCode082.handlerStart bodyEnd
      omega)
    q full used hq hl (positive_front q full used hq hl)
    (PA06A19PrepareAllQCode082.selected_certificate full.length q)

end PaperProofs.Structure.LaminarTree.PA06A19PrepareAllQPositive087
