module

public import Structure.PA06_A19Prepare_RawActive076_Layout
public import Structure.PA06_A19Prepare_ActiveSuffix076_Run
public import Structure.PA06_A19Prepare_StrongBuilder075

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED actual positive raw body in the selected containing code.
One048 clock, ONE strong161 builder witness and one532 metadata clock are
joined directly. The arbitrary tail is not executed. Original caller-free
fixed code eligibility must be discharged by Root for its final program. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareRawActive076

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims CompactControllerClaims RawIncidenceLaminarRAM
open PA06A19PreparePreBuild044 (bits capacity allocation)
open PA06A19PrepareInitialUsed037 (Fetched)

private theorem raw_active_local (whole frontCode builtPrefix tail : List PackingOp) (endpoint : Nat)
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
    PA06A19PrepareRawHeader039Body.wordRun_add rom whole firstClock builderClock initial
  have fullPrefixes := PA06A19PrepareCompletion060Canonical.fetched_add (allocation q full) rom whole initial
    firstClock builderClock firstPrefixes builderPrefixes
  have allPrefixes := PA06A19PrepareCompletion060Canonical.fetched_add (allocation q full) rom whole initial
    (firstClock + builderClock) suffixClock fullPrefixes (by
      intro count hc
      rw [builderRun]
      exact suffixPrefixes count hc)
  have completeRun : packingRun rom whole (firstClock + builderClock + suffixClock) initial =
      packingRun rom whole suffixClock built := by
    rw [PA06A19PrepareRawHeader039Body.wordRun_add rom whole (firstClock + builderClock) suffixClock initial, builderRun]
  refine ⟨firstClock, firstBound, builderClock, builderBound, metadataClock, metadataBound, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_, allPrefixes⟩
  · rw [completeRun]
    exact represents
  · rw [completeRun]
    exact active
  · rw [completeRun]
    simpa only [endpointEq] using exitPC

theorem raw_active (right : List PackingOp) (q : Nat)
    (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (hcode : WordsFit (bits q full) (packingCode (program right)))
    (hcodePC : Fits (bits q full) (5 * (program right).length)) :
    ∃ firstClock ≤ PA06A19PreparePreBuild044.clockBound q full,
    ∃ builderClock ≤ PA06A19PreparePostDP055.builderClockBound q full,
    ∃ metadataClock ≤ PA06A19PrepareStaticMetadata036.metadataNatBound full.length q
        (PA06A19PrepareChildrenCache023.preparedSize q full),
      let total := firstClock + builderClock +
        (metadataClock + PA06A19PrepareInitialUsed037.clock q + 24)
      let rom := controllerInput q full used
      let after := packingRun rom (program right) total (natInitial.toWord (bits q full))
      HeapRepresents q full (capacity q full) ⟨0, used, false⟩ after.heap ∧
      after.halted = false ∧ after.pc.toNat = 5 * (builderEnd + 691) ∧
      ∀ count < total, Fetched (allocation q full) rom (program right)
        (packingRun rom (program right) count (natInitial.toWord (bits q full))) := by
  exact raw_active_local (program right) (front right) (builderFront right) right (builderEnd + 691)
    (front_length right)
    (by rw [builderFront, List.length_append, front_length])
    (builder_layout right) (suffix_layout right)
    (by rw [builderFront_length])
    (by rw [builderFront_length, program_length]; omega)
    q full used hq hl (by
      obtain ⟨firstClock, firstBound, firstPost⟩ :=
        PA06A19PreparePreBuildCards048.raw_prebuild_cards_entry q full
          (PA06A19PreparePostDP055.tail (bodyTail right)) used hq hl hcodePC hcode
      dsimp only at firstPost
      rcases firstPost with ⟨firstData, _copiedCards, firstRaw, firstPC, firstActive, firstPrefixes⟩
      exact ⟨firstClock, firstBound, firstData, firstRaw, firstPC, firstActive, firstPrefixes⟩)
    ⟨hcode, hcodePC⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareRawActive076
