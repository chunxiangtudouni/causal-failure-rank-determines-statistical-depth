module

public import Structure.PA06_A19Prepare_AfterParents085_Cache

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED actual51-op clear/VM continuation in the fixed patched
program.  Its own permanent frame retains all real high-cache data. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareAfterParents085

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM CompactControllerClaims
open PA06A19PreparePreBuild044 (CachedData Data control_cell_fits high_cell_fits
  copiedOrd_of_frame ordinal_bounds outputData_of_high_frame)

private theorem clear_stage_local (whole left right : List PackingOp)
    (leftLength : left.length = 1588)
    (layout : left ++ PA06A19PrepareClearVM045.programAt left.length ++ right = whole)
    (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (before : WordState (bits q full))
    (hpc : before.pc.toNat = 5 * 1588) (ha : before.halted = false)
    (data : CachedData q full before)
    (cards : PA06A19PrepareBankData042.CopiedCardData q full (controlBase q full) before)
    (certificate : WordsFit (bits q full) (packingCode whole) ∧ Fits (bits q full) (5 * whole.length)) :
    let after := packingRun (controllerInput q full used) whole
      (PA06A19PrepareClearVM045.clock full.length q (treeSize q full)) before
    Data q full after ∧
      PA06A19PrepareBankData042.CopiedCardData q full (controlBase q full) after ∧ after.pc.toNat = 5 * 1639 ∧ after.halted = false ∧
      (∀ count < PA06A19PrepareClearVM045.clock full.length q (treeSize q full),
        PA06A19PrepareInitialUsed037.Fetched (allocation q full) (controllerInput q full used) whole
          (packingRun (controllerInput q full used) whole count before)) := by
  have hp : before.pc.toNat = 5 * left.length := by
    rw [leftLength]; exact hpc
  have hc : WordsFit (bits q full)
      (packingCode (left ++ PA06A19PrepareClearVM045.programAt left.length ++ right)) := by
    rw [layout]; exact certificate.1
  have he : Fits (bits q full)
      (5 * (left ++ PA06A19PrepareClearVM045.programAt left.length ++ right).length) := by
    rw [layout]; exact certificate.2
  have result := PA06A19PrepareClearVM045.actual_data q full used hq left
    right before hp ha data.scalars.bank032 hc he data.header
  rw [layout] at result
  dsimp only at result
  rcases result with ⟨zeroView, bounded, header, address, pc, active, vm, _lower, _outer⟩
  let after := packingRun (controllerInput q full used) whole
    (PA06A19PrepareClearVM045.clock full.length q (treeSize q full)) before
  have permanent (point : BitVec (bits q full))
      (hpoint : (controlBase q full ≤ point.toNat ∧ point.toNat < controlBase q full + 32) ∨
        controlBase q full + 39 ≤ point.toNat) : after.heap point = before.heap point := by
    have hh := PA06A19PrepareClearVM045.actual_permanent_frame q full used hq left
      right before hp ha data.scalars.bank032 hc he data.header point hpoint
    rw [layout] at hh
    exact hh
  have scalarFrame (offset : Nat) (ho : offset < 7) :
      after.heap (BitVec.ofNat _ (controlBase q full + offset)) =
        before.heap (BitVec.ofNat _ (controlBase q full + offset)) := by
    apply permanent
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (control_cell_fits q full hq offset (by omega))]
    dsimp only [PA06A19PrepareAfterParents085.controlBase, PA06A19PreparePreBuild044.controlBase]
    exact Or.inl ⟨by omega, by omega⟩
  have highFrame (a : Nat) (ha0 : controlBase q full + 512 ≤ a)
      (ha1 : a ≤ PA06A19PrepareChildrenCache023.highCacheEnd
        (controlBase q full) (PA06A19PrepareChildrenCache023.mass q full)) :
      after.heap (BitVec.ofNat _ a) = before.heap (BitVec.ofNat _ a) := by
    apply permanent
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (high_cell_fits q full hq a ha1)]
    exact Or.inr (by omega)
  have newCards : PA06A19PrepareBankData042.CopiedCardData q full (controlBase q full) after := by
    constructor
    · have preserved := highFrame (controlBase q full + 528) (by omega) (by
        unfold PA06A19PrepareChildrenCache023.highCacheEnd
        omega)
      rw [preserved]
      exact cards.mass_cell
    · intro candidate
      let location := controlBase q full + 512 +
        PA06A19PrepareCompactParents035Cards.cardSlot full.length q candidate.val
      have candidateBound := candidate.isLt
      have preserved : after.heap (BitVec.ofNat _ location) = before.heap (BitVec.ofNat _ location) :=
        highFrame location (by
          unfold location PA06A19PrepareCompactParents035Cards.cardSlot RawCandidateOrderingRAM.arraySlot
          omega) (by
          unfold location PA06A19PrepareCompactParents035Cards.cardSlot RawCandidateOrderingRAM.arraySlot
            PA06A19PrepareChildrenCache023.highCacheEnd PA06A19PrepareChildrenCache023.mass
          omega)
      rw [preserved]
      exact cards.cards candidate
  have ord : PA06A19PrepareBankData042.CopiedOrdData q full (controlBase q full) after := by
    apply copiedOrd_of_frame data.copiedOrd
    intro node
    apply highFrame _ (ordinal_bounds q full node).1
    have hn := (ordinal_bounds q full node).2
    unfold PA06A19PrepareChildrenCache023.degreeBase at hn
    unfold PA06A19PrepareChildrenCache023.highCacheEnd
    dsimp only [PA06A19PrepareAfterParents085.controlBase, PA06A19PreparePreBuild044.controlBase] at hn ⊢
    omega
  have cache := outputData_of_high_frame q full hq hl before after data.cache address highFrame
  have hbaseWord : before.register .address = BitVec.ofNat (bits q full) (controlBase q full) := by
    have hbaseFit : Fits (bits q full) (controlBase q full) := by
      simpa only [Nat.add_zero] using control_cell_fits q full hq 0 (by decide)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbaseFit]
    exact data.scalars.bank032.base
  have vmActual : ∀ slot, 32 ≤ slot → slot < 39 →
      after.heap (BitVec.ofNat _ (controlBase q full + slot)) = 0 := by
    intro slot hlo hhi
    have hh := vm slot hlo hhi
    rw [hbaseWord, BitVec.ofNat_add_ofNat] at hh
    exact hh
  have safe := PA06A19PrepareClearVM045.actual_prefix_access q full used hq left
    right before hp ha data.scalars.bank032 hc he
  rw [leftLength] at pc
  refine ⟨⟨⟨header, data.scalars.of_frame address scalarFrame, ord, cache⟩,
    zeroView, bounded, vmActual⟩, newCards, pc, active, ?_⟩
  intro count hcount
  have hs := safe count hcount
  rw [layout] at hs
  exact hs

theorem clear_stage (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (before : WordState (bits q full))
    (hpc : before.pc.toNat = 5 * 1588) (ha : before.halted = false)
    (data : CachedData q full before)
    (cards : PA06A19PrepareBankData042.CopiedCardData q full (controlBase q full) before) :
    let after := packingRun (controllerInput q full used) program
      (PA06A19PrepareClearVM045.clock full.length q (treeSize q full)) before
    Data q full after ∧
      PA06A19PrepareBankData042.CopiedCardData q full (controlBase q full) after ∧ after.pc.toNat = 5 * 1639 ∧ after.halted = false ∧
      Safe q full used before (PA06A19PrepareClearVM045.clock full.length q (treeSize q full)) := by
  simpa only [Safe] using
    (clear_stage_local PA06A19PrepareAllQCode082.program clearLeft oldTail
      clearLeft_length clear_layout q full used hq hl before hpc ha data cards
      (PA06A19PrepareAllQCode082.selected_certificate full.length q))

end PaperProofs.Structure.LaminarTree.PA06A19PrepareAfterParents085
