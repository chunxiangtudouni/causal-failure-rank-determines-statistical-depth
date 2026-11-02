module

public import Structure.PA06_A19Prepare_STInput050
public import Structure.PA06_A19Prepare_StaticMetadata036_ScanState
public import Structure.PSTR_BuildLower_BuilderEndResources_113

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED post-DP data transport. States stay abstract throughout.
The cache frame is the actual builder's endpoint result, not an assumption
of safety or of metadata production on the original raw caller. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PreparePostDP055

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open CompactControllerClaims

theorem st_controlBase_eq_actual (q : Nat) (full : List (Finset (Fin q))) :
    PSTRBuildLower.PreparedLayout.controlBase q full =
      PA06A19PrepareChildrenCache023.actualControlBase q full := rfl

theorem st_controlBase_eq_pre (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    PSTRBuildLower.PreparedLayout.controlBase q full =
      PA06A19PreparePreBuild044.controlBase q full :=
  (st_controlBase_eq_actual q full).trans
    (PA06A19PreparePreBuild044.children_controlBase q full hq)

theorem actualPacked_eq_pre (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    PA06A19PrepareChildrenCache023.actualPackedWords q full =
      PA06A19PreparePreBuild044.packedWords q full := by
  change packedCapacityWords q (capacityWords 8192 full.length q
      (PA06A19PrepareChildrenCache023.preparedSize q full)) (indexWidth 32 full.length q) =
    packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full))
      (indexWidth 32 full.length q)
  rw [PA06A19PreparePreBuild044.prepared_size q full hq]

/-- RuntimeData supplies all seven permanent scalar cells after DP, while
the same predicate obtained from044 supplies their prior physical values.
Equality is at Word values, so this step does not assume a no-wrap answer. -/
theorem control_frame (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (before after : WordState (indexWidth 32 full.length q))
    (beforeData : PSTRBuildLower.RuntimeData.Data q full before.heap)
    (afterData : PSTRBuildLower.RuntimeData.Data q full after.heap) :
    ∀ offset < 7,
      after.heap (BitVec.ofNat _ (PA06A19PreparePreBuild044.controlBase q full + offset)) =
        before.heap (BitVec.ofNat _ (PA06A19PreparePreBuild044.controlBase q full + offset)) := by
  intro offset ho
  rw [← st_controlBase_eq_pre q full hq]
  interval_cases offset
  · simpa only [Nat.add_zero] using afterData.stages.trans beforeData.stages.symm
  · exact afterData.tools.trans beforeData.tools.symm
  · exact afterData.size.trans beforeData.size.symm
  · exact afterData.cutoff.trans beforeData.cutoff.symm
  · exact afterData.capacity.trans beforeData.capacity.symm
  · exact afterData.packed.trans beforeData.packed.symm
  · exact afterData.index.trans beforeData.index.symm

/-- Every transported high word is fitted by the ORIGINAL actual cache
geometry. CacheFrame has no unbounded-Nat-heap interpretation. -/
theorem high_frame (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (before after : WordState (indexWidth 32 full.length q))
    (frame : PSTRBuildLower.ResourceTrace.CacheFrame q full before.heap after.heap) :
    ∀ address, PA06A19PreparePreBuild044.controlBase q full + 512 ≤ address →
      address ≤ PA06A19PrepareChildrenCache023.highCacheEnd
        (PA06A19PreparePreBuild044.controlBase q full)
        (PA06A19PrepareChildrenCache023.mass q full) →
      after.heap (BitVec.ofNat _ address) = before.heap (BitVec.ofNat _ address) := by
  intro address hlo hhi
  apply frame address
  · rw [st_controlBase_eq_pre q full hq]
    exact hlo
  · exact PA06A19PreparePreBuild044.high_cell_fits q full hq address hhi

theorem rawCardData_of_cache_frame (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (before after : WordState (indexWidth 32 full.length q))
    (raw : PA06A19PrepareStaticMetadata036.RawCardData q full
      (PA06A19PreparePreBuild044.controlBase q full)
      (PA06A19PrepareRuntimeHeader019.natView before))
    (frame : PSTRBuildLower.ResourceTrace.CacheFrame q full before.heap after.heap) :
    PA06A19PrepareStaticMetadata036.RawCardData q full
      (PA06A19PreparePreBuild044.controlBase q full)
      (PA06A19PrepareRuntimeHeader019.natView after) := by
  have physical := high_frame q full hq before after frame
  have cell (address : Nat)
      (hlo : PA06A19PreparePreBuild044.controlBase q full + 512 ≤ address)
      (hhi : address ≤ PA06A19PrepareChildrenCache023.highCacheEnd
        (PA06A19PreparePreBuild044.controlBase q full)
        (PA06A19PrepareChildrenCache023.mass q full)) :
      (PA06A19PrepareRuntimeHeader019.natView after).heap address =
        (PA06A19PrepareRuntimeHeader019.natView before).heap address :=
    congrArg BitVec.toNat (physical address hlo hhi)
  constructor
  · rw [cell _ (by omega) (by
      unfold PA06A19PrepareChildrenCache023.highCacheEnd
      omega)]
    exact raw.mass_cell
  · intro candidate
    have hc : candidate.val < PA06A19PrepareChildrenCache023.mass q full := candidate.isLt
    rw [cell _ (by
      unfold PA06A19PrepareStaticMetadata036.rawCardAddress
      omega) (by
      unfold PA06A19PrepareStaticMetadata036.rawCardAddress
        PA06A19PrepareChildrenCache023.highCacheEnd
      omega)]
    exact raw.cards candidate
  · intro node
    have hn : node.val < PA06A19PrepareChildrenCache023.preparedSize q full := node.isLt
    have ht := PA06A19PrepareChildrenCache023.preparedSize_le_mass q full
    obtain ⟨candidate, hord, support⟩ := raw.ordered node
    refine ⟨candidate, ?_, support⟩
    rw [cell _ (by
      unfold PA06A19PrepareStaticMetadata036.rawOrdAddress
      omega) (by
      unfold PA06A19PrepareStaticMetadata036.rawOrdAddress
        PA06A19PrepareChildrenCache023.highCacheEnd
      omega)]
    exact hord

end PaperProofs.Structure.LaminarTree.PA06A19PreparePostDP055
