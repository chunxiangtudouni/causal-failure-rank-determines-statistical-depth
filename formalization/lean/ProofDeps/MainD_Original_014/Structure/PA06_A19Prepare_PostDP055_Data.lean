module

public import Structure.PA06_A19Prepare_PostDP055_Frames

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED data-only endpoint from the genuine builder's outputs.
No metadata word or future successful execution is a field or assumption. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PreparePostDP055

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open CompactControllerClaims

def completedSource (q : Nat) (full : List (Finset (Fin q))) : State :=
  IndexedClosureRAM.execute (givenTreeROM q full).semantic
    (PA17TableBuild005.buildProgram full.length q (PSTRBuildLower.PreparedLayout.t q full))
    (initial (fun _ => 0))

/-- Real post-builder entry: original source output, actual permanent bank,
actual copied cache, fullCnew bound and the original scratch Header.
ScanInput and OutputData are exactly WordComplete019's entry predicates. -/
structure Data (q : Nat) (full : List (Finset (Fin q)))
    (state : WordState (indexWidth 32 full.length q)) : Prop where
  source : PSTRBuildLower.SourceRep.Prepared q full (completedSource q full) state
  runtime : PSTRBuildLower.RuntimeData.Data q full state.heap
  scalars : PA06A19PreparePreBuild044.ScalarData q full state
  scan : PA06A19PrepareStaticMetadata036.ScanInput q full
    (PA06A19PrepareChildrenCache023.actualControlBase q full)
    (PA06A19PrepareChildrenCache023.actualPackedWords q full)
    (PA06A19PrepareChildrenCache023.wordView state)
  children : PA06A19PrepareChildrenCache023.OutputData q full
    (PA06A19PrepareChildrenCache023.actualControlBase q full)
    (PA06A19PrepareChildrenCache023.wordView state)
  header : PA06A19PrepareRuntimePacked016.Header q state.heap
  bounded : PSTRBuildLower.GlobalCapacity.Bounded q full state.heap
  capacityBounded : CapacityPrefixBounded q (capacityWords 8192 full.length q (treeSize q full))
    (unpackHeap q (capacityWords 8192 full.length q (treeSize q full))
      (indexWidth 32 full.length q) (dataHeap state.heap))

theorem used_bound_of_bounded (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (state : WordState (indexWidth 32 full.length q))
    (bounded : PSTRBuildLower.GlobalCapacity.Bounded q full state.heap) :
    CapacityPrefixBounded q (capacityWords 8192 full.length q (treeSize q full))
      (unpackHeap q (capacityWords 8192 full.length q (treeSize q full))
        (indexWidth 32 full.length q) (dataHeap state.heap)) := by
  have ht : treeSize q full = PSTRBuildLower.PreparedLayout.t q full := by
    simp only [treeSize, Nat.ne_of_gt hq, ite_false]
  unfold PSTRBuildLower.GlobalCapacity.Bounded at bounded
  simp only [logicalHeap, Nat.ne_of_gt hq, ite_false] at bounded
  simpa only [PSTRBuildLower.PreparedLayout.capacity, ht] using bounded

theorem scanInput_of_scalars_raw (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (state : WordState (indexWidth 32 full.length q))
    (scalars : PA06A19PreparePreBuild044.ScalarData q full state)
    (raw : PA06A19PrepareStaticMetadata036.RawCardData q full
      (PA06A19PreparePreBuild044.controlBase q full)
      (PA06A19PrepareRuntimeHeader019.natView state)) :
    PA06A19PrepareStaticMetadata036.ScanInput q full
      (PA06A19PrepareChildrenCache023.actualControlBase q full)
      (PA06A19PrepareChildrenCache023.actualPackedWords q full)
      (PA06A19PrepareChildrenCache023.wordView state) := by
  rw [PA06A19PreparePreBuild044.children_controlBase q full hq, actualPacked_eq_pre q full hq]
  constructor
  · exact scalars.bank032.base
  · exact raw
  · change (state.heap (BitVec.ofNat (indexWidth 32 full.length q)
      (PA06A19PreparePreBuild044.controlBase q full))).toNat = full.length
    exact scalars.bank032.N
  · exact scalars.bank032.Q
  · exact scalars.bank032.T.trans (PA06A19PreparePreBuild044.prepared_size q full hq)
  · exact scalars.ordinaryBase

/-- Every input below is an actual output of113 on the same endpoint;
the original raw producer supplies only044.Data and RawCardData. -/
theorem data_of_builder_outputs (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (before after : WordState (indexWidth 32 full.length q))
    (pre : PA06A19PreparePreBuild044.Data q full before)
    (raw : PA06A19PrepareStaticMetadata036.RawCardData q full
      (PA06A19PreparePreBuild044.controlBase q full)
      (PA06A19PrepareRuntimeHeader019.natView before))
    (source : PSTRBuildLower.SourceRep.Prepared q full (completedSource q full) after)
    (runtime : PSTRBuildLower.RuntimeData.Data q full after.heap)
    (bounded : PSTRBuildLower.GlobalCapacity.Bounded q full after.heap)
    (frame : PSTRBuildLower.ResourceTrace.CacheFrame q full before.heap after.heap) :
    Data q full after := by
  have entry := PA06A19PrepareSTInput050.st_input_of_data q full hq before pre
  have address : after.register .address = before.register .address :=
    source.address.trans entry.2.1.address.symm
  have scalars := PA06A19PreparePreBuild044.ScalarData.of_frame pre.cached.scalars
    address (control_frame q full hq before after entry.1 runtime)
  have rawAfter := rawCardData_of_cache_frame q full hq before after raw frame
  have children := PA06A19PreparePreBuild044.outputData_of_high_frame q full hq hl
    before after pre.cached.cache address (high_frame q full hq before after frame)
  refine
    { source := source
      runtime := runtime
      scalars := scalars
      scan := scanInput_of_scalars_raw q full hq after scalars rawAfter
      children := ?_
      header := runtime.header
      bounded := bounded
      capacityBounded := used_bound_of_bounded q full hq after bounded }
  rw [PA06A19PreparePreBuild044.children_controlBase q full hq]
  exact children

end PaperProofs.Structure.LaminarTree.PA06A19PreparePostDP055
