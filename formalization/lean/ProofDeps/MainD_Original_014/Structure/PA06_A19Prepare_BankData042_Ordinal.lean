module

public import Structure.PA06_A19Prepare_BankData042_CacheInput
public import Structure.PA06_A19Prepare_CompactParents035Ord

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareBankData042

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety CompactControllerClaims PA06A19PrepareRuntimeLayout026

/-- The ordinal in the actual high cache, together with its original
candidate interpretation. This reads the physical heap used by the builder. -/
def CopiedOrdData (q : Nat) (full : List (Finset (Fin q))) (CB : Nat)
    (state : WordState (indexWidth 32 full.length q)) : Prop :=
  ∀ node : (prepareNormalization q full).indexed.NodeId,
    let source := PA06A19PrepareCompactParents035Ord.ordSlot full.length q node.val
    let candidate := (state.heap (BitVec.ofNat _ (CB + 512 + source))).toNat
    candidate ∈ RawCandidateOrder.retainedCandidateIndices q full ∧ candidate < full.length + q + 1 ∧
      RawCandidateParents.candidateSupport q full candidate = (prepareNormalization q full).indexed.decode node

theorem embedded_copied_ord (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (state : WordState (indexWidth 32 full.length q))
    (ord : PA06A19PrepareCompactParents035Ord.OrdData q full state)
    (hpc : state.pc.toNat = 5 * left.length) (ha : state.halted = false)
    (hM : (state.heap (BitVec.ofNat _ 16)).toNat = full.length + q + 1)
    (ht : (state.heap (BitVec.ofNat _ (20 + 4 * (full.length + q + 1)))).toNat = treeSize q full)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ sequence left.length ++ right)))
    (hend : Fits (indexWidth 32 full.length q) (5 * (left ++ sequence left.length ++ right).length)) :
    let bits := indexWidth 32 full.length q
    let t := treeSize q full
    let P := packedCapacityWords q (capacityWords 8192 full.length q t) bits
    let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
    CopiedOrdData q full CB (packingRun (controllerInput q full used)
      (left ++ sequence left.length ++ right) (sequenceClock full.length q) state) := by
  dsimp only
  intro node
  let source := PA06A19PrepareCompactParents035Ord.ordSlot full.length q node.val
  have hnode : node.val < full.length + q + 1 :=
    node.isLt.trans_le (prepared_indexed_size_le q full)
  have hsource : source = 20 + 2 * (full.length + q + 1) + node.val := by
    dsimp only [source, PA06A19PrepareCompactParents035Ord.ordSlot, RawCandidateOrderingRAM.arraySlot]
    omega
  have h16 : 16 ≤ source := by rw [hsource]; omega
  have hL : source < PA06A19PrepareControlBank017.cacheLength full.length q := by
    rw [hsource]
    unfold PA06A19PrepareControlBank017.cacheLength PA06A19PrepareControlBank017.mass
    omega
  have copied := embedded_sequence_copied_word q full used hq left right state hpc ha hM ht hh hcode hend
    source h16 hL
  dsimp only
  change let candidate := ((packingRun (controllerInput q full used) (left ++ sequence left.length ++ right)
    (sequenceClock full.length q) state).heap (BitVec.ofNat _
      (PA06A19PrepareControlBank017.cacheBase full.length q (treeSize q full)
        (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full))
          (indexWidth 32 full.length q)) + source))).toNat
    candidate ∈ RawCandidateOrder.retainedCandidateIndices q full ∧ candidate < full.length + q + 1 ∧
      RawCandidateParents.candidateSupport q full candidate = (prepareNormalization q full).indexed.decode node
  rw [copied]
  exact ord node

end PaperProofs.Structure.LaminarTree.PA06A19PrepareBankData042
