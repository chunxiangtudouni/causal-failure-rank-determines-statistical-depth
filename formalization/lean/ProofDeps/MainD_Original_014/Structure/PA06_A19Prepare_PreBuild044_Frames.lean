module

public import Structure.PA06_A19Prepare_PreBuild044_Layout

set_option autoImplicit false
set_option warningAsError true

/-! Candidate frame transport, not a new raw-input qualification. Every
frame used by the assembly below is an output of023 or045 execution. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PreparePreBuild044

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM CompactControllerClaims

structure ScalarData (q : Nat) (full : List (Finset (Fin q)))
    (state : WordState (bits q full)) : Prop where
  bank032 : PA06A19PrepareFiniteInit032.BankData q full state
  bank037 : PA06A19PrepareInitialUsed037.BankData q full state
  oldCapacity : (state.heap (BitVec.ofNat _ (controlBase q full + 3))).toNat =
    PA06A19PreparePackedView013.oldCapacity full.length q (treeSize q full)
  ordinaryBase : (state.heap (BitVec.ofNat _ (controlBase q full + 6))).toNat =
    4 + packedWords q full

theorem ScalarData.of_frame {q : Nat} {full : List (Finset (Fin q))}
    {before after : WordState (bits q full)} (data : ScalarData q full before)
    (haddress : after.register .address = before.register .address)
    (frame : ∀ offset < 7, after.heap (BitVec.ofNat _ (controlBase q full + offset)) =
      before.heap (BitVec.ofNat _ (controlBase q full + offset))) : ScalarData q full after := by
  have h0 := frame 0 (by decide)
  simp only [Nat.add_zero] at h0
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · rw [haddress]; exact data.bank032.base
    · rw [h0]; exact data.bank032.N
    · rw [frame 1 (by decide)]; exact data.bank032.Q
    · rw [frame 2 (by decide)]; exact data.bank032.T
    · rw [frame 5 (by decide)]; exact data.bank032.P
  · constructor
    · rw [haddress]; exact data.bank037.base
    · simp only [Nat.add_zero]
      rw [h0]; exact data.bank032.N
    · rw [frame 1 (by decide)]; exact data.bank037.Q
    · rw [frame 2 (by decide)]; exact data.bank037.T
    · rw [frame 4 (by decide)]; exact data.bank037.C
  · rw [frame 3 (by decide)]; exact data.oldCapacity
  · rw [frame 6 (by decide)]; exact data.ordinaryBase

def ordinalAddress (q : Nat) (full : List (Finset (Fin q)))
    (node : (prepareNormalization q full).indexed.NodeId) : Nat :=
  controlBase q full + 512 + PA06A19PrepareCompactParents035Ord.ordSlot full.length q node.val

theorem ordinal_bounds (q : Nat) (full : List (Finset (Fin q)))
    (node : (prepareNormalization q full).indexed.NodeId) :
    controlBase q full + 512 ≤ ordinalAddress q full node ∧
      ordinalAddress q full node < PA06A19PrepareChildrenCache023.degreeBase
        (controlBase q full) (PA06A19PrepareChildrenCache023.mass q full) := by
  have hn := node.isLt.trans_le (prepared_indexed_size_le q full)
  dsimp only [ordinalAddress, PA06A19PrepareCompactParents035Ord.ordSlot,
    RawCandidateOrderingRAM.arraySlot, PA06A19PrepareChildrenCache023.degreeBase,
    PA06A19PrepareChildrenCache023.mass]
  omega

theorem copiedOrd_of_frame {q : Nat} {full : List (Finset (Fin q))}
    {before after : WordState (bits q full)}
    (data : PA06A19PrepareBankData042.CopiedOrdData q full (controlBase q full) before)
    (frame : ∀ node : (prepareNormalization q full).indexed.NodeId,
      after.heap (BitVec.ofNat _ (ordinalAddress q full node)) =
        before.heap (BitVec.ofNat _ (ordinalAddress q full node))) :
    PA06A19PrepareBankData042.CopiedOrdData q full (controlBase q full) after := by
  intro node
  change let candidate := (after.heap (BitVec.ofNat _ (ordinalAddress q full node))).toNat
    candidate ∈ RawCandidateOrder.retainedCandidateIndices q full ∧
      candidate < full.length + q + 1 ∧
      RawCandidateParents.candidateSupport q full candidate =
        (prepareNormalization q full).indexed.decode node
  rw [frame node]
  exact data node

theorem header_of_frame {q : Nat} {full : List (Finset (Fin q))}
    {before after : WordState (bits q full)}
    (data : PA06A19PrepareRuntimePacked016.Header q before.heap)
    (frame : ∀ n < 4, after.heap (BitVec.ofNat _ n) = before.heap (BitVec.ofNat _ n)) :
    PA06A19PrepareRuntimePacked016.Header q after.heap := by
  constructor
  · rw [frame 0 (by decide)]; exact data.width
  · rw [frame 1 (by decide)]; exact data.mask
  · rw [frame 2 (by decide)]; exact data.ones
  · rw [frame 3 (by decide)]; exact data.wordBits

theorem high_cell_fits (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (address : Nat) (ha : address ≤ PA06A19PrepareChildrenCache023.highCacheEnd
      (controlBase q full) (PA06A19PrepareChildrenCache023.mass q full)) : Fits (bits q full) address := by
  have h := (PA06A19PrepareChildrenCache023.highCacheEnd_actual_fits q full hq).2.2
  rw [children_controlBase q full hq] at h
  exact ha.trans_lt h

theorem control_cell_fits (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (offset : Nat) (ho : offset ≤ 38) : Fits (bits q full) (controlBase q full + offset) :=
  (by omega : controlBase q full + offset ≤ controlBase q full + 38).trans_lt
    (PA06A19PrepareClearVM045.actual_virtual_room q full hq).1

theorem ordinal_fits (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (node : (prepareNormalization q full).indexed.NodeId) :
    Fits (bits q full) (ordinalAddress q full node) := by
  apply high_cell_fits q full hq
  have hb := (ordinal_bounds q full node).2
  unfold PA06A19PrepareChildrenCache023.degreeBase at hb
  unfold PA06A19PrepareChildrenCache023.highCacheEnd
  omega

/-- The023 physical Protected frame preserves every permanent scalar and
every copied ordinal, not merely a proof-side Nat reconstruction. -/
theorem cache_retained_frames (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (before after : WordState (bits q full))
    (frame : ∀ point : BitVec (bits q full),
      PA06A19PrepareChildrenCache023.Protected q full (controlBase q full) point.toNat →
        after.heap point = before.heap point) :
    (∀ offset < 7, after.heap (BitVec.ofNat _ (controlBase q full + offset)) =
      before.heap (BitVec.ofNat _ (controlBase q full + offset))) ∧
    (∀ node : (prepareNormalization q full).indexed.NodeId,
      after.heap (BitVec.ofNat _ (ordinalAddress q full node)) =
        before.heap (BitVec.ofNat _ (ordinalAddress q full node))) ∧
    (∀ n < 4, after.heap (BitVec.ofNat _ n) = before.heap (BitVec.ofNat _ n)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro offset ho
    apply frame
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (control_cell_fits q full hq offset (by omega))]
    unfold PA06A19PrepareChildrenCache023.Protected PA06A19PrepareChildrenCache023.degreeBase
    constructor <;> omega
  · intro node
    apply frame
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (ordinal_fits q full hq node)]
    have hb := ordinal_bounds q full node
    exact ⟨Or.inr (by omega), Or.inl hb.2⟩
  · intro n hn
    apply frame
    have hf : Fits (bits q full) n :=
      (by omega : n ≤ controlBase q full + 38).trans_lt
        (PA06A19PrepareClearVM045.actual_virtual_room q full hq).1
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf]
    unfold PA06A19PrepareChildrenCache023.Protected PA06A19PrepareChildrenCache023.degreeBase
    constructor <;> omega

/-- All023 OutputData words are in the high cache. This transport uses045's
real permanent frame and keeps the original givenTreeROM specification. -/
theorem outputData_of_high_frame (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (before after : WordState (bits q full))
    (data : PA06A19PrepareChildrenCache023.OutputData q full (controlBase q full)
      (PA06A19PrepareChildrenCache023.wordView before))
    (haddress : after.register .address = before.register .address)
    (frame : ∀ address, controlBase q full + 512 ≤ address →
      address ≤ PA06A19PrepareChildrenCache023.highCacheEnd
        (controlBase q full) (PA06A19PrepareChildrenCache023.mass q full) →
      after.heap (BitVec.ofNat _ address) = before.heap (BitVec.ofNat _ address)) :
    PA06A19PrepareChildrenCache023.OutputData q full (controlBase q full)
      (PA06A19PrepareChildrenCache023.wordView after) := by
  have ht := PA06A19PrepareChildrenCache023.preparedSize_le_mass q full
  have hlen : (givenTreeROM q full).children.length =
      PA06A19PrepareChildrenCache023.preparedSize q full - 1 :=
    RawTreeSerialization.givenTreeROM_children_length q full hq hl
  have cell (address : Nat) (ha : controlBase q full + 512 ≤ address)
      (hb : address ≤ PA06A19PrepareChildrenCache023.highCacheEnd
        (controlBase q full) (PA06A19PrepareChildrenCache023.mass q full)) :
      (PA06A19PrepareChildrenCache023.wordView after).heap address =
        (PA06A19PrepareChildrenCache023.wordView before).heap address :=
    congrArg BitVec.toNat (frame address ha hb)
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · change (after.register .address).toNat = controlBase q full
      rw [haddress]; exact data.1.address
    · rw [cell _ (by omega) (by unfold PA06A19PrepareChildrenCache023.highCacheEnd; omega)]
      exact data.1.mass_cell
    · rw [cell _ (by omega) (by unfold PA06A19PrepareChildrenCache023.highCacheEnd; omega)]
      exact data.1.node_cell
    · intro child hc
      rw [cell _ (by
        unfold PA06A19PrepareChildrenCache023.parentAddress
        omega) (by
        unfold PA06A19PrepareChildrenCache023.parentAddress PA06A19PrepareChildrenCache023.highCacheEnd
        omega)]
      exact data.1.parents child hc
  · intro node
    have hn : node.val < PA06A19PrepareChildrenCache023.preparedSize q full := node.isLt
    rw [cell _ (by
      unfold PA06A19PrepareChildrenCache023.degreeBase
      omega) (by
      unfold PA06A19PrepareChildrenCache023.degreeBase PA06A19PrepareChildrenCache023.highCacheEnd
      omega)]
    exact data.2.1 node
  · intro position hp
    have hp0 := hp
    rw [hlen] at hp
    rw [cell _ (by
      unfold PA06A19PrepareChildrenCache023.childrenBase PA06A19PrepareChildrenCache023.degreeBase
      omega) (by
      unfold PA06A19PrepareChildrenCache023.childrenBase PA06A19PrepareChildrenCache023.degreeBase PA06A19PrepareChildrenCache023.highCacheEnd
      omega)]
    exact data.2.2 position hp0

end PaperProofs.Structure.LaminarTree.PA06A19PreparePreBuild044
