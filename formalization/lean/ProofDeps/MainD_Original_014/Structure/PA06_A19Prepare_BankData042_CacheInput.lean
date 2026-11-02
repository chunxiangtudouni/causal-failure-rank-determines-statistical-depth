module

public import Structure.PA06_A19Prepare_BankData042
public import Structure.PA06_A19Prepare_CompactParents035Entry
public import Structure.PA06_A19Prepare_ChildrenCache023_Data
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Candidate bridge from actual raw WordParents and the actual relocated
heap to the children producer's InputData. The frame premise below is an
internal preceding header-segment output (all physical cache words>=16);
it must be eliminated by that real execution, never added to the original
raw caller. No copied heap, parent table, hSafe or copy result is assumed. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareBankData042

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety RawTreePreprocessingClaims CompactControllerClaims
  PA06A19PrepareRuntimeLayout026

/-- Every copied source word>=16 survives low scratch9..15 and bank0..6.
This is equality for the actual Word result in the same containing code. -/
theorem embedded_sequence_copied_word (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc.toNat = 5 * left.length) (ha : state.halted = false)
    (hM : (state.heap (BitVec.ofNat _ 16)).toNat = full.length + q + 1)
    (ht : (state.heap (BitVec.ofNat _ (20 + 4 * (full.length + q + 1)))).toNat = treeSize q full)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ sequence left.length ++ right)))
    (hend : Fits (indexWidth 32 full.length q) (5 * (left ++ sequence left.length ++ right).length))
    (source : Nat) (hsource : 16 ≤ source)
    (hsourceEnd : source < PA06A19PrepareControlBank017.cacheLength full.length q) :
    let bits := indexWidth 32 full.length q
    let t := treeSize q full
    let P := packedCapacityWords q (capacityWords 8192 full.length q t) bits
    let target := PA06A19PrepareControlBank017.cacheBase full.length q t P
    (packingRun (controllerInput q full used) (left ++ sequence left.length ++ right)
      (sequenceClock full.length q) state).heap (BitVec.ofNat bits (target + source)) =
        state.heap (BitVec.ofNat bits source) := by
  let bits := indexWidth 32 full.length q
  let t := treeSize q full
  let P := packedCapacityWords q (capacityWords 8192 full.length q t) bits
  let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
  let target := PA06A19PrepareControlBank017.cacheBase full.length q t P
  let L := PA06A19PrepareControlBank017.cacheLength full.length q
  let original := (PA06A19PrepareRuntimeHeader019.natView state).heap
  let laid := lowFields full.length q t (CapacityBits.width q) bits original
  let moved := PA06A19PrepareControlBank017.relocatedHeap laid 0 target L
  have actual := PA06A19PrepareRuntimeSequence041.embedded_sequence_data q full used hq left right state
    hpc ha hM ht hh hcode hend
  dsimp only at actual
  have endFit : Fits bits (target + L) := (actual_transfer_end_room q full hq).2
  have pointFit : Fits bits (target + source) := (Nat.add_le_add_left hsourceEnd.le target).trans_lt endFit
  have pointNat : (BitVec.ofNat bits (target + source)).toNat = target + source := Nat.mod_eq_of_lt pointFit
  have hne (offset : Nat) (ho : offset ≤ 6) : target + source ≠ CB + offset := by
    dsimp only [target, PA06A19PrepareControlBank017.cacheBase]
    dsimp only [CB]
    omega
  have fields : bankFields full.length q t P CB moved (target + source) = moved (target + source) := by
    unfold bankFields
    rw [Function.update_of_ne (hne 6 (by decide)), Function.update_of_ne (hne 5 (by decide)),
      Function.update_of_ne (hne 4 (by decide)), Function.update_of_ne (hne 3 (by decide)),
      Function.update_of_ne (hne 2 (by decide)), Function.update_of_ne (hne 1 (by decide)),
      Function.update_of_ne (hne 0 (by decide))]
  have copied : moved (target + source) = laid source := by
    exact (PA06A19PrepareControlBank017.relocatedHeap_target laid 0 target L source hsourceEnd).trans (by rw [Nat.zero_add])
  have low : laid source = original source := by
    dsimp only [laid]
    unfold lowFields
    rw [Function.update_of_ne (show source ≠ 15 by omega), Function.update_of_ne (show source ≠ 14 by omega),
      Function.update_of_ne (show source ≠ 13 by omega), Function.update_of_ne (show source ≠ 12 by omega),
      Function.update_of_ne (show source ≠ 11 by omega), Function.update_of_ne (show source ≠ 10 by omega),
      Function.update_of_ne (show source ≠ 9 by omega)]
  dsimp only
  calc
    _ = BitVec.ofNat bits (bankFields full.length q t P CB moved ((BitVec.ofNat bits (target + source)).toNat)) := actual.2.2.2 _
    _ = BitVec.ofNat bits (original source) := by rw [pointNat, fields, copied, low]
    _ = state.heap (BitVec.ofNat bits source) := by
      dsimp only [original, PA06A19PrepareRuntimeHeader019.natView, bits]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The source parents are certified by the real raw Word run. Only the
intervening physical>=16 frame is consumed; the actual041 relocation and
bank stores establish the entire children InputData in the reached state. -/
private theorem childrenInput_of_copied_words (q : Nat) (full : List (Finset (Fin q)))
    (raw fresh : WordState (indexWidth 32 full.length q))
    (parents : PA06A19PrepareCompactParents035Entry.WordParents q full raw) (CB : Nat)
    (address : (fresh.register .address).toNat = CB)
    (copied : ∀ source : Nat, 16 ≤ source →
      source < PA06A19PrepareControlBank017.cacheLength full.length q →
      fresh.heap (BitVec.ofNat _ (CB + 512 + source)) = raw.heap (BitVec.ofNat _ source)) :
    PA06A19PrepareChildrenCache023.InputData q full CB
      (PA06A19PrepareRuntimeHeader019.natView fresh) := by
  let M := full.length + q + 1
  let L := PA06A19PrepareControlBank017.cacheLength full.length q
  have hsize : (prepareNormalization q full).indexed.nodes.size ≤ M := prepared_indexed_size_le q full
  have nodeAddress : RawCandidateParentRAM.nodeCountAddress 16 M = 20 + 4 * M := by
    unfold RawCandidateParentRAM.nodeCountAddress RawCandidateOrderingRAM.arraySlot
    omega
  have nodeLow : 16 ≤ RawCandidateParentRAM.nodeCountAddress 16 M := by rw [nodeAddress]; omega
  have nodeEnd : RawCandidateParentRAM.nodeCountAddress 16 M < L := by
    rw [nodeAddress]
    dsimp only [L, PA06A19PrepareControlBank017.cacheLength, PA06A19PrepareControlBank017.mass, M]
    omega
  constructor
  · exact address
  · have h := congrArg BitVec.toNat (copied 16 (by decide) (by
      dsimp only [PA06A19PrepareControlBank017.cacheLength]
      omega))
    rw [show CB + 512 + 16 = CB + 528 by omega, parents.2.2.2.1] at h
    exact h
  · have h := congrArg BitVec.toNat
      (copied (RawCandidateParentRAM.nodeCountAddress 16 M) nodeLow nodeEnd)
    have hp :
        (raw.heap (BitVec.ofNat (indexWidth 32 full.length q)
          (RawCandidateParentRAM.nodeCountAddress 16 M))).toNat =
          (prepareNormalization q full).indexed.nodes.size := parents.2.2.2.2.1
    rw [nodeAddress] at hp
    rw [nodeAddress, show CB + 512 + (20 + 4 * M) = CB + 532 + 4 * M by omega] at h
    exact h.trans hp
  · intro child hc
    have hcM : child < M := hc.trans_le hsize
    let source := RawCandidateParentRAM.parentSlot 16 M child
    have hsource16 : 16 ≤ source := by
      dsimp only [source]
      rw [RawCandidateParentRAM.parentSlot_eq]
      omega
    have hsourceEnd : source < L := by
      dsimp only [source]
      rw [RawCandidateParentRAM.parentSlot_eq]
      dsimp only [L, PA06A19PrepareControlBank017.cacheLength, PA06A19PrepareControlBank017.mass, M]
      omega
    have h := congrArg BitVec.toNat (copied source hsource16 hsourceEnd)
    have location : CB + 512 + source = PA06A19PrepareChildrenCache023.parentAddress CB M child := by
      dsimp only [source, PA06A19PrepareChildrenCache023.parentAddress]
      rw [RawCandidateParentRAM.parentSlot_eq]
      omega
    rw [location] at h
    exact (h.trans (parents.2.2.2.2.2 ⟨child, hc⟩)).trans
      (UniformNormalizationRAM.givenTreeROM_parent q full ⟨child, hc⟩).symm

/-- The actual containing sequence supplies both the bank address and all
physical copied words; record construction sees only an abstract state. -/
theorem embedded_children_input (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp)
    (raw state : WordState (indexWidth 32 full.length q))
    (parents : PA06A19PrepareCompactParents035Entry.WordParents q full raw)
    (frame : ∀ point : BitVec (indexWidth 32 full.length q), 16 ≤ point.toNat → state.heap point = raw.heap point)
    (hpc : state.pc.toNat = 5 * left.length) (ha : state.halted = false)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ sequence left.length ++ right)))
    (hend : Fits (indexWidth 32 full.length q) (5 * (left ++ sequence left.length ++ right).length)) :
    let bits := indexWidth 32 full.length q
    let t := treeSize q full
    let P := packedCapacityWords q (capacityWords 8192 full.length q t) bits
    let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
    PA06A19PrepareChildrenCache023.InputData q full CB
      (PA06A19PrepareRuntimeHeader019.natView (packingRun (controllerInput q full used)
        (left ++ sequence left.length ++ right) (sequenceClock full.length q) state)) := by
  let bits := indexWidth 32 full.length q
  let M := full.length + q + 1
  let t := treeSize q full
  let P := packedCapacityWords q (capacityWords 8192 full.length q t) bits
  let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
  let target := PA06A19PrepareControlBank017.cacheBase full.length q t P
  let L := PA06A19PrepareControlBank017.cacheLength full.length q
  have endFit : Fits bits (target + L) := (actual_transfer_end_room q full hq).2
  have sourceFit (source : Nat) (hs : source < L) : Fits bits source :=
    (by omega : source ≤ target + L).trans_lt endFit
  have sourceFrame (source : Nat) (h16 : 16 ≤ source) (hs : source < L) :
      state.heap (BitVec.ofNat bits source) = raw.heap (BitVec.ofNat bits source) := by
    apply frame
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (sourceFit source hs)]
    exact h16
  have nodeAddress : RawCandidateParentRAM.nodeCountAddress 16 M = 20 + 4 * M := by
    unfold RawCandidateParentRAM.nodeCountAddress RawCandidateOrderingRAM.arraySlot
    omega
  have nodeLow : 16 ≤ RawCandidateParentRAM.nodeCountAddress 16 M := by rw [nodeAddress]; omega
  have nodeEnd : RawCandidateParentRAM.nodeCountAddress 16 M < L := by
    rw [nodeAddress]
    dsimp only [L, PA06A19PrepareControlBank017.cacheLength, PA06A19PrepareControlBank017.mass, M]
    omega
  have htPrepared : t = (prepareNormalization q full).indexed.nodes.size := by
    dsimp only [t, treeSize]
    rw [ite_eq_right (Nat.ne_of_gt hq)]
  have hM : (state.heap (BitVec.ofNat bits 16)).toNat = M := by
    rw [sourceFrame 16 (by decide) (by
      dsimp only [L, PA06A19PrepareControlBank017.cacheLength]
      omega)]
    exact parents.2.2.2.1
  have ht : (state.heap (BitVec.ofNat bits (20 + 4 * M))).toNat = t := by
    rw [← nodeAddress, sourceFrame _ nodeLow nodeEnd]
    exact parents.2.2.2.2.1.trans htPrepared.symm
  have actual := PA06A19PrepareRuntimeSequence041.embedded_sequence_data q full used hq left right state
    hpc ha hM ht hh hcode hend
  dsimp only at actual
  exact childrenInput_of_copied_words q full raw
    (packingRun (controllerInput q full used) (left ++ sequence left.length ++ right)
      (sequenceClock full.length q) state) parents CB actual.2.2.1
    (fun source h16 hs =>
      (embedded_sequence_copied_word q full used hq left right state hpc ha hM ht hh hcode hend
        source h16 hs).trans (sourceFrame source h16 hs))

end PaperProofs.Structure.LaminarTree.PA06A19PrepareBankData042
