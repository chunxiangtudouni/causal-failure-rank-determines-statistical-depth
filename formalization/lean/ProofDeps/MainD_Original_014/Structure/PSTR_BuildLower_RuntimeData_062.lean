module

public import Structure.PSTR_BuildLower_InternalPort_058
public import Structure.PSTR_BuildLower_PreparedPortRoom_060

/-! Data-only runtime builder inputs: real permanent bank/header/cache words.
Their preservation follows from agreement at their actual physical addresses.
No source-step, whole-builder, success, safety or cost contract is a field. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.RuntimeData
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open PreparedLayout

structure Data (q : Nat) (full : List (Finset (Fin q)))
    (heap : BitVec (bits q full) → BitVec (bits q full)) : Prop
    extends InternalInput.Data q full (controlBase q full) heap where
  stages : heap (BitVec.ofNat _ (controlBase q full)) = BitVec.ofNat _ full.length
  tools : heap (BitVec.ofNat _ (controlBase q full + 1)) = BitVec.ofNat _ q
  cutoff : heap (BitVec.ofNat _ (controlBase q full + 3)) = BitVec.ofNat _ (oldCapacity q full)
  capacity : heap (BitVec.ofNat _ (controlBase q full + 4)) = BitVec.ofNat _ (PreparedLayout.capacity q full)
  packed : heap (BitVec.ofNat _ (controlBase q full + 5)) = BitVec.ofNat _ (PreparedLayout.packed q full)
  index : heap (BitVec.ofNat _ (controlBase q full + 6)) = BitVec.ofNat _ (indexBase q full)
  cached : ∀ node : (prepareNormalization q full).indexed.NodeId,
    PA06A19PrepareBankNodeBit022.CachedWordNode full (controlBase q full) node heap
  header : PA06A19PrepareRuntimePacked016.Header q heap

theorem cache_address_room (q : Nat) (full : List (Finset (Fin q))) (factor a : Nat)
    (hf : factor ≤ 5) (ha : a < t q full + 1) :
    controlBase q full + 533 + factor * (full.length + q + 1) + a < allocated q full := by
  have hm := Nat.mul_le_mul_right (full.length + q + 1) hf
  unfold controlBase allocated
  omega

theorem cache_address_fits (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (factor a : Nat)
    (hf : factor ≤ 5) (ha : a < t q full + 1) :
    Fits (bits q full) (controlBase q full + 533 + factor * (full.length + q + 1) + a) :=
  (cache_address_room q full factor a hf ha).trans (allocation_fits q full hq)

theorem Data.of_frame (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (before after : BitVec (bits q full) → BitVec (bits q full)) (data : Data q full before)
    (header : ∀ point < 4, after (BitVec.ofNat _ point) = before (BitVec.ofNat _ point))
    (control : ∀ offset < 32, after (BitVec.ofNat _ (controlBase q full + offset)) =
      before (BitVec.ofNat _ (controlBase q full + offset)))
    (cache : ∀ point, controlBase q full + 512 ≤ point → Fits (bits q full) point →
      after (BitVec.ofNat _ point) = before (BitVec.ofNat _ point)) : Data q full after := by
  have hmass : Fits (bits q full) (controlBase q full + 528) := by
    have hh := cache_address_fits q full hq 0 0 (by decide) (by omega)
    simp only [Nat.zero_mul, Nat.add_zero] at hh
    exact lt_of_le_of_lt (by omega) hh
  refine
    { toData := { mass := ?_, size := ?_, parent := ?_, degree := ?_ }
      stages := ?_
      tools := ?_
      cutoff := ?_
      capacity := ?_
      packed := ?_
      index := ?_
      cached := ?_
      header := ?_ }
  · rw [cache _ (by omega) hmass]
    exact data.mass
  · rw [control 2 (by decide)]
    exact data.size
  · intro node
    rw [cache _ (by omega) (cache_address_fits q full hq 4 node.val (by decide)
      (by have hn : node.val < t q full := node.isLt; omega))]
    exact data.parent node
  · intro node
    rw [cache _ (by omega) (cache_address_fits q full hq 5 node.val (by decide)
      (by have hn : node.val < t q full := node.isLt; omega))]
    exact data.degree node
  · have hh := control 0 (by decide)
    simpa only [Nat.add_zero] using hh.trans data.stages
  · rw [control 1 (by decide)]
    exact data.tools
  · rw [control 3 (by decide)]
    exact data.cutoff
  · rw [control 4 (by decide)]
    exact data.capacity
  · rw [control 5 (by decide)]
    exact data.packed
  · rw [control 6 (by decide)]
    exact data.index
  · intro node
    obtain ⟨candidate, hword, hsupport⟩ := data.cached node
    refine ⟨candidate, ?_, hsupport⟩
    rw [cache _ ?_ ((ord_room q full node).trans (allocation_fits q full hq))]
    · exact hword
    · unfold PA06A19PrepareBankNodeBit022.ordAddress
      omega
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [header 0 (by decide)]
      exact data.header.width
    · rw [header 1 (by decide)]
      exact data.header.mask
    · rw [header 2 (by decide)]
      exact data.header.ones
    · rw [header 3 (by decide)]
      exact data.header.wordBits

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.RuntimeData
