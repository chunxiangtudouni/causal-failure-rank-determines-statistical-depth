module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Control_015f

/-! Semantic invariance needed by the outer budget loop: all budgets are
judged against the SAME original logicalHeap, even when physical H < C. -/

@[expose] public section
set_option maxRecDepth 26000
set_option maxHeartbeats 2600000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem rawGood_of_leading_frame {bits q : Nat} (full : List (Finset (Fin q))) (capWords entryBase : Nat)
    (old fresh : BitVec bits → BitVec bits) (hb : 0 < bits) (hq : 0 < q)
    (hs : Fits bits (4 + capWords * CapacityBits.width q))
    (hroom : Fits bits (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 16))
    (hframe : ∀ physical < PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 8, fresh (BitVec.ofNat bits physical) = old (BitVec.ofNat bits physical))
    (hrow : entryBase + (treeSize q full + 1) ≤ capWords) :
    rawGood (logicalHeap q capWords fresh) entryBase
      (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords)) (treeSize q full) =
    rawGood (logicalHeap q capWords old) entryBase
      (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords)) (treeSize q full) := by
  have hf := logical_leading_frame full capWords (treeSize q full) old fresh hb hq hs hroom hframe
  have htag : logicalHeap q capWords fresh entryBase = logicalHeap q capWords old entryBase := by
    apply hf
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
      PSTRQueryLayout.logicalWorkspace
    omega
  unfold rawGood
  rw [htag]
  congr 1
  apply acceptPrefix_congr
  intro node hn
  constructor
  · apply hf
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    omega
  · apply hf
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
      PSTRQueryLayout.logicalWorkspace
    omega

theorem rawBad_of_leading_frame {bits q : Nat} (full : List (Finset (Fin q))) (capWords entryBase encoded : Nat)
    (old fresh : BitVec bits → BitVec bits) (hb : 0 < bits) (hq : 0 < q)
    (hs : Fits bits (4 + capWords * CapacityBits.width q))
    (hroom : Fits bits (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 16))
    (hframe : ∀ physical < PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 8, fresh (BitVec.ofNat bits physical) = old (BitVec.ofNat bits physical))
    (hrow : entryBase + (treeSize q full + 1) ≤ capWords) (hn : encoded ≤ treeSize q full)
    (hparents : ∀ e ≤ treeSize q full, logicalHeap q capWords old
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + e) ≤ treeSize q full) :
    rawBad (logicalHeap q capWords fresh) entryBase
      (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords))
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full)) (treeSize q full) encoded =
    rawBad (logicalHeap q capWords old) entryBase
      (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords))
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full)) (treeSize q full) encoded := by
  have hf := logical_leading_frame full capWords (treeSize q full) old fresh hb hq hs hroom hframe
  unfold rawBad
  rw [rawGood_of_leading_frame full capWords entryBase old fresh hb hq hs hroom hframe hrow]
  congr 1
  apply chainPrefix_congr _ _ _ _ _ (treeSize q full) _ _ hparents hn
  · intro node hnode
    apply hf
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    omega
  · intro node hnode
    apply hf
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
      PSTRQueryLayout.logicalWorkspace
    omega
  · intro e he
    apply hf
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    omega

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
