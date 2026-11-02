module

public import PaperProofs.Structure.PA17_QueryTests_009
public import PaperProofs.Structure.PSTR_QueryLayout_041
public import PaperProofs.Structure.PSTR_HD_WordSegments_014
public import PaperProofs.Structure.PackedCapacityRAM

/-! Fixed-runtime tests: scalar semantic invariants and actual header-relative
Word primitives. These are components, not a complete fixed-tests run. VOID
payloads are unrestricted here, exactly as in the original tag-first model. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM PA17TagBridge001

def acceptPrefix (heap : Nat → Nat) (entryBase countsBase remaining : Nat) : Bool :=
  (List.range remaining).all (fun node => decide (heap (countsBase + node) ≤ heap (entryBase + 1 + node)))

theorem acceptPrefix_zero (heap : Nat → Nat) (entryBase countsBase : Nat) :
    acceptPrefix heap entryBase countsBase 0 = true := rfl

theorem acceptPrefix_succ (heap : Nat → Nat) (entryBase countsBase remaining : Nat) :
    acceptPrefix heap entryBase countsBase (remaining + 1) =
      (decide (heap (countsBase + remaining) ≤ heap (entryBase + 1 + remaining)) &&
        acceptPrefix heap entryBase countsBase remaining) := by
  simp only [acceptPrefix, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
  exact Bool.and_comm _ _

theorem acceptPrefix_correct {q : Nat} (cache : IndexedNodeCache (Fin q))
    (heap : Nat → Nat) (entryBase countsBase : Nat) (counts : IndexedCapacity cache)
    (entry : IndexedEntry.FixedEntry cache)
    (hcounts : ∀ node : cache.NodeId, heap (countsBase + node.val) = counts.get node)
    (hentry : TagFirstRep cache heap entryBase entry) :
    ((decide (heap entryBase ≠ 0)) && acceptPrefix heap entryBase countsBase cache.nodes.size) =
      IndexedQuery.accepts cache counts entry := by
  cases entry with
  | void =>
    change heap entryBase = 0 at hentry
    rw [hentry]
    rfl
  | vector capacity =>
    have he : acceptPrefix heap entryBase countsBase cache.nodes.size =
        IndexedQuery.accepts cache counts (.vector capacity) := by
      apply Bool.eq_iff_iff.mpr
      simp only [acceptPrefix, List.all_eq_true, List.mem_range, decide_eq_true_eq,
        IndexedQuery.accepts, List.mem_finRange, forall_const]
      constructor
      · intro h node
        have hh := h node.val node.isLt
        rw [hcounts node, hentry.2 node] at hh
        exact hh
      · intro h index hi
        rw [hcounts ⟨index, hi⟩, hentry.2 ⟨index, hi⟩]
        exact h ⟨index, hi⟩
    rw [hentry.1]
    exact he

def chainPrefix (heap : Nat → Nat) (entryBase countsBase parentBase : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, encoded =>
      (if encoded = 0 then true else
        decide (heap (countsBase + (encoded - 1)) < heap (entryBase + 1 + (encoded - 1)))) &&
      chainPrefix heap entryBase countsBase parentBase fuel (heap (parentBase + encoded))

theorem chainPrefix_none (heap : Nat → Nat) (entryBase countsBase parentBase fuel : Nat)
    (hsentinel : heap parentBase = 0) :
    chainPrefix heap entryBase countsBase parentBase fuel 0 = true := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [chainPrefix, ite_true, Nat.add_zero, hsentinel, Bool.true_and] using ih

theorem chainPrefix_correct {q : Nat} (cache : IndexedNodeCache (Fin q))
    (heap : Nat → Nat) (entryBase countsBase parentBase fuel : Nat)
    (counts capacity : IndexedCapacity cache) (current : Option cache.NodeId)
    (hcounts : ∀ node : cache.NodeId, heap (countsBase + node.val) = counts.get node)
    (hcapacity : ∀ node : cache.NodeId, heap (entryBase + 1 + node.val) = capacity.get node)
    (hparents : PA17HeapAncestors001.ParentHeapFor cache parentBase heap) :
    chainPrefix heap entryBase countsBase parentBase fuel (IndexedClosureRAM.encodedNode cache current) =
      PA17QueryTests009.chainTest cache counts capacity fuel current := by
  induction fuel generalizing current with
  | zero => cases current <;> rfl
  | succ fuel ih =>
    cases current with
    | none =>
      exact chainPrefix_none heap entryBase countsBase parentBase (fuel + 1) hparents.1
    | some node =>
      simp only [chainPrefix, IndexedClosureRAM.encodedNode, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, ite_false, Nat.add_sub_cancel, hcounts node, hcapacity node]
      have hp := hparents.2 node
      change heap (parentBase + (node.val + 1)) =
        IndexedClosureRAM.encodedNode cache (cache.parents.get node) at hp
      rw [hp, ih]
      cases hh : cache.parents.get node <;>
        simp only [PA17QueryTests009.chainTest, IndexedAncestors.parentChain, hh,
          List.all_cons, List.all_nil, Bool.and_true]

def loadSlot (offset : Nat) (target : Register) : List PackingOp :=
  [.base (.base (.constant .index offset)), .base (.base (.add .index .address .index)),
    .base (.base (.loadHeap target .index))]

def storeSlot (offset : Nat) (source : Register) : List PackingOp :=
  [.base (.base (.constant .index offset)), .base (.base (.add .index .address .index)),
    .base (.base (.storeHeap .index source))]

theorem loadSlot_length (offset : Nat) (target : Register) : (loadSlot offset target).length = 3 := rfl
theorem storeSlot_length (offset : Nat) (source : Register) : (storeSlot offset source).length = 3 := rfl

theorem loadSlot_straight (offset : Nat) (target : Register) : StraightProgram (loadSlot offset target) := by
  simp [loadSlot, StraightProgram, StraightOp]

theorem storeSlot_straight (offset : Nat) (source : Register) : StraightProgram (storeSlot offset source) := by
  simp [storeSlot, StraightProgram, StraightOp]

theorem loadSlot_noStore (offset : Nat) (target : Register) :
    ∀ op ∈ loadSlot offset target, HeapPreservingOp op := by
  simp [loadSlot, HeapPreservingOp]

theorem execute_loadSlot {bits : Nat} (rom : PhysicalROM) (offset header : Nat)
    (target : Register) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header) (hne : target ≠ .address) :
    let after := executeOps rom (loadSlot offset target) state
    after.register target = state.heap (BitVec.ofNat bits (header + offset)) ∧
      after.register .address = BitVec.ofNat bits header ∧ after.heap = state.heap := by
  cases target <;>
    simp_all +decide [loadSlot, executeOps, packingExecuteOp, wordOp, wordInstruction,
      BitVec.ofNat_add_ofNat]

theorem execute_storeSlot {bits : Nat} (rom : PhysicalROM) (offset header : Nat)
    (source : Register) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header) (hne : source ≠ .index) :
    let after := executeOps rom (storeSlot offset source) state
    after.heap = Function.update state.heap (BitVec.ofNat bits (header + offset)) (state.register source) ∧
      after.register .address = BitVec.ofNat bits header := by
  cases source <;>
    simp_all +decide [storeSlot, executeOps, packingExecuteOp, wordOp, wordInstruction,
      BitVec.ofNat_add_ofNat]

theorem loadSlot_access {bits : Nat} (rom : PhysicalROM) (offset header heapWords : Nat)
    (target : Register) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header) (ha : header + offset < heapWords)
    (count : Nat) (hc : count < (loadSlot offset target).length) :
    packingAccessFits rom heapWords (executeOps rom ((loadSlot offset target).take count) state)
      (loadSlot offset target)[count] := by
  change count < 3 at hc
  interval_cases count <;>
    simp +decide [loadSlot, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, hh, BitVec.ofNat_add_ofNat]
  exact (Nat.mod_le _ _).trans_lt ha

theorem storeSlot_access {bits : Nat} (rom : PhysicalROM) (offset header heapWords : Nat)
    (source : Register) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header) (ha : header + offset < heapWords)
    (count : Nat) (hc : count < (storeSlot offset source).length) :
    packingAccessFits rom heapWords (executeOps rom ((storeSlot offset source).take count) state)
      (storeSlot offset source)[count] := by
  change count < 3 at hc
  interval_cases count <;>
    simp +decide [storeSlot, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, hh, BitVec.ofNat_add_ofNat]
  exact (Nat.mod_le _ _).trans_lt ha

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010


