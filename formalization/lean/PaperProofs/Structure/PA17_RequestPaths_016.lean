module

public import PaperProofs.Structure.AlgorithmClaims
import Mathlib.Tactic.Ring

/-! Composition for the ORIGINAL arbitrary request-list and persistent heap
interface. This file is conditional on the original per-query QueryClaims
for every original admissible incoming heap; it does not construct that
implementation or assert A17. Scratch is never reset between requests. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17RequestPaths016

open IndexedRAM IndexedClosureRAM AlgorithmClaims

/-- Exactly the three original admissibility conditions, without metadata,
physical-card or semantic-entry normalization assumptions. -/
def HeapReady (wordFactor q : Nat) (full : List (Finset (Fin q)))
    (capWords heapWords : Nat) (heap : Nat → Nat) : Prop :=
  PhysicalTableCorrect q full heap ∧ CapacityPrefixBounded q capWords heap ∧
    ∀ address < heapWords, Fits (indexWidth wordFactor full.length q) (heap address)

theorem tableWord_lt (N q t slot : Nat) (hslot : slot < cells N q) (index : Nat) (hi : index ≤ t) :
    slot * (t + 1) + index < tableWords N q t := by
  have hh := Nat.mul_le_mul_right (t + 1) (show slot + 1 ≤ cells N q from by omega)
  rw [Nat.add_mul, Nat.one_mul] at hh
  unfold tableWords
  omega

theorem rowSlot_lt (N q : Nat) (stage : Fin (N + 1)) (budget : Fin (q + 2)) :
    stage.val * (q + 2) + budget.val < cells N q := by
  have hh := Nat.mul_le_mul_right (q + 2) (show stage.val + 1 ≤ N + 1 from stage.isLt)
  rw [Nat.add_mul, Nat.one_mul] at hh
  unfold cells
  have hb := budget.isLt
  omega

theorem readEntry_of_table_frame (N q t slot : Nat) (hslot : slot < cells N q)
    (old fresh : Nat → Nat)
    (hframe : ∀ address < tableWords N q t, fresh address = old address) :
    readEntry t slot fresh = readEntry t slot old := by
  have ht := hframe (slot * (t + 1)) (by
    simpa only [Nat.add_zero] using tableWord_lt N q t slot hslot 0 (Nat.zero_le _))
  simp only [readEntry, ht]
  split_ifs
  · rfl
  · apply congrArg CapacityBits.Entry.vector
    apply Vector.ext
    intro index hi
    change (Vector.ofFn _).get ⟨index, hi⟩ = (Vector.ofFn _).get ⟨index, hi⟩
    rw [cache_get_ofFn, cache_get_ofFn,
      hframe _ (by
        simpa only [Nat.add_assoc] using tableWord_lt N q t slot hslot (1 + index) (by omega))]

theorem physicalTableCorrect_of_frame (q : Nat) (full : List (Finset (Fin q)))
    (old fresh : Nat → Nat) (htable : PhysicalTableCorrect q full old)
    (hframe : ∀ address < tableWords full.length q (prepareNormalization q full).indexed.nodes.size,
      fresh address = old address) :
    PhysicalTableCorrect q full fresh := by
  constructor
  · intro stage budget
    rw [readEntry_of_table_frame full.length q _ _ (rowSlot_lt full.length q stage budget) old fresh hframe]
    exact htable.1 stage budget
  · intro slot hs
    rw [hframe _ (by
      simpa only [Nat.add_zero] using tableWord_lt full.length q _ slot hs 0 (Nat.zero_le _))]
    exact htable.2 slot hs

/-- The final *actual* query heap is admissible for the next query.
The size is the original given-tree size used in NatRAMImplementationClaims. -/
theorem query_preserves_heapReady (constant wordFactor : Nat) (implementation : Implementation)
    (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (capWords heapWords : Nat)
    (stage : Fin (full.length + 1)) (used : Finset (Fin q)) (heap : Nat → Nat)
    (hready : HeapReady wordFactor q full capWords heapWords heap)
    (hquery : QueryClaims constant wordFactor implementation q full hq
      (prepareNormalization q full).indexed.nodes.size capWords heapWords stage used heap) :
    HeapReady wordFactor q full capWords heapWords
      (execute (queryROM q full stage.val used).semantic
        (implementation.queryProgram full.length q (prepareNormalization q full).indexed.nodes.size)
        (initial heap)).heap := by
  let code := implementation.queryProgram full.length q (prepareNormalization q full).indexed.nodes.size
  have hcapacity := hquery.2.2.2.2 code.length le_rfl
  rw [List.take_length] at hcapacity
  have hstate := hquery.2.1.1.2.2.2.1 code.length le_rfl
  rw [List.take_length] at hstate
  exact ⟨physicalTableCorrect_of_frame q full heap _ hready.1 hquery.2.2.2.1, hcapacity, hstate.2.2⟩

theorem pathCost_eq (implementation : Implementation) (q : Nat) (full : List (Finset (Fin q)))
    (t : Nat) (requests : List (Request q full.length)) :
    pathCost implementation q full t requests =
      requests.length * totalQueryCost q (implementation.queryProgram full.length q t) := by
  simp only [pathCost, List.map_const', List.sum_replicate, Nat.nsmul_eq_mul]

theorem pathCost_le_of_query_cost (constant : Nat) (implementation : Implementation)
    (q : Nat) (full : List (Finset (Fin q))) (t : Nat)
    (hcost : totalQueryCost q (implementation.queryProgram full.length q t) ≤ constant * queryWork q t)
    (requests : List (Request q full.length)) :
    pathCost implementation q full t requests ≤ constant * requests.length * queryWork q t := by
  rw [pathCost_eq]
  calc
    _ ≤ requests.length * (constant * queryWork q t) := Nat.mul_le_mul_left requests.length hcost
    _ = _ := by ring

/-- The original incoming-heap quantifiers are retained verbatim. Every
induction step uses the actual heap output of the preceding query, including
all reused scratch words. No table/card/metadata oracle is added. -/
theorem requests_preserve_heapReady (constant wordFactor : Nat) (implementation : Implementation)
    (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (capWords heapWords : Nat)
    (hqueries : ∀ heap : Nat → Nat, PhysicalTableCorrect q full heap →
      CapacityPrefixBounded q capWords heap →
      (∀ address < heapWords, Fits (indexWidth wordFactor full.length q) (heap address)) →
      ∀ stage : Fin (full.length + 1), ∀ used : Finset (Fin q),
      QueryClaims constant wordFactor implementation q full hq
        (prepareNormalization q full).indexed.nodes.size capWords heapWords stage used heap)
    (requests : List (Request q full.length)) (heap : Nat → Nat)
    (hready : HeapReady wordFactor q full capWords heapWords heap) :
    PathClaims constant wordFactor implementation q full hq
      (prepareNormalization q full).indexed.nodes.size capWords heapWords requests heap ∧
      HeapReady wordFactor q full capWords heapWords
        (pathExecute implementation q full (prepareNormalization q full).indexed.nodes.size requests heap) := by
  induction requests generalizing heap with
  | nil => exact ⟨True.intro, hready⟩
  | cons request later ih =>
    have hclaim := hqueries heap hready.1 hready.2.1 hready.2.2 request.stage request.used
    have hn := query_preserves_heapReady constant wordFactor implementation q full hq capWords heapWords
      request.stage request.used heap hready hclaim
    obtain ⟨hlater, hfinal⟩ := ih _ hn
    exact ⟨⟨hclaim, hlater⟩, hfinal⟩

theorem requests_claims_and_cost (constant wordFactor : Nat) (implementation : Implementation)
    (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (capWords heapWords : Nat)
    (hqueries : ∀ heap : Nat → Nat, PhysicalTableCorrect q full heap →
      CapacityPrefixBounded q capWords heap →
      (∀ address < heapWords, Fits (indexWidth wordFactor full.length q) (heap address)) →
      ∀ stage : Fin (full.length + 1), ∀ used : Finset (Fin q),
      QueryClaims constant wordFactor implementation q full hq
        (prepareNormalization q full).indexed.nodes.size capWords heapWords stage used heap)
    (requests : List (Request q full.length)) (heap : Nat → Nat)
    (hready : HeapReady wordFactor q full capWords heapWords heap) :
    pathCost implementation q full (prepareNormalization q full).indexed.nodes.size requests ≤
        constant * requests.length * queryWork q (prepareNormalization q full).indexed.nodes.size ∧
      PathClaims constant wordFactor implementation q full hq
        (prepareNormalization q full).indexed.nodes.size capWords heapWords requests heap ∧
      HeapReady wordFactor q full capWords heapWords
        (pathExecute implementation q full (prepareNormalization q full).indexed.nodes.size requests heap) := by
  have hcost := (hqueries heap hready.1 hready.2.1 hready.2.2 ⟨0, by omega⟩ ∅).1
  exact ⟨pathCost_le_of_query_cost constant implementation q full _ hcost requests,
    requests_preserve_heapReady constant wordFactor implementation q full hq capWords heapWords
      hqueries requests heap hready⟩

/-- The exact <=N request conclusion required by the final conjunct of
NatRAMImplementationClaims, still conditional on the original query proof. -/
theorem bounded_requests_claims (constant wordFactor : Nat) (implementation : Implementation)
    (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (capWords heapWords : Nat)
    (hqueries : ∀ heap : Nat → Nat, PhysicalTableCorrect q full heap →
      CapacityPrefixBounded q capWords heap →
      (∀ address < heapWords, Fits (indexWidth wordFactor full.length q) (heap address)) →
      ∀ stage : Fin (full.length + 1), ∀ used : Finset (Fin q),
      QueryClaims constant wordFactor implementation q full hq
        (prepareNormalization q full).indexed.nodes.size capWords heapWords stage used heap)
    (requests : List (Request q full.length)) (hrequests : requests.length ≤ full.length)
    (heap : Nat → Nat) (hready : HeapReady wordFactor q full capWords heapWords heap) :
    pathCost implementation q full (prepareNormalization q full).indexed.nodes.size requests ≤
        constant * full.length * queryWork q (prepareNormalization q full).indexed.nodes.size ∧
      PathClaims constant wordFactor implementation q full hq
        (prepareNormalization q full).indexed.nodes.size capWords heapWords requests heap ∧
      PhysicalTableCorrect q full
        (pathExecute implementation q full (prepareNormalization q full).indexed.nodes.size requests heap) := by
  obtain ⟨hcost, hpath, hfinal⟩ := requests_claims_and_cost constant wordFactor implementation q full hq
    capWords heapWords hqueries requests heap hready
  refine ⟨hcost.trans ?_, hpath, hfinal.1⟩
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left constant hrequests)

end PaperProofs.Structure.LaminarTree.PA17RequestPaths016
