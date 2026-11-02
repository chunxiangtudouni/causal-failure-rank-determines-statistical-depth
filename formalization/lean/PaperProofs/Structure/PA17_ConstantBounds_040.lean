module
public import PaperProofs.Structure.AlgorithmClaims

/-! Increase only the uniform cost/space constant in the original claims.
Programs, word width, raw inputs, actual runs and all outputs are unchanged. -/
@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA17ConstantBounds040

open IndexedRAM IndexedClosureRAM AlgorithmClaims

theorem queryClaims_mono (small large wordFactor : Nat) (hc : small ≤ large)
    (implementation : Implementation) (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (t capWords heapWords : Nat) (stage : Fin (full.length + 1)) (used : Finset (Fin q)) (heap : Nat → Nat)
    (hs : QueryClaims small wordFactor implementation q full hq t capWords heapWords stage used heap) :
    QueryClaims large wordFactor implementation q full hq t capWords heapWords stage used heap :=
  ⟨hs.1.trans (Nat.mul_le_mul_right _ hc), hs.2⟩

theorem pathClaims_mono (small large wordFactor : Nat) (hc : small ≤ large)
    (implementation : Implementation) (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (t capWords heapWords : Nat) (requests : List (Request q full.length)) (heap : Nat → Nat)
    (hs : PathClaims small wordFactor implementation q full hq t capWords heapWords requests heap) :
    PathClaims large wordFactor implementation q full hq t capWords heapWords requests heap := by
  induction requests generalizing heap with
  | nil => trivial
  | cons request later ih =>
    exact ⟨queryClaims_mono small large wordFactor hc implementation q full hq t capWords heapWords
      request.stage request.used heap hs.1, ih _ hs.2⟩

theorem natRAMImplementationClaims_mono (small large wordFactor : Nat) (hc : small ≤ large)
    (implementation : Implementation) (hs : NatRAMImplementationClaims small wordFactor implementation) :
    NatRAMImplementationClaims large wordFactor implementation := by
  intro q full hq hlaminar
  obtain ⟨htable, hbits, hindex, hcost, hexecution, hcorrect, hcapacity, hqueries, hrolling, hrequests⟩ :=
    hs q full hq hlaminar
  refine ⟨htable, hbits.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc)),
    hindex.trans (Nat.mul_le_mul_right _ hc), hcost.trans (Nat.mul_le_mul_right _ hc),
    hexecution, hcorrect, hcapacity, ?_, ?_, ?_⟩
  · intro heap ht hp hf stage used
    exact queryClaims_mono small large wordFactor hc implementation q full hq _ _ _ stage used heap
      (hqueries heap ht hp hf stage used)
  · dsimp only
    intro used
    obtain ⟨hcap, hspace, hi, ht, he, hp, hr⟩ := hrolling used
    exact ⟨hcap, hspace.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc)),
      hi.trans (Nat.mul_le_mul_right _ hc), ht.trans (Nat.mul_le_mul_right _ hc), he, hp, hr⟩
  · intro requests hlength
    obtain ⟨hcost, hpath, hfinal⟩ := hrequests requests hlength
    exact ⟨hcost.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc)),
      pathClaims_mono small large wordFactor hc implementation q full hq _ _ _ requests _ hpath, hfinal⟩

theorem uniformCodeGenerationClaims_mono (small large wordFactor : Nat) (hc : small ≤ large)
    (implementation : Implementation) (packed : PackedPrograms)
    (hs : UniformCodeGenerationClaims small wordFactor implementation packed) :
    UniformCodeGenerationClaims large wordFactor implementation packed := by
  obtain ⟨generator, hg⟩ := hs
  refine ⟨generator, ?_⟩
  intro N q t hq ht hsize
  obtain ⟨steps, heapWords, hcode, hrom, hfit, hlength, hhalt, houtput, hprefix, hcost⟩ := hg N q t hq ht hsize
  exact ⟨steps, heapWords, hcode, hrom, hfit, hlength, hhalt, houtput, hprefix,
    hcost.trans (Nat.mul_le_mul_right _ hc)⟩

theorem packedPhaseRefines_mono (small large wordFactor N q t capWords indexWords : Nat) (hc : small ≤ large)
    (rom : PhysicalROM) (logical : List Op) (packed : List PackingOp)
    (heap : BitVec (indexWidth wordFactor N q) → BitVec (indexWidth wordFactor N q))
    (hs : PackedPhaseRefines small wordFactor N q t capWords indexWords rom logical packed heap) :
    PackedPhaseRefines large wordFactor N q t capWords indexWords rom logical packed heap := by
  obtain ⟨hrun, hregisters, hheap, hcapacity, hcost, hspace, ht⟩ := hs
  exact ⟨hrun, hregisters, hheap, hcapacity, hcost.trans (Nat.mul_le_mul_right _ hc), hspace, ht⟩

theorem packedImplementationClaims_mono (small large wordFactor : Nat) (hc : small ≤ large)
    (implementation : Implementation) (hs : PackedImplementationClaims small wordFactor implementation) :
    PackedImplementationClaims large wordFactor implementation := by
  obtain ⟨packed, hgen, hphases⟩ := hs
  refine ⟨packed, uniformCodeGenerationClaims_mono small large wordFactor hc implementation packed hgen, ?_⟩
  intro q full hq hlaminar
  obtain ⟨hbuild, hrolling, hquery⟩ := hphases q full hq hlaminar
  refine ⟨packedPhaseRefines_mono small large wordFactor _ _ _ _ _ hc _ _ _ _ hbuild, ?_, ?_⟩
  · intro used
    exact packedPhaseRefines_mono small large wordFactor _ _ _ _ _ hc _ _ _ _ (hrolling used)
  · intro heap
    dsimp only
    intro ht hp stage used
    exact packedPhaseRefines_mono small large wordFactor _ _ _ _ _ hc _ _ _ _ (hquery heap ht hp stage used)

/-- A final assembly rule only: its two substantive premises must both be
proved for the same actual implementation and the same word factor. -/
theorem fullGivenTree_of_nat_and_packed (natConstant packedConstant wordFactor : Nat)
    (implementation : Implementation) (hpositive : 0 < natConstant) (hword : 0 < wordFactor)
    (hnat : NatRAMImplementationClaims natConstant wordFactor implementation)
    (hpacked : PackedImplementationClaims packedConstant wordFactor implementation) : FullGivenTreeClaims :=
  ⟨max natConstant packedConstant, wordFactor, implementation,
    hpositive.trans_le (Nat.le_max_left _ _), hword,
    natRAMImplementationClaims_mono _ _ _ (Nat.le_max_left _ _) implementation hnat,
    packedImplementationClaims_mono _ _ _ (Nat.le_max_right _ _) implementation hpacked⟩

end PaperProofs.Structure.LaminarTree.PA17ConstantBounds040
