module

public import PaperProofs.Structure.PSTR_UniformPositiveQuery_121
public import PaperProofs.Structure.PSTR_UniformZeroQuery_112

/-! Original QUERY on ONE guarded1371 body, ALL q including0, arbitrary
entry registers. The actual q0 and positive runs return to the same exit;
all original reply/representation/table/capacity/safety facts share clock. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRUniformQuery

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRCountKernel PA17A19RuntimeEntry020

def budget {q : Nat} (full : List (Finset (Fin q))) : Nat :=
  if q = 0 then 44 else PSTRUniformPositiveQuery.budget full

theorem budget_bound {q : Nat} (full : List (Finset (Fin q))) :
    budget full ≤ 1790 * liveWork q (treeSize q full) := by
  by_cases hq : q = 0
  · subst q
    simp only [budget, ite_true, liveWork]
    omega
  · simpa only [budget, hq, ite_false] using PSTRUniformPositiveQuery.budget_bound full (Nat.pos_of_ne_zero hq)

theorem actual_query {q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (allowed : Allowed full configuration .query)
    (hl : LaminarSchedule full) (whole : List PackingOp) (contains : PSTRUniformQueryCode.Contains whole)
    (hw : WordsFit (wordBits full) (packingCode whole)) (hpc : Fits (wordBits full) (5 * whole.length))
    (state : WordState (wordBits full)) (hp : state.pc = BitVec.ofNat (wordBits full) 0) (ha : state.halted = false)
    (rep : HeapRepresents q full (capacity full) configuration state.heap) :
    ∃ steps ≤ budget full, PSTRUniformPositiveQuery.Result full .query configuration allowed whole state steps := by
  by_cases hq : q = 0
  · subst q
    rcases configuration with ⟨stage, used, failed⟩
    have hf : failed = false := allowed.1
    subst failed
    let stg := cursor full ⟨stage, used, false⟩ .query allowed
    have zero := PSTRUniformZeroQuery.actual_query full used stg whole 1345 1371
      (PSTRUniformQueryCode.bootstrap_in whole contains) (PSTRUniformQueryCode.zero_in whole contains)
      (PSTRUniformQueryCode.zero_return_in whole contains) hw hpc state hp ha rep
    refine ⟨44, Nat.le_refl _, ?_⟩
    refine ⟨zero.2.1, zero.1, zero.2.2.2.1, ?_, ?_, ?_, ?_, zero.2.2.2.2.2.1, ?_⟩
    · intro clock hc
      rw [zero.2.2.2.2.1 clock hc]
      exact rep
    · intro clock hc
      change CapacityPrefixBounded 0 0 _
      intro address haddress
      omega
    · intro clock hc address _ha
      rw [zero.2.2.2.2.1 clock hc]
    · intro clock hc physical _hf _hh
      rw [zero.2.2.2.2.1 clock hc]
    · intro hq
      omega
  · obtain ⟨steps, upper, result⟩ := PSTRUniformPositiveQuery.actual_query full .query configuration allowed
      (Nat.pos_of_ne_zero hq) hl whole contains hw hpc state hp ha rep
    exact ⟨steps, by simpa only [budget, hq, ite_false] using upper, result⟩

end PaperProofs.Structure.LaminarTree.PSTRUniformQuery
