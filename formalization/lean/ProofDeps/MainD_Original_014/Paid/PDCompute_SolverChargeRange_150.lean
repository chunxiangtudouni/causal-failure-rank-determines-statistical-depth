module

public import Paid.PDCompute_SolverMaximumBits_054
public import PaperProofs.Paid.PDROC_DataBits_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PDROC.DataBits

/-- Generalize the existing original range argument to a bound on
ACTUAL cached charges, avoiding a raw gamma-size term in solver bits. -/
theorem solverTesting_range (P : Parameters) (fee penalty : ℚ) (C : ℚ)
    (Cnonneg : 0 ≤ C) (charges : ∀ m≤P.certificate.M,P.binarySymmetric.endpointCharge m ≤ C)
    (previous : MenuRow) (n tools level : ℕ) (hlevel : level ≤ P.certificate.M)
    (hprev : ∀ k,EntryRange P.certificate.M ((n:ℚ)*C) n (previous.getD k abandonEntry)) :
    EntryRange P.certificate.M (((n+1:ℕ):ℚ)*C) (n+1)
      (P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools level) := by
  let good:=previous.getD tools abandonEntry
  let bad:=(P.menuBadBranch fee penalty previous tools).2
  let p:=P.binarySymmetric.endpointError level
  let c:=P.binarySymmetric.endpointCharge level
  have hp0 : 0 ≤ p := (P.binarySymmetric.endpointError_pos level).le
  have hp1 : p ≤ 1 := (P.binarySymmetric.endpointError_le_half level).trans (by norm_num)
  have hg:=hprev tools
  have hb:=menuBadBranch_entryRange P fee penalty previous ((n:ℚ)*C) n tools (mul_nonneg (Nat.cast_nonneg _) Cnonneg) (Nat.cast_nonneg _) hprev
  have ho:=convex_bounds hp0 hp1 hg.observation_nonneg hg.observation_le hb.observation_nonneg hb.observation_le
  have hr:=convex_bounds hp0 hp1 hg.repairs_nonneg (hg.repairs_le.trans (by linarith)) hb.repairs_nonneg hb.repairs_le
  have hf:=convex_bounds hp0 hp1 hg.failure_nonneg hg.failure_le hb.failure_nonneg hb.failure_le
  have hc0 : 0 ≤ c := P.binarySymmetric.endpointCharge_nonneg level
  have hc : c ≤ C := charges level hlevel
  rw [cachedMenuTestingEntry_eq]
  change EntryRange _ _ _ (P.menuTestingEntry fee penalty previous tools level)
  refine ⟨?_,?_,hr.1,hr.2,hf.1,hf.2,?_⟩
  · change 0 ≤ c+(1-p)*good.observation+p*bad.observation
    linarith [ho.1]
  · change c+(1-p)*good.observation+p*bad.observation ≤ _
    push_cast
    nlinarith [ho.2]
  · change 3+natBits level ≤ 3+natBits P.certificate.M
    exact Nat.add_le_add_left (natBits_mono hlevel) 3

theorem solverNext_range (P : Parameters) (fee penalty : ℚ) (C : ℚ)
    (Cnonneg : 0 ≤ C) (charges : ∀ m≤P.certificate.M,P.binarySymmetric.endpointCharge m ≤ C)
    (previous : MenuRow) (n tools : ℕ)
    (hprev : ∀ k,EntryRange P.certificate.M ((n:ℚ)*C) n (previous.getD k abandonEntry)) :
    EntryRange P.certificate.M (((n+1:ℕ):ℚ)*C) (n+1)
      (P.cachedNextMenuEntry P.endpointCache fee penalty previous tools) := by
  have level : P.cachedLeastTestingLevel P.endpointCache fee penalty previous tools ≤ P.certificate.M := by
    rw [cachedLeastTestingLevel_eq]
    exact (P.leastTestingLevel_spec fee penalty previous tools).1
  unfold cachedNextMenuEntry
  dsimp only
  split_ifs
  · exact entryRange_abandon _ (mul_nonneg (Nat.cast_nonneg _) Cnonneg) (by positivity)
  · exact entryRange_abandon _ (mul_nonneg (Nat.cast_nonneg _) Cnonneg) (by positivity)
  · exact solverTesting_range P fee penalty C Cnonneg charges previous n tools _ level hprev

theorem solverNextRow_range (P : Parameters) (fee penalty : ℚ) (C : ℚ)
    (Cnonneg : 0 ≤ C) (charges : ∀ m≤P.certificate.M,P.binarySymmetric.endpointCharge m ≤ C)
    (previous : MenuRow) (n tools k : ℕ)
    (hprev : ∀ j,EntryRange P.certificate.M ((n:ℚ)*C) n (previous.getD j abandonEntry)) :
    EntryRange P.certificate.M (((n+1:ℕ):ℚ)*C) (n+1)
      ((P.cachedNextMenuRow P.endpointCache fee penalty previous tools).getD k abandonEntry) := by
  apply array_getD_pred _ _ (EntryRange _ _ _)
    (entryRange_abandon _ (mul_nonneg (Nat.cast_nonneg _) Cnonneg) (by positivity))
  intro i hi
  simpa only [cachedNextMenuRow,Array.getElem_ofFn] using solverNext_range P fee penalty C Cnonneg charges previous n i hprev

theorem solverTable_range (P : Parameters) (fee penalty : ℚ) (C : ℚ)
    (Cnonneg : 0 ≤ C) (charges : ∀ m≤P.certificate.M,P.binarySymmetric.endpointCharge m ≤ C)
    (tools stages row column : ℕ) (inside : row ≤ stages) :
    EntryRange P.certificate.M ((row:ℚ)*C) row
      (menuEntryAt (P.cachedSolveMenuTable P.endpointCache fee penalty tools stages) row column) := by
  induction stages generalizing row column with
  | zero =>
    have equal : row=0 := by omega
    subst row
    simpa [menuEntryAt,PaperProofs.Paid.Parameters.cachedSolveMenuTable] using baseMenuRow_entryRange P tools column
  | succ stages ih =>
    let rows:=P.cachedSolveMenuTable P.endpointCache fee penalty tools stages
    have size : rows.size=stages+1 := cachedSolveMenuTable_size P fee penalty tools stages
    by_cases earlier : row ≤ stages
    · have valid : row<rows.size := by omega
      change EntryRange _ _ _ (((rows.push (P.cachedNextMenuRow P.endpointCache fee penalty (rows.getD stages (baseMenuRow tools)) tools)).getD row #[]).getD column abandonEntry)
      rw [array_getD_push_lt _ _ _ _ valid]
      exact ih row column earlier
    · have equal : row=stages+1 := by omega
      subst row
      have previous : ∀ j,EntryRange P.certificate.M ((stages:ℚ)*C) stages ((rows.getD stages (baseMenuRow tools)).getD j abandonEntry) := by
        intro j
        rw [array_getD_default_eq rows stages (baseMenuRow tools) #[] (by omega)]
        exact ih stages j (le_refl _)
      change EntryRange _ _ _ (((rows.push (P.cachedNextMenuRow P.endpointCache fee penalty (rows.getD stages (baseMenuRow tools)) tools)).getD (stages+1) #[]).getD column abandonEntry)
      rw [←size,array_getD_push_size,size]
      simpa only [Nat.cast_add,Nat.cast_one] using solverNextRow_range P fee penalty C Cnonneg charges _ stages tools column previous

end PDCompute.Solver
