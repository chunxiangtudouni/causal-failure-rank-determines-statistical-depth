module

public import PaperProofs.Paid.PDMenu_MenuTableBounds_061
public import PaperProofs.Paid.PDMenu_PaidPenaltyProgram_059
public import PaperProofs.Paid.PDMenu_FiniteMenu_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open scoped ENNReal

namespace PDMenuNativeValue

open PaperProofs.Paid PDMenu

theorem menuEntry_objective_nonneg {entry : MenuEntry} {n k : ℕ} (h : MenuStatsBound entry n k)
    (fee penalty : ℚ) (hfee : 0 ≤ fee) (hpenalty : 0 ≤ penalty) : 0 ≤ entry.objective fee penalty :=
  add_nonneg (add_nonneg h.1 (mul_nonneg hfee h.2.1)) (mul_nonneg hpenalty h.2.2.2.1)

theorem menuWeightedObjectiveENN (charge p good bad : ℚ) (hc : 0 ≤ charge)
    (hp : 0 ≤ p) (hpone : p ≤ 1) (hg : 0 ≤ good) (hb : 0 ≤ bad) :
    ENNReal.ofReal ((charge + (1 - p) * good + p * bad : ℚ) : ℝ) =
      ENNReal.ofReal (charge : ℝ) + ENNReal.ofReal (1 - (p : ℝ)) * ENNReal.ofReal (good : ℝ) +
        ENNReal.ofReal (p : ℝ) * ENNReal.ofReal (bad : ℝ) := by
  have hcR : 0 ≤ (charge : ℝ) := by exact_mod_cast hc
  have hpR : 0 ≤ (p : ℝ) := by exact_mod_cast hp
  have hqR : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr (by exact_mod_cast hpone)
  have hgR : 0 ≤ (good : ℝ) := by exact_mod_cast hg
  have hbR : 0 ≤ (bad : ℝ) := by exact_mod_cast hb
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_one]
  rw [ENNReal.ofReal_add (add_nonneg hcR (mul_nonneg hqR hgR)) (mul_nonneg hpR hbR),
    ENNReal.ofReal_add hcR (mul_nonneg hqR hgR), ENNReal.ofReal_mul hqR, ENNReal.ofReal_mul hpR]

theorem menuBadBranch_value_eq (P : Parameters) (fee penalty : ℚ) (hfee : 0 ≤ fee) (hpenalty : 0 ≤ penalty)
    (previous : MenuRow) (n K k : ℕ) (hk : k ≤ K)
    (hstats : ∀ j : ℕ, MenuStatsBound (previous.getD j abandonEntry) n j)
    (hvalues : ∀ j : ℕ, j ≤ K → P.freshPaidPenalty fee hfee n j (ENNReal.ofReal (penalty : ℝ)) =
      ENNReal.ofReal ((previous.getD j abandonEntry).objective fee penalty : ℝ)) :
    ENNReal.ofReal ((P.menuBadBranch fee penalty previous k).2.objective fee penalty : ℝ) =
      P.paidBadSuccessor fee hfee (n + 1) k (ENNReal.ofReal (penalty : ℝ)) := by
  cases k with
  | zero => rw [P.menuBadBranch_zero]; rfl
  | succ k =>
    have hcost : 0 ≤ ((previous.getD k abandonEntry).objective fee penalty : ℝ) := by
      exact_mod_cast menuEntry_objective_nonneg (hstats k) fee penalty hfee hpenalty
    have hfR : 0 ≤ (fee : ℝ) := by exact_mod_cast hfee
    rw [P.menuBadBranch_succ, Rat.cast_min, ENNReal.ofReal_min, Rat.cast_add,
      ENNReal.ofReal_add hfR hcost, ← hvalues k (by omega)]
    rfl

theorem menuTestingEntry_value_eq (P : Parameters) (fee penalty : ℚ) (hfee : 0 ≤ fee) (hpenalty : 0 ≤ penalty)
    (previous : MenuRow) (n K k : ℕ) (hk : k ≤ K)
    (hstats : ∀ j : ℕ, MenuStatsBound (previous.getD j abandonEntry) n j)
    (hvalues : ∀ j : ℕ, j ≤ K → P.freshPaidPenalty fee hfee n j (ENNReal.ofReal (penalty : ℝ)) =
      ENNReal.ofReal ((previous.getD j abandonEntry).objective fee penalty : ℝ)) (m : ℕ) :
    ENNReal.ofReal ((P.menuTestingEntry fee penalty previous k m).objective fee penalty : ℝ) =
      P.paidEndpointObjective fee hfee (n + 1) k (ENNReal.ofReal (penalty : ℝ)) m := by
  rw [P.menuTestingEntry_objective, menuWeightedObjectiveENN _ _ _ _ (P.binarySymmetric.endpointCharge_nonneg m)
    (P.binarySymmetric.endpointError_pos m).le ((P.binarySymmetric.endpointError_le_half m).trans (by norm_num))
    (menuEntry_objective_nonneg (hstats k) fee penalty hfee hpenalty)
    (menuEntry_objective_nonneg (menuBadBranch_stats P fee penalty previous n k hstats) fee penalty hfee hpenalty)]
  rw [← hvalues k hk, menuBadBranch_value_eq P fee penalty hfee hpenalty previous n K k hk hstats hvalues]
  rfl

theorem nextMenuEntry_objective_min (P : Parameters) (fee penalty : ℚ) (hfee : 0 ≤ fee) (hpenalty : 0 ≤ penalty)
    (previous : MenuRow) (n k : ℕ)
    (hstats : ∀ j : ℕ, MenuStatsBound (previous.getD j abandonEntry) n j) :
    (P.nextMenuEntry fee penalty previous k).objective fee penalty =
      min penalty ((P.menuTestingEntry fee penalty previous k (P.leastTestingLevel fee penalty previous k)).objective fee penalty) := by
  have hbest := menuEntry_objective_nonneg (menuTestingEntry_stats P fee penalty previous n k
    (P.leastTestingLevel fee penalty previous k) (hstats k)
    (menuBadBranch_stats P fee penalty previous n k hstats)) fee penalty hfee hpenalty
  by_cases hz : penalty = 0
  · simp only [Parameters.nextMenuEntry, hz, ite_true]
    rw [min_eq_left (by simpa only [hz] using hbest)]
    simp only [abandonEntry, MenuEntry.objective, mul_zero, mul_one, add_zero]
  · dsimp only [Parameters.nextMenuEntry]
    rw [ite_eq_right hz]
    split_ifs with hcompare
    · simp only [abandonEntry, MenuEntry.objective, mul_zero, mul_one, add_zero, zero_add]
      exact (min_eq_left hcompare).symm
    · exact (min_eq_right (le_of_not_ge hcompare)).symm

theorem leastTestingLevel_value_inf (P : Parameters) (fee penalty : ℚ) (hfee : 0 ≤ fee) (hpenalty : 0 ≤ penalty)
    (hLambda : penalty ≤ P.Lambda) (previous : MenuRow) (n K k : ℕ) (hk : k ≤ K)
    (hstats : ∀ j : ℕ, MenuStatsBound (previous.getD j abandonEntry) n j)
    (hvalues : ∀ j : ℕ, j ≤ K → P.freshPaidPenalty fee hfee n j (ENNReal.ofReal (penalty : ℝ)) =
      ENNReal.ofReal ((previous.getD j abandonEntry).objective fee penalty : ℝ)) :
    ENNReal.ofReal ((P.menuTestingEntry fee penalty previous k (P.leastTestingLevel fee penalty previous k)).objective fee penalty : ℝ) =
      ⨅ m : ℕ, P.paidEndpointObjective fee hfee (n + 1) k (ENNReal.ofReal (penalty : ℝ)) m := by
  let chosen := P.leastTestingLevel fee penalty previous k
  have hs := P.leastTestingLevel_spec fee penalty previous k
  obtain ⟨m, hm, hmin⟩ := paidEndpointMinimumExists P fee hfee (n + 1) k (ENNReal.ofReal (penalty : ℝ))
    (Nat.zero_lt_succ n) ENNReal.ofReal_ne_top
  have hbound : m ≤ P.certificate.M := (paidFiniteMenu P).1 fee hfee (n + 1) k _ m (Nat.zero_lt_succ n)
    (ENNReal.ofReal_le_ofReal (by exact_mod_cast hLambda)) hm
  apply le_antisymm
  · calc
      _ ≤ ENNReal.ofReal ((P.menuTestingEntry fee penalty previous k m).objective fee penalty : ℝ) :=
        ENNReal.ofReal_le_ofReal (by exact_mod_cast hs.2.1 m hbound)
      _ = P.paidEndpointObjective fee hfee (n + 1) k (ENNReal.ofReal (penalty : ℝ)) m :=
        menuTestingEntry_value_eq P fee penalty hfee hpenalty previous n K k hk hstats hvalues m
      _ = _ := hmin.symm
  · exact (iInf_le (fun m => P.paidEndpointObjective fee hfee (n + 1) k (ENNReal.ofReal (penalty : ℝ)) m) chosen).trans
      (menuTestingEntry_value_eq P fee penalty hfee hpenalty previous n K k hk hstats hvalues chosen).symm.le

theorem nextMenuEntry_value_eq (P : Parameters) (fee penalty : ℚ) (hfee : 0 ≤ fee) (hpenalty : 0 ≤ penalty)
    (hLambda : penalty ≤ P.Lambda) (previous : MenuRow) (n K k : ℕ) (hk : k ≤ K)
    (hstats : ∀ j : ℕ, MenuStatsBound (previous.getD j abandonEntry) n j)
    (hvalues : ∀ j : ℕ, j ≤ K → P.freshPaidPenalty fee hfee n j (ENNReal.ofReal (penalty : ℝ)) =
      ENNReal.ofReal ((previous.getD j abandonEntry).objective fee penalty : ℝ)) :
    P.freshPaidPenalty fee hfee (n + 1) k (ENNReal.ofReal (penalty : ℝ)) =
      ENNReal.ofReal ((P.nextMenuEntry fee penalty previous k).objective fee penalty : ℝ) := by
  rw [paidExactPenaltyBellman P fee hfee (n + 1) k _ (Nat.zero_lt_succ n) ENNReal.ofReal_ne_top,
    nextMenuEntry_objective_min P fee penalty hfee hpenalty previous n k hstats,
    Rat.cast_min, ENNReal.ofReal_min,
    leastTestingLevel_value_inf P fee penalty hfee hpenalty hLambda previous n K k hk hstats hvalues]

end PDMenuNativeValue
