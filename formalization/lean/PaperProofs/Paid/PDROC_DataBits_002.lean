module

public import PaperProofs.Paid.PDROC_DataBits_001
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.DataBits

theorem den_add_common {a b : ℚ} {D : ℕ} (ha : a.den ∣ D) (hb : b.den ∣ D) :
    (a + b).den ∣ D := (Rat.add_den_dvd_lcm a b).trans (Nat.lcm_dvd ha hb)

theorem den_mul_common {a b : ℚ} {D E : ℕ} (ha : a.den ∣ D) (hb : b.den ∣ E) :
    (a * b).den ∣ D * E := (Rat.mul_den_dvd a b).trans (mul_dvd_mul ha hb)

def EntryDen (D : ℕ) (entry : MenuEntry) : Prop :=
  entry.observation.den ∣ D ∧ entry.repairs.den ∣ D ∧ entry.failure.den ∣ D

theorem entryDen_finish (D : ℕ) : EntryDen D finishEntry := by simp [EntryDen, finishEntry]

theorem entryDen_abandon (D : ℕ) : EntryDen D abandonEntry := by simp [EntryDen, abandonEntry]

theorem entryDen_repair {D : ℕ} {entry : MenuEntry} (h : EntryDen D entry) :
    EntryDen D (repairEntry entry) := by simpa [EntryDen, repairEntry] using h

theorem entryDen_mono {D E : ℕ} {entry : MenuEntry} (h : EntryDen D entry) (hDE : D ∣ E) :
    EntryDen E entry := ⟨h.1.trans hDE, h.2.1.trans hDE, h.2.2.trans hDE⟩

theorem menuBadBranch_entryDen (P : Parameters) (fee penalty : ℚ) (previous : MenuRow)
    (D tools : ℕ) (hprev : ∀ k, EntryDen D (previous.getD k abandonEntry)) :
    EntryDen D (P.menuBadBranch fee penalty previous tools).2 := by
  cases tools with
  | zero => exact entryDen_abandon D
  | succ tools =>
      unfold menuBadBranch
      dsimp only
      split_ifs
      · exact entryDen_repair (hprev tools)
      · exact entryDen_abandon D

theorem menu_scalar_den_dvd (P : Parameters) (fee q : ℚ) (hq : q ∈ P.menuScalars fee) :
    q.den ∣ P.menuCommonDenominator fee := by
  exact List.dvd_prod (List.mem_map.mpr ⟨q, hq, rfl⟩)

theorem endpoint_scalar_mem (P : Parameters) (fee : ℚ) (m : ℕ) (hm : m ≤ P.certificate.M) :
    (P.endpointConstant m).error ∈ P.menuScalars fee ∧
      (P.endpointConstant m).charge ∈ P.menuScalars fee := by
  have he : P.endpointConstant m ∈ P.endpointCache.toList := by
    simp only [endpointCache, Array.toList_ofFn, List.mem_ofFn]
    exact ⟨⟨m, by omega⟩, rfl⟩
  constructor
  · apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨P.endpointConstant m, he, by simp⟩
  · apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨P.endpointConstant m, he, by simp⟩

theorem cached_endpoint_den_dvd (P : Parameters) (fee : ℚ) (m : ℕ) (hm : m ≤ P.certificate.M) :
    (P.cachedEndpoint P.endpointCache m).error.den ∣ P.menuCommonDenominator fee ∧
      (P.cachedEndpoint P.endpointCache m).charge.den ∣ P.menuCommonDenominator fee := by
  rw [cachedEndpoint_eq]
  exact ⟨menu_scalar_den_dvd P fee _ (endpoint_scalar_mem P fee m hm).1,
    menu_scalar_den_dvd P fee _ (endpoint_scalar_mem P fee m hm).2⟩

theorem menuCommonDenominator_pos (P : Parameters) (fee : ℚ) : 0 < P.menuCommonDenominator fee := by
  unfold menuCommonDenominator
  apply List.prod_pos
  intro d hd
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hd
  exact q.den_pos

/-- One actual cached test introduces at most one new factor of the common
denominator, independently of the multiplier used for the comparisons. -/
theorem cachedMenuTestingEntry_entryDen (P : Parameters) (fee penalty : ℚ)
    (previous : MenuRow) (n tools level : ℕ) (hlevel : level ≤ P.certificate.M)
    (hprev : ∀ k, EntryDen ((P.menuCommonDenominator fee)^n) (previous.getD k abandonEntry)) :
    EntryDen ((P.menuCommonDenominator fee)^(n + 1))
      (P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools level) := by
  let D := P.menuCommonDenominator fee
  let good := previous.getD tools abandonEntry
  let bad := (P.menuBadBranch fee penalty previous tools).2
  let p := (P.cachedEndpoint P.endpointCache level).error
  let c := (P.cachedEndpoint P.endpointCache level).charge
  have hg : EntryDen (D^n) good := hprev tools
  have hb : EntryDen (D^n) bad := menuBadBranch_entryDen P fee penalty previous (D^n) tools hprev
  have hp : p.den ∣ D := (cached_endpoint_den_dvd P fee level hlevel).1
  have hc : c.den ∣ D := (cached_endpoint_den_dvd P fee level hlevel).2
  have hcomp : (1 - p).den ∣ D := by simpa using hp
  have hmul {a b : ℚ} (ha : a.den ∣ D) (hb : b.den ∣ D^n) : (a*b).den ∣ D^(n+1) := by
    simpa only [pow_succ'] using den_mul_common ha hb
  have hc' : c.den ∣ D^(n+1) := hc.trans (dvd_pow_self D (by omega))
  change (c + (1-p)*good.observation + p*bad.observation).den ∣ D^(n+1) ∧
    ((1-p)*good.repairs + p*bad.repairs).den ∣ D^(n+1) ∧
    ((1-p)*good.failure + p*bad.failure).den ∣ D^(n+1)
  exact ⟨den_add_common (den_add_common hc' (hmul hcomp hg.1)) (hmul hp hb.1),
    den_add_common (hmul hcomp hg.2.1) (hmul hp hb.2.1),
    den_add_common (hmul hcomp hg.2.2) (hmul hp hb.2.2)⟩

theorem cachedNextMenuEntry_entryDen (P : Parameters) (fee penalty : ℚ)
    (previous : MenuRow) (n tools : ℕ)
    (hprev : ∀ k, EntryDen ((P.menuCommonDenominator fee)^n) (previous.getD k abandonEntry)) :
    EntryDen ((P.menuCommonDenominator fee)^(n + 1))
      (P.cachedNextMenuEntry P.endpointCache fee penalty previous tools) := by
  have hl : P.cachedLeastTestingLevel P.endpointCache fee penalty previous tools ≤ P.certificate.M := by
    rw [cachedLeastTestingLevel_eq]
    exact (P.leastTestingLevel_spec fee penalty previous tools).1
  unfold cachedNextMenuEntry
  dsimp only
  split_ifs
  · exact entryDen_abandon _
  · exact entryDen_abandon _
  · exact cachedMenuTestingEntry_entryDen P fee penalty previous n tools _ hl hprev

theorem array_getD_pred {A : Type*} (values : Array A) (fallback : A) (predicate : A → Prop)
    (hf : predicate fallback) (hv : ∀ i (hi : i < values.size), predicate values[i]) (i : ℕ) :
    predicate (values.getD i fallback) := by
  by_cases hi : i < values.size
  · simpa only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
      using hv i hi
  · simpa only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_gt hi), Option.getD_none]
      using hf

theorem baseMenuRow_entryDen (tools k : ℕ) : EntryDen 1 ((baseMenuRow tools).getD k abandonEntry) := by
  apply array_getD_pred _ _ (EntryDen 1) (entryDen_abandon 1)
  intro i hi
  simpa only [baseMenuRow, Array.getElem_replicate] using entryDen_finish 1

theorem cachedNextMenuRow_entryDen (P : Parameters) (fee penalty : ℚ)
    (previous : MenuRow) (n tools k : ℕ)
    (hprev : ∀ j, EntryDen ((P.menuCommonDenominator fee)^n) (previous.getD j abandonEntry)) :
    EntryDen ((P.menuCommonDenominator fee)^(n+1))
      ((P.cachedNextMenuRow P.endpointCache fee penalty previous tools).getD k abandonEntry) := by
  apply array_getD_pred _ _ (EntryDen _) (entryDen_abandon _)
  intro i hi
  simpa only [cachedNextMenuRow, Array.getElem_ofFn] using
    cachedNextMenuEntry_entryDen P fee penalty previous n i hprev

theorem array_getD_default_eq {A : Type*} (values : Array A) (i : ℕ) (a b : A)
    (hi : i < values.size) : values.getD i a = values.getD i b := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]

theorem array_getD_push_lt {A : Type*} (values : Array A) (x fallback : A) (i : ℕ)
    (hi : i < values.size) : (values.push x).getD i fallback = values.getD i fallback := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, ite_eq_right (Nat.ne_of_lt hi)]

theorem array_getD_push_size {A : Type*} (values : Array A) (x fallback : A) :
    (values.push x).getD values.size fallback = x := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push_size, Option.getD_some]

theorem cachedSolveMenuTable_size (P : Parameters) (fee penalty : ℚ) (tools stages : ℕ) :
    (P.cachedSolveMenuTable P.endpointCache fee penalty tools stages).size = stages + 1 := by
  simpa only [cachedSolveMenuTable_eq] using P.solveMenuTable_size fee penalty tools stages

/-- The exact original cached table has the depth-indexed common-denominator
invariant in every stored row, including every fallback tool lookup. -/
theorem cachedSolveMenuTable_entryDen (P : Parameters) (fee penalty : ℚ) (tools stages n k : ℕ)
    (hn : n ≤ stages) :
    EntryDen ((P.menuCommonDenominator fee)^n)
      (menuEntryAt (P.cachedSolveMenuTable P.endpointCache fee penalty tools stages) n k) := by
  induction stages generalizing n k with
  | zero =>
      have hz : n = 0 := by omega
      subst n
      simpa [menuEntryAt, PaperProofs.Paid.Parameters.cachedSolveMenuTable] using baseMenuRow_entryDen tools k
  | succ stages ih =>
      let rows := P.cachedSolveMenuTable P.endpointCache fee penalty tools stages
      have hs : rows.size = stages + 1 := cachedSolveMenuTable_size P fee penalty tools stages
      by_cases hle : n ≤ stages
      · have hi : n < rows.size := by omega
        change EntryDen _ (((rows.push
          (P.cachedNextMenuRow P.endpointCache fee penalty (rows.getD stages (baseMenuRow tools)) tools)).getD n #[]).getD k abandonEntry)
        rw [array_getD_push_lt _ _ _ _ hi]
        exact ih n k hle
      · have he : n = stages + 1 := by omega
        subst n
        have hp : ∀ j, EntryDen ((P.menuCommonDenominator fee)^stages)
            ((rows.getD stages (baseMenuRow tools)).getD j abandonEntry) := by
          intro j
          rw [array_getD_default_eq rows stages (baseMenuRow tools) #[] (by omega)]
          exact ih stages j (le_refl _)
        change EntryDen _ (((rows.push
          (P.cachedNextMenuRow P.endpointCache fee penalty (rows.getD stages (baseMenuRow tools)) tools)).getD (stages+1) #[]).getD k abandonEntry)
        rw [← hs, array_getD_push_size]
        rw [hs]
        exact cachedNextMenuRow_entryDen P fee penalty _ stages tools k hp

theorem menu_objective_den_dvd (P : Parameters) (fee penalty : ℚ) (n : ℕ) (entry : MenuEntry)
    (h : EntryDen ((P.menuCommonDenominator fee)^n) entry) :
    (entry.objective fee penalty).den ∣ (P.menuCommonDenominator fee)^(n+1) * penalty.den := by
  let D := P.menuCommonDenominator fee
  have hf : fee.den ∣ D := menu_scalar_den_dvd P fee fee (by simp [menuScalars])
  have hpow : D^n ∣ D^(n+1) := pow_dvd_pow D (by omega)
  have ho : entry.observation.den ∣ D^(n+1) * penalty.den :=
    h.1.trans (hpow.trans (dvd_mul_right _ _))
  have hr : (fee*entry.repairs).den ∣ D^(n+1) * penalty.den := by
    have hx : (fee*entry.repairs).den ∣ D^(n+1) := by
      simpa only [pow_succ'] using den_mul_common hf h.2.1
    exact hx.trans (dvd_mul_right _ _)
  have hb : (penalty*entry.failure).den ∣ D^(n+1) * penalty.den := by
    simpa only [mul_comm] using den_mul_common (dvd_refl penalty.den) (h.2.2.trans hpow)
  exact den_add_common (den_add_common ho hr) hb

end PDROC.DataBits
