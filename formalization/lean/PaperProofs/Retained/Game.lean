module

public import PaperProofs.Retained.Matroid
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.TakeDrop

set_option autoImplicit false
set_option warningAsError true

/-!
The independent retained first-failure game of `price-proofs.tex:313-341`.
Declarations advance in the given finite stage list. An error adds its stage
to the discovered set, and execution stops at the first unmatchable set.
This is not yet a native terminal-matching controller or its stochastic bridge.
-/

@[expose] public section

namespace PaperProofs.Retained

open Common

variable {I : Instance}

/-- The error-set index records actual declarations made before termination;
the natural-number index counts those errors along the play. -/
inductive Play (I : Instance) : List I.Stage → Finset I.Stage → Finset I.Stage → ℕ → Bool → Prop where
  | failed (later : List I.Stage) (past : Finset I.Stage) (bad : ¬ Matchable I past) :
      Play I later past ∅ 0 false
  | terminal (past : Finset I.Stage) (healthy : Matchable I past) : Play I [] past ∅ 0 true
  | correct {i : I.Stage} {later : List I.Stage} {past errors : Finset I.Stage}
      {count : ℕ} {success : Bool} (healthy : Matchable I past)
      (continuation : Play I later past errors count success) :
      Play I (i :: later) past errors count success
  | error {i : I.Stage} {later : List I.Stage} {past errors : Finset I.Stage}
      {count : ℕ} {success : Bool} (healthy : Matchable I past)
      (continuation : Play I later (insert i past) errors count success) :
      Play I (i :: later) past (insert i errors) (count + 1) success

def Safe (I : Instance) (later : List I.Stage) (past : Finset I.Stage) (budget : ℕ) : Prop :=
  ∀ count, count ≤ budget → ∀ errors, ¬ Play I later past errors count false

private theorem union_insert (past errors : Finset I.Stage) (i : I.Stage) :
    past ∪ insert i errors = insert i past ∪ errors := by
  ext j
  simp only [Finset.mem_union, Finset.mem_insert]
  tauto

theorem Play.success_or_unmatchable {later : List I.Stage} {past errors : Finset I.Stage}
    {count : ℕ} {success : Bool} (play : Play I later past errors count success) :
    success = true ∨ ¬ Matchable I (past ∪ errors) := by
  induction play with
  | failed _ _ hbad => exact Or.inr (by simpa only [Finset.union_empty] using hbad)
  | terminal => exact Or.inl rfl
  | correct _ _ ih => exact ih
  | error _ _ ih =>
    rcases ih with hsuccess | hbad
    · exact Or.inl hsuccess
    · exact Or.inr (by rwa [union_insert])

theorem Play.failure_unmatchable {later : List I.Stage} {past errors : Finset I.Stage}
    {count : ℕ} (play : Play I later past errors count false) :
    ¬ Matchable I (past ∪ errors) := by
  simpa only [Bool.false_eq_true, false_or] using play.success_or_unmatchable

theorem Play.errors_subset {later : List I.Stage} {past errors : Finset I.Stage}
    {count : ℕ} {success : Bool} (play : Play I later past errors count success) :
    errors ⊆ later.toFinset := by
  induction play with
  | failed => exact Finset.empty_subset _
  | terminal => exact Finset.empty_subset _
  | correct _ _ ih =>
    simp only [List.toFinset_cons]
    exact ih.trans (Finset.subset_insert _ _)
  | error _ _ ih =>
    simp only [List.toFinset_cons]
    apply Finset.insert_subset_iff.mpr
    exact ⟨by simp, ih.trans (Finset.subset_insert _ _)⟩

theorem Play.error_card_le {later : List I.Stage} {past errors : Finset I.Stage}
    {count : ℕ} {success : Bool} (play : Play I later past errors count success) :
    errors.card ≤ count := by
  induction play with
  | failed => simp
  | terminal => simp
  | correct _ _ ih => exact ih
  | @error i later past errors count success _ _ ih =>
    exact (Finset.card_insert_le i errors).trans (Nat.add_le_add_right ih 1)

/-- Every unmatchable proposed continuation has a real first-failure play
using only its declared errors and no more than their cardinality. -/
theorem first_failure_of_unmatchable {later : List I.Stage} {past proposed : Finset I.Stage}
    (hfuture : proposed ⊆ later.toFinset) (hbad : ¬ Matchable I (past ∪ proposed)) :
    ∃ errors count, Play I later past errors count false ∧ errors ⊆ proposed ∧ count ≤ proposed.card := by
  induction later generalizing past proposed with
  | nil =>
    have hempty : proposed = ∅ := Finset.subset_empty.mp (by simpa only [List.toFinset_nil] using hfuture)
    have hpast : ¬ Matchable I past := by simpa only [hempty, Finset.union_empty] using hbad
    exact ⟨∅, 0, .failed [] past hpast, Finset.empty_subset _, Nat.zero_le _⟩
  | cons i later ih =>
    by_cases hpast : Matchable I past
    · by_cases hi : i ∈ proposed
      · have hfuture' : proposed.erase i ⊆ later.toFinset := by
          intro j hj
          have hne := (Finset.mem_erase.mp hj).1
          have hmem := hfuture (Finset.mem_erase.mp hj).2
          simpa only [List.toFinset_cons, Finset.mem_insert, hne, false_or] using hmem
        have heq : insert i past ∪ proposed.erase i = past ∪ proposed := by
          ext j
          by_cases hji : j = i <;> simp [hji, hi, or_comm]
        have hbad' : ¬ Matchable I (insert i past ∪ proposed.erase i) := heq ▸ hbad
        obtain ⟨errors, count, hplay, herrors, hcount⟩ := ih hfuture' hbad'
        refine ⟨insert i errors, count + 1, .error hpast hplay, ?_, ?_⟩
        · exact Finset.insert_subset_iff.mpr ⟨hi, herrors.trans (Finset.erase_subset _ _)⟩
        · have hcard := Finset.card_erase_add_one hi
          omega
      · have hfuture' : proposed ⊆ later.toFinset := by
          intro j hj
          have hmem := hfuture hj
          rcases (show j = i ∨ j ∈ later.toFinset by simpa only [List.toFinset_cons, Finset.mem_insert] using hmem) with hji | htail
          · exact False.elim (hi (hji ▸ hj))
          · exact htail
        obtain ⟨errors, count, hplay, herrors, hcount⟩ := ih hfuture' hbad
        exact ⟨errors, count, .correct hpast hplay, herrors, hcount⟩
    · exact ⟨∅, 0, .failed _ past hpast, Finset.empty_subset _, Nat.zero_le _⟩

theorem safe_iff_future_sets (I : Instance) (later : List I.Stage) (past : Finset I.Stage) (budget : ℕ) :
    Safe I later past budget ↔ ∀ proposed ⊆ later.toFinset,
      proposed.card ≤ budget → Matchable I (past ∪ proposed) := by
  constructor
  · intro hsafe proposed hfuture hcard
    by_contra hbad
    obtain ⟨errors, count, hplay, _, hcount⟩ := first_failure_of_unmatchable hfuture hbad
    exact hsafe count (hcount.trans hcard) errors hplay
  · intro hall count hcount errors hplay
    exact hplay.failure_unmatchable
      (hall errors hplay.errors_subset (hplay.error_card_le.trans hcount))

theorem Safe.mono {later : List I.Stage} {past : Finset I.Stage} {small large : ℕ}
    (h : Safe I later past large) (hle : small ≤ large) : Safe I later past small :=
  fun count hcount errors => h count (hcount.trans hle) errors

theorem safe_zero_iff (I : Instance) (later : List I.Stage) (past : Finset I.Stage) :
    Safe I later past 0 ↔ Matchable I past := by
  rw [safe_iff_future_sets]
  constructor
  · intro h
    simpa only [Finset.union_empty] using h ∅ (Finset.empty_subset _) (by simp)
  · intro hpast proposed _ hcard
    have hempty : proposed = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
    simpa only [hempty, Finset.union_empty] using hpast

theorem not_safe_iff_future_set (I : Instance) (later : List I.Stage)
    (past : Finset I.Stage) (budget : ℕ) :
    ¬ Safe I later past budget ↔ ∃ proposed ⊆ later.toFinset,
      proposed.card ≤ budget ∧ ¬ Matchable I (past ∪ proposed) := by
  classical
  constructor
  · intro hbad
    by_contra hnone
    apply hbad
    apply (safe_iff_future_sets I later past budget).mpr
    intro proposed hfuture hcard
    by_contra hunmatchable
    exact hnone ⟨proposed, hfuture, hcard, hunmatchable⟩
  · rintro ⟨proposed, hfuture, hcard, hbad⟩ hsafe
    exact hbad ((safe_iff_future_sets I later past budget).mp hsafe proposed hfuture hcard)

/-- Minimum genuinely unsafe budget of the first-failure Play semantics.
Infinity means every finite adversarial error budget is safe. -/
noncomputable def errorRank (I : Instance) (later : List I.Stage) (past : Finset I.Stage) : ℕ∞ := by
  classical
  exact if h : ∃ budget, ¬ Safe I later past budget then (Nat.find h : ℕ∞) else ⊤

theorem rank_le_nat_iff (I : Instance) (later : List I.Stage) (past : Finset I.Stage) (budget : ℕ) :
    errorRank I later past ≤ (budget : ℕ∞) ↔ ¬ Safe I later past budget := by
  classical
  unfold errorRank
  split_ifs with hex
  · constructor
    · intro hle hsafe
      exact Nat.find_spec hex (hsafe.mono (ENat.natCast_le_natCast.mp hle))
    · intro hbad
      exact ENat.natCast_le_natCast.mpr (Nat.find_min' hex hbad)
  · constructor
    · intro hle
      exact False.elim (ENat.natCast_ne_top budget (top_le_iff.mp hle))
    · intro hbad
      exact False.elim (hex ⟨budget, hbad⟩)

theorem safe_iff_lt_errorRank (I : Instance) (later : List I.Stage)
    (past : Finset I.Stage) (budget : ℕ) :
    Safe I later past budget ↔ (budget : ℕ∞) < errorRank I later past := by
  rw [lt_iff_not_ge, rank_le_nat_iff]
  exact not_not.symm

theorem rank_eq_top_iff (I : Instance) (later : List I.Stage) (past : Finset I.Stage) :
    errorRank I later past = ⊤ ↔ ∀ budget, Safe I later past budget := by
  classical
  constructor
  · intro htop budget
    apply (safe_iff_lt_errorRank I later past budget).mpr
    rw [htop]
    exact ENat.natCast_lt_top budget
  · intro hall
    unfold errorRank
    split_ifs with hex
    · exact False.elim (Nat.find_spec hex (hall (Nat.find hex)))
    · rfl

theorem rank_eq_nat_iff (I : Instance) (later : List I.Stage) (past : Finset I.Stage) (budget : ℕ) :
    errorRank I later past = (budget : ℕ∞) ↔
      ¬ Safe I later past budget ∧ ∀ smaller < budget, Safe I later past smaller := by
  classical
  unfold errorRank
  split_ifs with hex
  · constructor
    · intro heq
      have hfind : Nat.find hex = budget := by exact_mod_cast heq
      refine ⟨by simpa only [hfind] using Nat.find_spec hex, ?_⟩
      intro smaller hlt
      by_contra hbad
      exact Nat.find_min hex (by simpa only [hfind] using hlt) hbad
    · rintro ⟨hbad, hsmall⟩
      have hfind : Nat.find hex = budget := by
        apply Nat.le_antisymm (Nat.find_min' hex hbad)
        apply Nat.le_of_not_gt
        intro hlt
        exact Nat.find_spec hex (hsmall _ hlt)
      rw [hfind]
  · constructor
    · intro heq
      exact False.elim (ENat.natCast_ne_top budget heq.symm)
    · rintro ⟨hbad, _⟩
      exact False.elim (hex ⟨budget, hbad⟩)

theorem rank_le_nat_iff_future_set (I : Instance) (later : List I.Stage)
    (past : Finset I.Stage) (budget : ℕ) :
    errorRank I later past ≤ (budget : ℕ∞) ↔ ∃ proposed ⊆ later.toFinset,
      proposed.card ≤ budget ∧ ¬ Matchable I (past ∪ proposed) := by
  rw [rank_le_nat_iff, not_safe_iff_future_set]

def dependentExtensions (I : Instance) (later : List I.Stage) (past : Finset I.Stage) :
    Finset (Finset I.Stage) :=
  later.toFinset.powerset.filter (fun proposed => ¬ Matchable I (past ∪ proposed))

theorem mem_dependentExtensions (I : Instance) (later : List I.Stage)
    (past proposed : Finset I.Stage) :
    proposed ∈ dependentExtensions I later past ↔
      proposed ⊆ later.toFinset ∧ ¬ Matchable I (past ∪ proposed) := by
  simp only [dependentExtensions, Finset.mem_filter, Finset.mem_powerset]

/-- The finite-set minimum appearing in B:318-319, defined separately from
the semantic rank and only identified with it by the theorem below. -/
noncomputable def dependenceDepth (I : Instance) (later : List I.Stage) (past : Finset I.Stage) : ℕ∞ :=
  (dependentExtensions I later past).inf (fun proposed => (proposed.card : ℕ∞))

theorem depth_le_nat_iff (I : Instance) (later : List I.Stage)
    (past : Finset I.Stage) (budget : ℕ) :
    dependenceDepth I later past ≤ (budget : ℕ∞) ↔ ∃ proposed ⊆ later.toFinset,
      proposed.card ≤ budget ∧ ¬ Matchable I (past ∪ proposed) := by
  constructor
  · intro hle
    have hnonempty : (dependentExtensions I later past).Nonempty := by
      by_contra h
      have hempty := Finset.not_nonempty_iff_eq_empty.mp h
      have htop : dependenceDepth I later past = ⊤ := by simp only [dependenceDepth, hempty, Finset.inf_empty]
      rw [htop] at hle
      exact ENat.natCast_ne_top budget (top_le_iff.mp hle)
    obtain ⟨proposed, hmem, heq⟩ := Finset.exists_mem_eq_inf
      (dependentExtensions I later past) hnonempty (fun proposed => (proposed.card : ℕ∞))
    have hdata := (mem_dependentExtensions I later past proposed).mp hmem
    refine ⟨proposed, hdata.1, ?_, hdata.2⟩
    apply ENat.natCast_le_natCast.mp
    rwa [← heq]
  · rintro ⟨proposed, hfuture, hcard, hbad⟩
    have hmem := (mem_dependentExtensions I later past proposed).mpr ⟨hfuture, hbad⟩
    exact (Finset.inf_le hmem).trans (ENat.natCast_le_natCast.mpr hcard)

private theorem enat_eq_of_le_nat_iff {left right : ℕ∞}
    (h : ∀ budget : ℕ, left ≤ budget ↔ right ≤ budget) : left = right := by
  have hall (bound : ℕ∞) : left ≤ bound ↔ right ≤ bound :=
    ENat.recTopCoe (by simp) h bound
  exact le_antisymm ((hall right).mpr le_rfl) ((hall left).mp le_rfl)

theorem errorRank_eq_dependenceDepth (I : Instance) (later : List I.Stage) (past : Finset I.Stage) :
    errorRank I later past = dependenceDepth I later past := by
  apply enat_eq_of_le_nat_iff
  intro budget
  rw [rank_le_nat_iff_future_set, depth_le_nat_iff]

/-- The original fixed stage order, starting at the specified cursor. -/
def stagesFrom (I : Instance) (next : ℕ) : List I.Stage :=
  (List.finRange I.compatibility.length).drop next

theorem mem_stagesFrom (I : Instance) (next : ℕ) (i : I.Stage) :
    i ∈ stagesFrom I next ↔ next ≤ i.val := by
  unfold stagesFrom
  rw [List.mem_drop_iff_getElem]
  constructor
  · rintro ⟨j, _, hget⟩
    have hval := congrArg Fin.val hget
    simp only [List.getElem_finRange, Fin.val_cast] at hval
    omega
  · intro hle
    refine ⟨i.val - next, ?_, ?_⟩
    · simp only [List.length_finRange]
      omega
    · rw [List.getElem_finRange]
      apply Fin.ext
      simp only [Fin.val_cast]
      omega

theorem stagesFrom_toFinset (I : Instance) (next : ℕ) :
    (stagesFrom I next).toFinset = Finset.univ.filter (fun i : I.Stage => next ≤ i.val) := by
  ext i
  simp only [List.mem_toFinset, mem_stagesFrom, Finset.mem_filter, Finset.mem_univ, true_and]

theorem stagesFrom_cons (I : Instance) (i : I.Stage) :
    stagesFrom I i.val = i :: stagesFrom I (i.val + 1) := by
  have hi : i.val < (List.finRange I.compatibility.length).length := by
    simpa only [List.length_finRange] using i.isLt
  unfold stagesFrom
  rw [List.drop_eq_getElem_cons hi]
  congr 1
  rw [List.getElem_finRange]
  apply Fin.ext
  simp only [Fin.val_cast]

theorem girth_le_card_of_unmatchable {errors : Finset I.Stage}
    (hbad : ¬ Matchable I errors) : girth I ≤ (errors.card : ℕ∞) := by
  obtain ⟨circuit, hsub, hcircuit⟩ := exists_circuit_subset hbad
  exact (girth_le_card hcircuit).trans (ENat.natCast_le_natCast.mpr (Finset.card_le_card hsub))

theorem matchable_of_card_lt_girth {errors : Finset I.Stage}
    (hlt : (errors.card : ℕ∞) < girth I) : Matchable I errors := by
  by_contra hbad
  exact (not_le_of_gt hlt) (girth_le_card_of_unmatchable hbad)

theorem circuit_of_unmatchable_card_girth {errors : Finset I.Stage}
    (hbad : ¬ Matchable I errors) (hcard : (errors.card : ℕ∞) = girth I) : Circuit I errors := by
  refine ⟨hbad, ?_⟩
  intro smaller hproper
  apply matchable_of_card_lt_girth
  rw [← hcard]
  exact ENat.natCast_lt_natCast.mpr (Finset.card_lt_card hproper)

theorem girth_le_nat_iff (I : Instance) (budget : ℕ) :
    girth I ≤ (budget : ℕ∞) ↔ ∃ errors : Finset I.Stage,
      errors.card ≤ budget ∧ ¬ Matchable I errors := by
  constructor
  · intro hle
    have hfinite : girth I ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top budget) hle
    obtain ⟨errors, hcircuit, hgirth⟩ := minimum_circuit_exists I hfinite
    refine ⟨errors, ?_, hcircuit.1⟩
    apply ENat.natCast_le_natCast.mp
    rwa [← hgirth]
  · rintro ⟨errors, hcard, hbad⟩
    exact (girth_le_card_of_unmatchable hbad).trans (ENat.natCast_le_natCast.mpr hcard)

theorem initial_errorRank_eq_girth (I : Instance) : errorRank I (stagesFrom I 0) ∅ = girth I := by
  apply enat_eq_of_le_nat_iff
  intro budget
  rw [rank_le_nat_iff_future_set, girth_le_nat_iff]
  constructor
  · rintro ⟨errors, _, hcard, hbad⟩
    exact ⟨errors, hcard, by simpa only [Finset.empty_union] using hbad⟩
  · rintro ⟨errors, hcard, hbad⟩
    refine ⟨errors, ?_, hcard, by simpa only [Finset.empty_union] using hbad⟩
    intro i _
    rw [stagesFrom_toFinset]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, Nat.zero_le _⟩

theorem safe_bad_below_girth (I : Instance) (later : List I.Stage) (i : I.Stage)
    (depth : ℕ) (hdepth : girth I = (depth : ℕ∞)) (budget : ℕ) (hbudget : budget < depth - 1) :
    Safe I later {i} budget := by
  apply (safe_iff_future_sets I later {i} budget).mpr
  intro errors _ hcard
  apply matchable_of_card_lt_girth
  rw [hdepth]
  apply ENat.natCast_lt_natCast.mpr
  have hcount : ({i} ∪ errors).card ≤ errors.card + 1 := by
    simpa only [Finset.singleton_union] using Finset.card_insert_le i errors
  omega

/-- On the all-correct path the erroneous successor has depth g-1 exactly
at heads of size-g circuits, including g=1 (an already failed successor). -/
theorem bad_successor_rank_iff_girthHead (I : Instance) (i : I.Stage) (depth : ℕ)
    (hdepth : girth I = (depth : ℕ∞)) :
    errorRank I (stagesFrom I (i.val + 1)) {i} = ((depth - 1 : ℕ) : ℕ∞) ↔
      i ∈ girthHeads I := by
  have hpositive : 0 < depth := by
    have h := one_le_girth I
    rw [hdepth] at h
    exact ENat.natCast_le_natCast.mp h
  constructor
  · intro hrank
    have hle : errorRank I (stagesFrom I (i.val + 1)) {i} ≤ ((depth - 1 : ℕ) : ℕ∞) := hrank.le
    obtain ⟨errors, hfuture, hcard, hbad⟩ :=
      (rank_le_nat_iff_future_set I _ _ _).mp hle
    have hbad' : ¬ Matchable I (insert i errors) := by
      simpa only [Finset.singleton_union] using hbad
    have hupper : (insert i errors).card ≤ depth := by
      have h := Finset.card_insert_le i errors
      omega
    have hlower : depth ≤ (insert i errors).card := by
      have h := girth_le_card_of_unmatchable hbad'
      rw [hdepth] at h
      exact ENat.natCast_le_natCast.mp h
    have hsize : (insert i errors).card = depth := Nat.le_antisymm hupper hlower
    have hsize' : ((insert i errors).card : ℕ∞) = girth I := by rw [hsize, ← hdepth]
    have hcircuit := circuit_of_unmatchable_card_girth hbad' hsize'
    apply (mem_girthHeads I i).mpr
    refine ⟨insert i errors, ⟨hcircuit, by simp, ?_⟩, hsize'⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with hji | hmem
    · exact hji ▸ le_rfl
    · have hstage := (mem_stagesFrom I (i.val + 1) j).mp (List.mem_toFinset.mp (hfuture hmem))
      change i.val ≤ j.val
      omega
  · intro hhead
    obtain ⟨errors, ⟨hcircuit, hi, hfirst⟩, hsize⟩ := (mem_girthHeads I i).mp hhead
    have hsize' : errors.card = depth := by exact_mod_cast (hsize.trans hdepth)
    have hfuture : errors.erase i ⊆ (stagesFrom I (i.val + 1)).toFinset := by
      intro j hj
      have hmem := (Finset.mem_erase.mp hj).2
      have hne := (Finset.mem_erase.mp hj).1
      have hle : i.val ≤ j.val := hfirst j hmem
      have hneval : j.val ≠ i.val := fun heq => hne (Fin.ext heq)
      apply List.mem_toFinset.mpr
      apply (mem_stagesFrom I (i.val + 1) j).mpr
      omega
    have hbad : ¬ Matchable I ({i} ∪ errors.erase i) := by
      simpa only [Finset.singleton_union, Finset.insert_erase hi] using hcircuit.1
    have hcount : (errors.erase i).card ≤ depth - 1 := by
      simp only [Finset.card_erase_of_mem hi, hsize', le_refl]
    apply (rank_eq_nat_iff I _ _ (depth - 1)).mpr
    refine ⟨?_, fun smaller hsmall => safe_bad_below_girth I _ i depth hdepth smaller hsmall⟩
    exact (not_safe_iff_future_set I _ _ _).mpr ⟨errors.erase i, hfuture, hcount, hbad⟩

end PaperProofs.Retained
