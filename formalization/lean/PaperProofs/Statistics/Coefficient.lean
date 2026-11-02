module

public import PaperProofs.Structure.Rank
public import PaperProofs.Common.Input
public import Mathlib.Data.List.OfFn

/-!
The ordered coefficient in eq:price-coefficient and its critical-head formula
in eq:price-head. The rank is always the independent allocation-game rank.
The coefficient is not a statistical value, an asymptotic theorem, or an exact
real-arithmetic oracle. Its weights are the symbolic local KL coefficients.

The common-input adapter at the end derives every weight and compatibility set
from one `Common.StatisticalInput`; it does not introduce a second experiment.
-/

@[expose] public section

namespace PaperProofs.Statistics

open PaperProofs.Structure

variable {Tool : Type*}

abbrev WeightedSchedule (Tool : Type*) := List (Finset Tool × ℝ)

def eligibilitySchedule (stages : WeightedSchedule Tool) : List (Finset Tool) :=
  stages.map Prod.fst

@[simp] theorem eligibilitySchedule_nil : eligibilitySchedule ([] : WeightedSchedule Tool) = [] := rfl

@[simp] theorem eligibilitySchedule_cons (eligible : Finset Tool) (weight : ℝ)
    (later : WeightedSchedule Tool) :
    eligibilitySchedule ((eligible, weight) :: later) = eligible :: eligibilitySchedule later := rfl

def PositiveWeights (stages : WeightedSchedule Tool) : Prop :=
  ∀ stage ∈ stages, 0 < stage.2

variable [DecidableEq Tool]

/-- The actual ordered recurrence from eq:price-coefficient. Both indicator
conditions compare integer game ranks, never real-valued weights. -/
noncomputable def orderedCoefficient : WeightedSchedule Tool → Finset Tool → ℝ
  | [], _ => 0
  | (eligible, weight) :: later, remaining =>
      if errorRank (eligible :: eligibilitySchedule later) remaining = ⊤ then 0 else
        (if errorRank (eligibilitySchedule later) remaining =
            errorRank (eligible :: eligibilitySchedule later) remaining then
          orderedCoefficient later remaining else 0) +
        (if badChildRank eligible (eligibilitySchedule later) remaining + 1 =
            errorRank (eligible :: eligibilitySchedule later) remaining then weight else 0)

@[simp] theorem orderedCoefficient_nil (remaining : Finset Tool) :
    orderedCoefficient ([] : WeightedSchedule Tool) remaining = 0 := rfl

theorem orderedCoefficient_of_infiniteRank (stages : WeightedSchedule Tool)
    (remaining : Finset Tool) (htop : errorRank (eligibilitySchedule stages) remaining = ⊤) :
    orderedCoefficient stages remaining = 0 := by
  cases stages with
  | nil => rfl
  | cons stage later =>
    rcases stage with ⟨eligible, weight⟩
    simp only [eligibilitySchedule_cons] at htop
    simp [orderedCoefficient, htop]

private theorem rank_eq_good_or_bad (eligible : Finset Tool)
    (later : List (Finset Tool)) (remaining : Finset Tool) :
    errorRank later remaining = errorRank (eligible :: later) remaining ∨
      badChildRank eligible later remaining + 1 =
        errorRank (eligible :: later) remaining := by
  rcases le_total (errorRank later remaining) (1 + badChildRank eligible later remaining)
    with hle | hle
  · exact Or.inl ((errorRank_cons eligible later remaining).trans (min_eq_left hle)).symm
  · exact Or.inr (by
      simpa only [add_comm] using
        ((errorRank_cons eligible later remaining).trans (min_eq_right hle)).symm)

/-- Finite semantic rank implies a strictly positive coefficient for the
paper's positive local weights. No unproved statistical theorem is assumed. -/
theorem orderedCoefficient_pos (stages : WeightedSchedule Tool) (remaining : Finset Tool)
    (hweights : PositiveWeights stages)
    (hfinite : errorRank (eligibilitySchedule stages) remaining ≠ ⊤) :
    0 < orderedCoefficient stages remaining := by
  revert hweights hfinite
  induction stages with
  | nil =>
    intro _ hfinite
    exact False.elim (hfinite (errorRank_terminal remaining))
  | cons stage later ih =>
    rcases stage with ⟨eligible, weight⟩
    intro hweights hfinite
    have hweight : 0 < weight := hweights (eligible, weight) (List.mem_cons_self)
    have htail : PositiveWeights later := by
      intro stage hstage
      exact hweights stage (List.mem_cons_of_mem _ hstage)
    simp only [eligibilitySchedule_cons] at hfinite
    simp only [orderedCoefficient]
    split_ifs with htop hgood hbad
    · exact False.elim (hfinite htop)
    · have htailFinite : errorRank (eligibilitySchedule later) remaining ≠ ⊤ := by
        rw [hgood]
        exact hfinite
      exact add_pos (ih htail htailFinite) hweight
    · have htailFinite : errorRank (eligibilitySchedule later) remaining ≠ ⊤ := by
        rw [hgood]
        exact hfinite
      simpa only [add_zero] using ih htail htailFinite
    · simpa only [zero_add] using hweight
    · rename_i hbad
      rcases rank_eq_good_or_bad eligible (eligibilitySchedule later) remaining with h | h
      · exact False.elim (hgood h)
      · exact False.elim (hbad h)

theorem orderedCoefficient_nonneg (stages : WeightedSchedule Tool) (remaining : Finset Tool)
    (hweights : PositiveWeights stages) : 0 ≤ orderedCoefficient stages remaining := by
  by_cases htop : errorRank (eligibilitySchedule stages) remaining = ⊤
  · rw [orderedCoefficient_of_infiniteRank stages remaining htop]
  · exact (orderedCoefficient_pos stages remaining hweights htop).le

/-- The sum of critical local weights along the all-correct path, with one
fixed initial rank and unchanged remaining tools. Every ordered stage is
visited once; a term is present exactly when its bad rank plus one is the
fixed target rank. This is the finite ordered sum in eq:price-head. -/
noncomputable def criticalHeadSum : WeightedSchedule Tool → Finset Tool → ℕ∞ → ℝ
  | [], _, _ => 0
  | (eligible, weight) :: later, remaining, target =>
      (if badChildRank eligible (eligibilitySchedule later) remaining + 1 = target then
        weight else 0) + criticalHeadSum later remaining target

/-- The implemented indicator `bad + 1 = initial rank` is exactly the printed
criterion `bad = d - 1` when the initial rank is the finite natural depth d.
Positivity of d follows from the independent game rank, including at boundaries. -/
theorem critical_head_criterion (stages : WeightedSchedule Tool)
    (remaining : Finset Tool) (depth : Nat)
    (hrank : errorRank (eligibilitySchedule stages) remaining = (depth : ℕ∞))
    (bad : ℕ∞) :
    bad + 1 = errorRank (eligibilitySchedule stages) remaining ↔
      bad = ((depth - 1 : Nat) : ℕ∞) := by
  have hpos := errorRank_pos (eligibilitySchedule stages) remaining
  rw [hrank] at hpos ⊢
  cases depth with
  | zero => exact False.elim ((lt_irrefl (0 : ℕ∞)) hpos)
  | succ depth =>
    change bad + 1 = ((depth + 1 : Nat) : ℕ∞) ↔ bad = (depth : ℕ∞)
    rw [ENat.natCast_add, ENat.natCast_one]
    constructor
    · intro h
      exact (ENat.add_left_injective_of_ne_top ENat.one_ne_top) h
    · intro h
      exact congrArg (fun value : ℕ∞ => value + 1) h

/-- Once the all-correct suffix rank exceeds the target, it can contribute
no further critical head at that target. -/
theorem criticalHeadSum_eq_zero_of_lt_rank (stages : WeightedSchedule Tool)
    (remaining : Finset Tool) (target : ℕ∞)
    (hlt : target < errorRank (eligibilitySchedule stages) remaining) :
    criticalHeadSum stages remaining target = 0 := by
  revert hlt
  induction stages with
  | nil => intro _; rfl
  | cons stage later ih =>
    rcases stage with ⟨eligible, weight⟩
    intro hlt
    simp only [eligibilitySchedule_cons] at hlt
    have hgood : target < errorRank (eligibilitySchedule later) remaining := by
      apply lt_of_lt_of_le hlt
      rw [errorRank_cons]
      exact min_le_left _ _
    have hbad : target < badChildRank eligible (eligibilitySchedule later) remaining + 1 := by
      apply lt_of_lt_of_le hlt
      rw [errorRank_cons, add_comm (badChildRank eligible (eligibilitySchedule later) remaining) 1]
      exact min_le_right _ _
    have hnot : badChildRank eligible (eligibilitySchedule later) remaining + 1 ≠ target :=
      ne_of_gt hbad
    simp [criticalHeadSum, hnot, ih hgood]

/-- The ordered critical-head formula in eq:price-head, proved from the
coefficient recurrence and semantic rank monotonicity along correct branches. -/
theorem orderedCoefficient_head_formula (stages : WeightedSchedule Tool)
    (remaining : Finset Tool)
    (hfinite : errorRank (eligibilitySchedule stages) remaining ≠ ⊤) :
    orderedCoefficient stages remaining =
      criticalHeadSum stages remaining (errorRank (eligibilitySchedule stages) remaining) := by
  revert hfinite
  induction stages with
  | nil =>
    intro hfinite
    exact False.elim (hfinite (errorRank_terminal remaining))
  | cons stage later ih =>
    rcases stage with ⟨eligible, weight⟩
    intro hfinite
    simp only [eligibilitySchedule_cons] at hfinite ⊢
    by_cases hgood : errorRank (eligibilitySchedule later) remaining =
        errorRank (eligible :: eligibilitySchedule later) remaining
    · have htailFinite : errorRank (eligibilitySchedule later) remaining ≠ ⊤ := by
        rw [hgood]
        exact hfinite
      have htail := ih htailFinite
      rw [hgood] at htail
      simp [orderedCoefficient, hfinite, hgood, criticalHeadSum, htail, add_comm]
    · have hlt : errorRank (eligible :: eligibilitySchedule later) remaining <
          errorRank (eligibilitySchedule later) remaining := by
        apply lt_of_le_of_ne
        · rw [errorRank_cons]
          exact min_le_left _ _
        · exact Ne.symm hgood
      have htail := criticalHeadSum_eq_zero_of_lt_rank later remaining
        (errorRank (eligible :: eligibilitySchedule later) remaining) hlt
      simp [orderedCoefficient, hfinite, hgood, criticalHeadSum, htail]

end PaperProofs.Statistics

namespace PaperProofs.Common

open PaperProofs.Statistics
open PaperProofs.Structure

/-- Stage weights and eligibility come from one input in its original order. -/
noncomputable def StatisticalInput.weightedSchedule {I : Instance}
    (input : StatisticalInput I) : WeightedSchedule I.Tool :=
  List.ofFn (fun i : I.Stage => (I.eligible i, (input.experiment i).coefficient))

theorem StatisticalInput.weightedSchedule_eligibility {I : Instance}
    (input : StatisticalInput I) :
    eligibilitySchedule input.weightedSchedule = I.compatibility := by
  unfold StatisticalInput.weightedSchedule eligibilitySchedule
  rw [List.map_ofFn]
  change List.ofFn I.compatibility.get = I.compatibility
  exact List.ofFn_get I.compatibility

theorem StatisticalInput.weightedSchedule_positive {I : Instance}
    (input : StatisticalInput I) : PositiveWeights input.weightedSchedule := by
  change ∀ stage ∈ List.ofFn (fun i : I.Stage =>
    (I.eligible i, (input.experiment i).coefficient)), 0 < stage.2
  exact List.forall_mem_ofFn_iff.mpr (fun i => (input.experiment i).coefficient_pos)

noncomputable def StatisticalInput.orderedCoefficient {I : Instance}
    (input : StatisticalInput I) (remaining : Finset I.Tool) : ℝ :=
  Statistics.orderedCoefficient input.weightedSchedule remaining

theorem StatisticalInput.orderedCoefficient_pos {I : Instance}
    (input : StatisticalInput I) (remaining : Finset I.Tool)
    (hfinite : errorRank I.compatibility remaining ≠ ⊤) :
    0 < input.orderedCoefficient remaining := by
  apply Statistics.orderedCoefficient_pos _ _ input.weightedSchedule_positive
  simpa only [input.weightedSchedule_eligibility] using hfinite

theorem StatisticalInput.orderedCoefficient_head_formula {I : Instance}
    (input : StatisticalInput I) (remaining : Finset I.Tool)
    (hfinite : errorRank I.compatibility remaining ≠ ⊤) :
    input.orderedCoefficient remaining =
      criticalHeadSum input.weightedSchedule remaining (errorRank I.compatibility remaining) := by
  have hfinite' : errorRank (eligibilitySchedule input.weightedSchedule) remaining ≠ ⊤ := by
    simpa only [input.weightedSchedule_eligibility] using hfinite
  simpa only [StatisticalInput.orderedCoefficient, input.weightedSchedule_eligibility] using
    Statistics.orderedCoefficient_head_formula input.weightedSchedule remaining hfinite'

end PaperProofs.Common
