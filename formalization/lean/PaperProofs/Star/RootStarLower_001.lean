module

public import PaperProofs.Star.Claims
public import PaperProofs.Star.RootStarRank_003
public import PaperProofs.Retained.RootRetainedHead_004
public import PaperProofs.Star.LateLower

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open Filter Asymptotics MeasureTheory
open scoped Topology ENNReal BigOperators

namespace RootStarLower

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star PaperProofs.Statistics

def KindLower (P : Parameters) (order : Order) (kind : PortKind) (epsilon : ℝ) : Prop :=
  ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ delta : ℝ, 0 < delta → delta < cutoff →
    ∀ C : Contract (starInstance P.tools order), kind.contracts C →
      ∀ accounting, ENNReal.ofReal ((1 - epsilon) * P.leadingScale order kind delta) ≤
        P.value order C .native accounting (ENNReal.ofReal delta)

theorem current_rank (P : Parameters) (order : Order) :
    PaperProofs.Structure.errorRank (starInstance P.tools order).compatibility
      (starInstance P.tools order).tools = (P.priceDepth order .current : ℕ∞) := by
  cases order with
  | universalFirst => exact RootStarRank.universalFirst_rank P.tools (by have := P.tools_ge_two; omega)
  | singletonsFirst => exact RootStarRank.singletonsFirst_rank P.tools

theorem current_coefficient (P : Parameters) (order : Order) :
    (P.input order).orderedCoefficient (starInstance P.tools order).tools = P.channel.a := by
  cases order with
  | universalFirst => exact RootStarRank.universalFirst_coefficient P
  | singletonsFirst => exact RootStarRank.singletonsFirst_coefficient P

theorem retained_coefficient (P : Parameters) (order : Order) :
    PaperProofs.Retained.headCoefficient (P.input order) = P.channel.a := by
  have hq : 0 < P.tools := by have := P.tools_ge_two; omega
  simp only [PaperProofs.Retained.headCoefficient, girthHeads_eq P.tools hq order,
    Finset.sum_singleton, Parameters.local_coefficient_eq]

theorem current_kind_lower (P : Parameters) (order : Order) (epsilon : ℝ) (he : 0 < epsilon) :
    KindLower P order .current epsilon := by
  have lower := (P.input order).nativeLowerPriceLaw_of_penaltyAsymptotics
    (P.input order).penaltyAsymptotics
  obtain ⟨cutoff, hc, hb⟩ := lower (P.priceDepth order .current) (current_rank P order) epsilon he
  refine ⟨cutoff, hc, ?_⟩
  intro delta hd hs C hC accounting
  simpa only [current_coefficient P order, Parameters.leadingScale, Parameters.value] using
    hb delta hd hs C hC accounting

theorem early_kind_lower (P : Parameters) (order : Order)
    (hrec : PaperProofs.Retained.FreshPenaltyRecursion (P.input order))
    (epsilon : ℝ) (he : 0 < epsilon) : KindLower P order .earlyRetained epsilon := by
  have hq : 0 < P.tools := by have := P.tools_ge_two; omega
  have lower := RootRetainedHead.nativeLowerPriceLaw_of_recursion (P.input order) hrec
  obtain ⟨cutoff, hc, hb⟩ := lower (P.tools + 1) (girth_eq P.tools hq order) epsilon he
  refine ⟨cutoff, hc, ?_⟩
  intro delta hd hs C hC accounting
  simpa only [retained_coefficient P order, Parameters.leadingScale, Parameters.priceDepth, Parameters.value, mul_assoc] using
    hb delta hd hs C hC accounting

end RootStarLower
