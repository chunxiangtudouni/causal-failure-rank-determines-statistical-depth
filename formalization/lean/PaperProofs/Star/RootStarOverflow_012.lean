module

public import PaperProofs.Star.RootStarOverflow_011
public import PaperProofs.Star.RootStarOverflow_009

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace RootStarOverflow

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star PaperProofs.Star.Parameters

theorem run_eq_outside_overflow (P : Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (quota : ℕ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order)) (sample : Unit × (P.input order).World)
    (hidentify : ∀ n stage,
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample n).halted = false →
      P.starReferenceRule order kind r none ()
        (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample n).history = .review stage →
      quota ≤ (historyObservations
        (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample n).history stage).length →
      sample ∈ P.anyStarOverflow order kind r quota C accounting)
    (hno : sample ∉ P.anyStarOverflow order kind r quota C accounting) :
    ∀ n, run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r (some quota)) sample n =
      run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hh : (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample n).halted = true
    · have hhb : (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r (some quota)) sample n).halted = true := by rw [ih]; exact hh
      rw [run_succ_of_halted (P.input order) C .uncapped accounting _ sample n hhb,
        run_succ_of_halted (P.input order) C .uncapped accounting _ sample n hh, ih]
    · have ha : (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample n).halted = false := Bool.eq_false_iff.mpr hh
      rcases starRule_quota_exhausted P order kind r quota sample.1
          (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample n).history with hs | ⟨stage, hi, hq, _⟩
      · simp only [run]
        rw [ih, hs]
      · exact (hno (hidentify n stage ha hi hq)).elim

theorem risk_le_ideal_add_overflow (P : Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (quota : ℕ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order))
    (hidentify : ∀ (sample : Unit × (P.input order).World) n stage,
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample n).halted = false →
      P.starReferenceRule order kind r none ()
        (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample n).history = .review stage →
      quota ≤ (historyObservations
        (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample n).history stage).length →
      sample ∈ P.anyStarOverflow order kind r quota C accounting) :
    risk (P.input order) C .uncapped accounting (P.starReferenceRule order kind r (some quota)) (Measure.dirac ()) ≤
      risk (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) (Measure.dirac ()) +
        (P.input order).seededWorldLaw (Measure.dirac ()) (P.anyStarOverflow order kind r quota C accounting) := by
  have hsub : {sample | ¬ runSuccess (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r (some quota)) sample} ⊆
      {sample | ¬ runSuccess (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample} ∪
        P.anyStarOverflow order kind r quota C accounting := by
    intro sample hfailure
    by_cases ho : sample ∈ P.anyStarOverflow order kind r quota C accounting
    · exact Or.inr ho
    · refine Or.inl ?_
      rintro ⟨n, hh, hs⟩
      apply hfailure
      have heq := run_eq_outside_overflow P order kind r quota C accounting sample (hidentify sample) ho n
      exact ⟨n, by rw [heq]; exact hh, by rw [heq]; exact hs⟩
  exact (measure_mono hsub).trans (measure_union_le _ _)

theorem starOverflowAssembly_of_identification (P : Parameters)
    (hidentify : ∀ (order : Order) (kind : PortKind) (C : Contract (starInstance P.tools order)), kind.contracts C →
      ∀ (accounting : NormalAccounting (starInstance P.tools order)) (r : ℝ), 0 < r → r ≤ 1 / 4 →
        ∀ (quota : ℕ) (sample : Unit × (P.input order).World) n stage,
          (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample n).halted = false →
          P.starReferenceRule order kind r none ()
            (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample n).history = .review stage →
          quota ≤ (historyObservations
            (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample n).history stage).length →
          sample ∈ P.anyStarOverflow order kind r quota C accounting) : P.StarOverflowAssembly := by
  intro order kind C hC accounting delta exponent hd hq he
  refine ⟨reviewQuotaCertificate P order kind (delta / 2) (P.commonQuota exponent) C hC accounting,
    referenceAllPathCharges P order kind (delta / 2) (some (P.commonQuota exponent)) C hC accounting,
    anyStarOverflow_le P order kind C hC accounting delta exponent hd hq he, ?_⟩
  exact risk_le_ideal_add_overflow P order kind (delta / 2) (P.commonQuota exponent) C accounting
    (hidentify order kind C hC accounting (delta / 2) (by linarith) (by linarith) (P.commonQuota exponent))

end RootStarOverflow
