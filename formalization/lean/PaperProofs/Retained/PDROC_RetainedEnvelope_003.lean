module

public import PaperProofs.Retained.PDROC_RetainedEnvelope_002
public import PaperProofs.Retained.RootRetainedQueries_001
public import PaperProofs.Retained.RootRetainedAsymp_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PaperProofs.Retained.PRetObservationEnvelope119

open Common Common.Native Statistics MeasureTheory Filter
open scoped ENNReal Topology
open RootRetainedQueries RootRetainedAsymp

variable {I : Instance}

theorem observationEnvelope_zero_of_rank_top (input : StatisticalInput I) (next : ℕ)
    (old : Finset I.Stage) (risk : ℚ)
    (ht : errorRank I (stagesFrom I next) old = ⊤) :
    observationEnvelope input next old risk = 0 := by
  by_cases hn : next < I.stageCount
  · let stage : I.Stage := ⟨next, hn⟩
    have hq : rankIndex I next old = none := (rankQueryCorrect I next old).1.mpr ht
    have hc : rankCase I stage old = some .infiniteRank := by
      simp only [rankCase, stage, hq]
    change observationEnvelope input stage.val old risk = 0
    rw [observationEnvelope_step, hc]
  · exact observationEnvelope_past_end input next old risk (Nat.le_of_not_gt hn)

theorem finite_rank_cases (stage : I.Stage) (old : Finset I.Stage)
    (hh : Healthy I stage.val old) (depth : ℕ)
    (hr : errorRank I (stagesFrom I stage.val) old = (depth : ℕ∞)) :
    (rankCase I stage old = some .noTool ∧ depth = 1) ∨
      ∃ j : ℕ+, rankCase I stage old = some (.finiteBad j) ∧
        Healthy I (stage.val + 1) (insert stage old) ∧
        errorRank I (stagesFrom I (stage.val + 1)) (insert stage old) = (j.val : ℕ∞) ∧
        depth ≤ j.val + 1 := by
  classical
  have hp : rankIndex I stage.val old = some depth := (rankQueryCorrect I stage.val old).2 depth |>.mpr hr
  by_cases hm : Matchable I (insert stage old)
  · have hfinite : errorRank I (stagesFrom I (stage.val + 1)) (insert stage old) ≠ ⊤ :=
      ne_top_of_le_ne_top (by rw [hr]; exact ENat.natCast_ne_top depth) (rank_bad_le_current stage old hh)
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hfinite
    have hjpos : 0 < j := by
      have hpos := rank_positive (stagesFrom I (stage.val + 1)) (insert stage old) hm
      rw [← hj] at hpos
      exact_mod_cast hpos
    have hq : rankIndex I (stage.val + 1) (insert stage old) = some j :=
      (rankQueryCorrect I (stage.val + 1) (insert stage old)).2 j |>.mpr hj.symm
    have hc : rankCase I stage old = some (.finiteBad ⟨j, hjpos⟩) := by
      simp only [rankCase, hp, ite_eq_right (not_not.mpr hm), hq, dite_eq_left hjpos]
    have horder : depth ≤ j + 1 := by
      have hle : (depth : ℕ∞) ≤ 1 + (j : ℕ∞) := by
        rw [← hr, rank_suffix_step stage old hh, ← hj]
        exact min_le_right _ _
      exact ENat.natCast_le_natCast.mp (by
        simpa only [ENat.natCast_add, ENat.natCast_one, add_comm] using hle)
    exact Or.inr ⟨⟨j, hjpos⟩, hc, (healthy_error_iff I stage old hh).mpr hm, hj.symm, horder⟩
  · have hc : rankCase I stage old = some .noTool := by
      unfold rankCase
      rw [hp, ite_eq_left hm]
    have hzero := rank_zero_of_unmatchable (stagesFrom I (stage.val + 1)) (insert stage old) hm
    have hle : (depth : ℕ∞) ≤ (1 : ℕ∞) := by
      rw [← hr, rank_suffix_step stage old hh, hzero, add_zero]
      exact min_le_right _ _
    have hle' : depth ≤ 1 := ENat.natCast_le_natCast.mp hle
    have hpos : 0 < depth := by
      have h := rank_positive (stagesFrom I stage.val) old hh.2.2
      rw [hr] at h
      exact_mod_cast h
    exact Or.inl ⟨hc, by omega⟩

theorem rank_le_good (stage : I.Stage) (old : Finset I.Stage) (hh : Healthy I stage.val old) :
    errorRank I (stagesFrom I stage.val) old ≤ errorRank I (stagesFrom I (stage.val + 1)) old := by
  rw [rank_suffix_step stage old hh]
  exact min_le_left _ _

theorem observationEnvelopeReal_noTool (input : StatisticalInput I) (stage : I.Stage)
    (old : Finset I.Stage) (risk : ℚ) (hv : ReferenceBudgetValid risk)
    (hc : rankCase I stage old = some .noTool) :
    observationEnvelopeReal input stage.val old risk =
      (localObservationPrice input stage .noTool risk).toReal +
        observationEnvelopeReal input (stage.val + 1) old (risk / 2) := by
  have hh : ReferenceBudgetValid (risk / 2) := ⟨by linarith [hv.1], by linarith [hv.2]⟩
  unfold observationEnvelopeReal
  rw [observationEnvelope_step, hc]
  exact ENNReal.toReal_add (localObservationPrice_ne_top input stage .noTool risk hv)
    (observationEnvelope_ne_top input _ old _ hh)

theorem observationEnvelopeReal_finiteBad (input : StatisticalInput I) (stage : I.Stage)
    (old : Finset I.Stage) (risk : ℚ) (hv : ReferenceBudgetValid risk) (j : ℕ+)
    (hc : rankCase I stage old = some (.finiteBad j)) :
    observationEnvelopeReal input stage.val old risk =
      (localObservationPrice input stage (.finiteBad j) risk).toReal +
        observationEnvelopeReal input (stage.val + 1) old (risk / 2) +
        (controllerTarget risk j.val : ℝ) * observationEnvelopeReal input (stage.val + 1) (insert stage old)
          (controllerBadRisk risk (controllerTarget risk j.val)) := by
  have hh : ReferenceBudgetValid (risk / 2) := ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hb : ReferenceBudgetValid (controllerBadRisk risk (controllerTarget risk j.val)) :=
    ⟨controllerBadRisk_positive risk _ hv.1 hv.2
      (controllerTarget_pos risk j.val) (controllerTarget_le_quarter risk j.val),
      (controllerBadRisk_bounds risk _ hv.1 hv.2
        (controllerTarget_pos risk j.val) (controllerTarget_le_quarter risk j.val)).2⟩
  have hq : 0 ≤ (controllerTarget risk j.val : ℝ) := by exact_mod_cast (controllerTarget_pos risk j.val).le
  unfold observationEnvelopeReal
  rw [observationEnvelope_step, hc,
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr
      ⟨localObservationPrice_ne_top input stage (.finiteBad j) risk hv,
        observationEnvelope_ne_top input _ old _ hh⟩)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (observationEnvelope_ne_top input _ _ _ hb)),
    ENNReal.toReal_add (localObservationPrice_ne_top input stage (.finiteBad j) risk hv)
      (observationEnvelope_ne_top input _ old _ hh),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hq]

end PaperProofs.Retained.PRetObservationEnvelope119
