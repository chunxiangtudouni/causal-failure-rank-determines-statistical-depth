module

public import PaperProofs.Retained.PRet_ObservationEnvelope_119
public import PaperProofs.Statistics.IteratedLogComparison

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PaperProofs.Retained.PRetObservationEnvelope119

open Common Common.Native Statistics MeasureTheory
open scoped ENNReal

variable {I : Instance}

noncomputable def localPriceOffset (input : StatisticalInput I) (stage : I.Stage) : ℝ :=
  (input.experiment stage).logIncrementBound true +
    2 * |Real.log ((input.experiment stage).priorReal true / (input.experiment stage).priorReal false)|

theorem localObservationPrice_le_sharp (input : StatisticalInput I) (stage : I.Stage)
    (kind : ReferenceBudgetCase) (risk target : ℚ) (hv : ReferenceBudgetValid risk)
    (ht : referenceBudgetTarget kind risk = some target) :
    localObservationPrice input stage kind risk ≤
      ENNReal.ofReal ((input.experiment stage).coefficient *
        (Real.log (1 / (target : ℝ)) + localPriceOffset input stage)) := by
  let E := input.experiment stage
  have hp := referenceBudgetTarget_valid_floor kind risk target hv ht
  have hpR : 0 < (target : ℝ) := by exact_mod_cast hp.1
  have hpone : (target : ℝ) ≤ 1 := by
    exact_mod_cast hp.2.1.trans (by norm_num : (1 / 4 : ℚ) ≤ 1)
  have hlog : 0 ≤ Real.log (1 / (target : ℝ)) :=
    Real.log_nonneg ((le_div_iff₀ hpR).mpr (by simpa only [one_mul] using hpone))
  have hB : 0 ≤ Real.log (1 / (target : ℝ)) + localPriceOffset input stage := by
    have hK := E.logIncrementBound_nonneg true
    dsimp only [localPriceOffset]
    positivity
  have hb := E.bayesObservationCharge_le_drift_bound (Measure.dirac ()) (E.posteriorSPRT target)
    _ hB (E.posteriorSPRT_expectedObservationCharge_finite target
      (BinaryExperiment.posteriorThreshold_nonneg target hp.1 hp.2.1))
    (fun truth => by simpa only [localPriceOffset, E] using
      E.posteriorSPRT_sharpObservationCharge target hp.1 hp.2.1 truth)
  simpa only [localObservationPrice, ht] using hb

theorem localObservationPrice_ne_top (input : StatisticalInput I) (stage : I.Stage)
    (kind : ReferenceBudgetCase) (risk : ℚ) (hv : ReferenceBudgetValid risk) :
    localObservationPrice input stage kind risk ≠ ⊤ := by
  cases ht : referenceBudgetTarget kind risk with
  | none => simp only [localObservationPrice, ht, ne_eq, ENNReal.zero_ne_top, not_false_eq_true]
  | some target =>
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (localObservationPrice_le_sharp input stage kind risk target hv ht)

theorem observationEnvelopeAux_ne_top (input : StatisticalInput I) (fuel next : ℕ)
    (old : Finset I.Stage) (risk : ℚ) (hv : ReferenceBudgetValid risk) :
    observationEnvelopeAux input fuel next old risk ≠ ⊤ := by
  induction fuel generalizing next old risk with
  | zero => simp only [observationEnvelopeAux, ne_eq, ENNReal.zero_ne_top, not_false_eq_true]
  | succ fuel ih =>
    have hh : ReferenceBudgetValid (risk / 2) := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    rw [observationEnvelopeAux]
    split_ifs with hn
    · dsimp only
      cases hc : rankCase I ⟨next, hn⟩ old with
      | none => simpa only [hc] using ENNReal.zero_ne_top
      | some kind =>
        cases kind with
        | infiniteRank => simpa only [hc] using ENNReal.zero_ne_top
        | noTool =>
          exact ENNReal.add_ne_top.mpr ⟨localObservationPrice_ne_top input _ _ risk hv,
            ih (next + 1) old (risk / 2) hh⟩
        | finiteBad depth =>
          have hb : ReferenceBudgetValid (controllerBadRisk risk (controllerTarget risk depth.val)) :=
            ⟨controllerBadRisk_positive risk _ hv.1 hv.2
              (controllerTarget_pos risk depth.val) (controllerTarget_le_quarter risk depth.val),
              (controllerBadRisk_bounds risk _ hv.1 hv.2
                (controllerTarget_pos risk depth.val) (controllerTarget_le_quarter risk depth.val)).2⟩
          exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
            ⟨localObservationPrice_ne_top input _ _ risk hv, ih (next + 1) old (risk / 2) hh⟩,
            ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ih (next + 1) _ _ hb)⟩
    · exact ENNReal.zero_ne_top

theorem observationEnvelope_ne_top (input : StatisticalInput I) (next : ℕ)
    (old : Finset I.Stage) (risk : ℚ) (hv : ReferenceBudgetValid risk) :
    observationEnvelope input next old risk ≠ ⊤ :=
  observationEnvelopeAux_ne_top input _ next old risk hv

/-- Faithful real coordinates for the unchanged finite numerical envelope.
Finiteness is proved above before these coordinates are used. -/
noncomputable def observationEnvelopeReal (input : StatisticalInput I) (next : ℕ)
    (old : Finset I.Stage) (risk : ℚ) : ℝ :=
  (observationEnvelope input next old risk).toReal

theorem observationEnvelopeReal_nonneg (input : StatisticalInput I) (next : ℕ)
    (old : Finset I.Stage) (risk : ℚ) : 0 ≤ observationEnvelopeReal input next old risk :=
  ENNReal.toReal_nonneg

theorem ofReal_observationEnvelopeReal (input : StatisticalInput I) (next : ℕ)
    (old : Finset I.Stage) (risk : ℚ) (hv : ReferenceBudgetValid risk) :
    ENNReal.ofReal (observationEnvelopeReal input next old risk) =
      observationEnvelope input next old risk :=
  ENNReal.ofReal_toReal (observationEnvelope_ne_top input next old risk hv)

theorem observationEnvelope_step (input : StatisticalInput I) (stage : I.Stage)
    (old : Finset I.Stage) (risk : ℚ) :
    observationEnvelope input stage.val old risk =
      match rankCase I stage old with
      | none => 0
      | some .infiniteRank => 0
      | some .noTool => localObservationPrice input stage .noTool risk +
          observationEnvelope input (stage.val + 1) old (risk / 2)
      | some (.finiteBad depth) =>
          localObservationPrice input stage (.finiteBad depth) risk +
            observationEnvelope input (stage.val + 1) old (risk / 2) +
            ENNReal.ofReal (controllerTarget risk depth.val : ℝ) *
              observationEnvelope input (stage.val + 1) (insert stage old)
                (controllerBadRisk risk (controllerTarget risk depth.val)) := by
  have hf : I.stageCount - stage.val = (I.stageCount - (stage.val + 1)) + 1 := by
    have hs : stage.val < I.stageCount := stage.isLt
    omega
  have hs : stage.val < I.stageCount := stage.isLt
  unfold observationEnvelope
  rw [hf, observationEnvelopeAux, dite_eq_left hs]
  rfl

theorem observationEnvelope_past_end (input : StatisticalInput I) (next : ℕ)
    (old : Finset I.Stage) (risk : ℚ) (hn : I.stageCount ≤ next) :
    observationEnvelope input next old risk = 0 := by
  simp only [observationEnvelope, Nat.sub_eq_zero_of_le hn, observationEnvelopeAux]

end PaperProofs.Retained.PRetObservationEnvelope119
