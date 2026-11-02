module

public import PaperProofs.Paid.PDROC_EndpointWalk_001
public import PaperProofs.Paid.CalibratedBackend
public import PaperProofs.Paid.PDMenu_FiniteMenu_003
public import PaperProofs.Statistics.SPRTOverflow
public import PaperProofs.Statistics.BSCStoppedPosterior
public import PaperProofs.Statistics.PDROC_Mixture_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal
open PaperProofs.Statistics PaperProofs.Paid

namespace PDROC

-- Initial unchanged body from Paid.PDROC_EndpointWalk_002

/-- The absorbing process equals the original signed tape walk stopped
at min(T_level,n), pointwise even when T_level is infinite. -/
theorem endpointWalkState_eq_stopped_signed (B : BinarySymmetric.Parameters)
    (level : ℕ) (hlevel : 1 ≤ level) (tape : B.experiment.Tape) (n : ℕ) :
    ((endpointWalkState level tape n).val : ℤ) = (level : ℤ) +
      B.signedSum tape (min (B.experiment.posteriorThresholdStop (B.endpointError level) tape)
        (n : ℕ∞)).toNat := by
  let T := B.experiment.posteriorThresholdStop (B.endpointError level) tape
  change ((endpointWalkState level tape n).val : ℤ) =
    (level : ℤ) + B.signedSum tape (min T (n : ℕ∞)).toNat
  induction n with
  | zero =>
    change (level : ℤ) = (level : ℤ) + B.signedSum tape (min T (0 : ℕ∞)).toNat
    simp
  | succ n ih =>
    by_cases hhit : T ≤ (n : ℕ∞)
    · have hfinite : T ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hhit
      have hcast := ENat.natCast_toNat_eq_self.mpr hfinite
      have hsum := B.symmetricHittingTest_hits_exact level hlevel tape T.toNat hcast.symm
      have ih' : ((endpointWalkState level tape n).val : ℤ) =
          (level : ℤ) + B.signedSum tape T.toNat := by
        simpa only [min_eq_left hhit] using ih
      have hboundary : (endpointWalkState level tape n).val = 0 ∨
          (endpointWalkState level tape n).val = 2 * level := by
        rcases Int.natAbs_eq_iff.mp hsum with hpos | hneg
        · right
          omega
        · left
          omega
      have hnext : T ≤ ((n + 1 : ℕ) : ℕ∞) :=
        hhit.trans (by exact_mod_cast Nat.le_succ n)
      rw [endpointWalkState_succ_of_boundary level tape n hboundary, min_eq_left hnext]
      exact ih'
    · have hbefore : (n : ℕ∞) < T := lt_of_not_ge hhit
      have hmin : min T (n : ℕ∞) = (n : ℕ∞) := min_eq_right hbefore.le
      have hnext : ((n + 1 : ℕ) : ℕ∞) ≤ T := by
        simpa only [Nat.cast_add, Nat.cast_one] using ENat.natCast_add_one_le_iff.mpr hbefore
      have ih' : ((endpointWalkState level tape n).val : ℤ) =
          (level : ℤ) + B.signedSum tape n := by
        simpa only [hmin, ENat.toNat_natCast] using ih
      have hsmall : (B.signedSum tape n).natAbs < level := by
        apply Nat.lt_of_not_ge
        intro h
        have hle := (B.symmetricHittingTest_stop_le_iff level tape n).mpr ⟨n, le_rfl, h⟩
        exact (not_le_of_gt hbefore) hle
      have habs : |B.signedSum tape n| < (level : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast hsmall
      have hsides := abs_lt.mp habs
      have hzero : (endpointWalkState level tape n).val ≠ 0 := by omega
      have htop : (endpointWalkState level tape n).val ≠ 2 * level := by omega
      rw [endpointWalkState_succ_val_of_interior level tape n hzero htop,
        min_eq_right hnext, ENat.toNat_natCast, B.signedSum_succ, ih']
      ring

theorem endpointWalkState_capped_score (P : Parameters) (m : ℕ)
    (tape : P.binarySymmetric.experiment.Tape) :
    P.binarySymmetric.experiment.logOddsScore tape (P.cappedStop m tape).toNat =
      P.binarySymmetric.h *
        (((endpointWalkState (m + 1) tape P.certificate.Q).val : ℝ) - ((m + 1 : ℕ) : ℝ)) := by
  rw [P.binarySymmetric.logOddsScore_eq_signed]
  have h := endpointWalkState_eq_stopped_signed P.binarySymmetric (m + 1) (by omega) tape P.certificate.Q
  have hi : P.binarySymmetric.signedSum tape (P.cappedStop m tape).toNat =
      ((endpointWalkState (m + 1) tape P.certificate.Q).val : ℤ) - ((m + 1 : ℕ) : ℤ) := by
    change P.binarySymmetric.signedSum tape (min
      (P.binarySymmetric.experiment.posteriorThresholdStop (P.binarySymmetric.endpointError (m + 1)) tape)
      (P.certificate.Q : ℕ∞)).toNat = _
    linarith only [h]
  have hr : (P.binarySymmetric.signedSum tape (P.cappedStop m tape).toNat : ℝ) =
      ((endpointWalkState (m + 1) tape P.certificate.Q).val : ℝ) - ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast hi
  rw [hr]

/-- Terminal state loss is exactly the original MAP decision with its
original independent fair terminal tie. -/
theorem endpointWalkState_capped_decision (P : Parameters) (m : ℕ)
    (tie : Bool) (tape : P.binarySymmetric.experiment.Tape) :
    (P.cappedTest m).rule.decision tie tape =
      if (endpointWalkState (m + 1) tape P.certificate.Q).val = m + 1 then tie
      else decide (m + 1 ≤ (endpointWalkState (m + 1) tape P.certificate.Q).val) := by
  have hscore := endpointWalkState_capped_score P m tape
  have hh := P.binarySymmetric.h_pos
  have hzero : P.binarySymmetric.experiment.logOddsScore tape (P.cappedStop m tape).toNat = 0 ↔
      (endpointWalkState (m + 1) tape P.certificate.Q).val = m + 1 := by
    rw [hscore]
    constructor
    · intro h
      have hr : ((endpointWalkState (m + 1) tape P.certificate.Q).val : ℝ) = ((m + 1 : ℕ) : ℝ) := by
        exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hh.ne')
      exact_mod_cast hr
    · intro h
      rw [h, sub_self, mul_zero]
  have hsign : 0 ≤ P.binarySymmetric.experiment.logOddsScore tape (P.cappedStop m tape).toNat ↔
      m + 1 ≤ (endpointWalkState (m + 1) tape P.certificate.Q).val := by
    rw [hscore]
    constructor
    · intro h
      have hr : ((m + 1 : ℕ) : ℝ) ≤ ((endpointWalkState (m + 1) tape P.certificate.Q).val : ℝ) := by
        exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hh).mp h)
      exact_mod_cast hr
    · intro h
      have hr : ((m + 1 : ℕ) : ℝ) ≤ ((endpointWalkState (m + 1) tape P.certificate.Q).val : ℝ) := by
        exact_mod_cast h
      exact mul_nonneg hh.le (sub_nonneg.mpr hr)
  change (if P.binarySymmetric.experiment.logOddsScore tape (P.cappedStop m tape).toNat = 0 then tie
    else decide (0 ≤ P.binarySymmetric.experiment.logOddsScore tape (P.cappedStop m tape).toNat)) = _
  simp only [hzero, hsign]


-- Initial unchanged body from Paid.PDROC_EndpointWalk_003

def endpointWalkMirror (level : ℕ) (state : PaperProofs.Paid.Parameters.WalkCell level) :
    PaperProofs.Paid.Parameters.WalkCell level := ⟨2 * level - state.val, by omega⟩

def endpointWalkFlipLetter (letter : Fin 2) : Fin 2 := ⟨1 - letter.val, by omega⟩

@[simp] theorem endpointWalkMirror_involutive (level : ℕ)
    (state : PaperProofs.Paid.Parameters.WalkCell level) :
    endpointWalkMirror level (endpointWalkMirror level state) = state := by
  apply Fin.ext
  simp only [endpointWalkMirror]
  omega

@[simp] theorem endpointWalkFlipLetter_involutive (letter : Fin 2) :
    endpointWalkFlipLetter (endpointWalkFlipLetter letter) = letter := by
  apply Fin.ext
  simp only [endpointWalkFlipLetter]
  omega

private theorem endpointWalkMove_val (level : ℕ)
    (state : PaperProofs.Paid.Parameters.WalkCell level) (letter : Fin 2) :
    (PaperProofs.Paid.Parameters.walkMove level state letter).val =
      if state.val = 0 ∨ state.val = 2 * level then state.val
      else if letter.val = 1 then state.val + 1 else state.val - 1 := by
  unfold PaperProofs.Paid.Parameters.walkMove
  split_ifs <;> rfl

theorem endpointWalkMove_mirror (level : ℕ)
    (state : PaperProofs.Paid.Parameters.WalkCell level) (letter : Fin 2) :
    PaperProofs.Paid.Parameters.walkMove level (endpointWalkMirror level state)
        (endpointWalkFlipLetter letter) =
      endpointWalkMirror level (PaperProofs.Paid.Parameters.walkMove level state letter) := by
  apply Fin.ext
  change (PaperProofs.Paid.Parameters.walkMove level (endpointWalkMirror level state)
    (endpointWalkFlipLetter letter)).val =
      2 * level - (PaperProofs.Paid.Parameters.walkMove level state letter).val
  rw [endpointWalkMove_val, endpointWalkMove_val]
  change (if 2 * level - state.val = 0 ∨ 2 * level - state.val = 2 * level then 2 * level - state.val
    else if 1 - letter.val = 1 then (2 * level - state.val) + 1 else (2 * level - state.val) - 1) =
      2 * level - (if state.val = 0 ∨ state.val = 2 * level then state.val
        else if letter.val = 1 then state.val + 1 else state.val - 1)
  have hs := state.isLt
  have hy := letter.isLt
  split_ifs <;> omega

theorem endpointWalkFlipLetter_channel (B : BinarySymmetric.Parameters) (truth : Bool) (letter : Fin 2) :
    B.experiment.channel (!truth) (endpointWalkFlipLetter letter) =
      B.experiment.channel truth letter := by
  cases truth <;> fin_cases letter <;>
    simp [BinarySymmetric.Parameters.channel_formula, endpointWalkFlipLetter]

theorem endpointWalkState_mirror (level : ℕ) (tape : ℕ → Fin 2) (n : ℕ) :
    endpointWalkState level (fun k => endpointWalkFlipLetter (tape k)) n =
      endpointWalkMirror level (endpointWalkState level tape n) := by
  induction n with
  | zero =>
    apply Fin.ext
    simp only [endpointWalkState, endpointWalkMirror]
    omega
  | succ n ih =>
    rw [endpointWalkState_succ, endpointWalkState_succ, ih, endpointWalkMove_mirror]


-- Initial unchanged body from Paid.PDROC_EndpointBounds_001

/-- The original menu ceil, with no enlargement of Q. -/
theorem endpointCap_menu_drift (P : Parameters) :
    (P.certificate.M : ℚ) + 1 ≤ P.certificate.gamma * P.certificate.Q := by
  have hceil : ((P.certificate.M : ℚ) + 1) / P.certificate.gamma ≤
      (P.certificate.Q : ℚ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast P.Q_ge_menu_ceil)
  simpa only [mul_comm] using (div_le_iff₀ P.certificate.gamma_pos).mp hceil

/-- The original tail ceil gives the exponent actually used in D23. -/
theorem endpointCap_tail_exponent (P : Parameters) :
    (P.certificate.E : ℝ) ≤ (P.certificate.gamma : ℝ) ^ 2 * P.certificate.Q / 2 := by
  have hceil : (2 * (P.certificate.E : ℚ)) / P.certificate.gamma ^ 2 ≤
      (P.certificate.Q : ℚ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast P.Q_ge_tail_ceil)
  have hmul := (div_le_iff₀ (sq_pos_of_pos P.certificate.gamma_pos)).mp hceil
  have hr : 2 * (P.certificate.E : ℝ) ≤
      (P.certificate.Q : ℝ) * (P.certificate.gamma : ℝ) ^ 2 := by exact_mod_cast hmul
  nlinarith

theorem endpointCap_exp_le_exp (P : Parameters) :
    Real.exp (-(P.certificate.gamma : ℝ) ^ 2 * P.certificate.Q / 2) ≤
      Real.exp (-(P.certificate.E : ℝ)) := by
  apply Real.exp_le_exp.mpr
  linarith [endpointCap_tail_exponent P]

theorem endpointCap_exp_le_binary (P : Parameters) :
    Real.exp (-(P.certificate.E : ℝ)) ≤ (1 / 2 : ℝ) ^ P.certificate.E := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hbase : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) htwo
  calc
    Real.exp (-(P.certificate.E : ℝ)) = Real.exp (-1) ^ P.certificate.E := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ (1 / 2 : ℝ) ^ P.certificate.E :=
      pow_le_pow_left₀ (Real.exp_nonneg _) hbase _

theorem endpointCap_binary_le_target (P : Parameters) :
    (1 / 2 : ℚ) ^ P.certificate.E ≤ P.certificate.gamma * P.certificate.epsilon :=
  P.certificate.E_spec.2

/-- The logistic contraction holds for every index, including zero. -/
theorem endpointError_succ_contract (P : BinarySymmetric.Parameters) (m : ℕ) :
    P.endpointError (m + 1) ≤ (1 - 2 * P.gamma) * P.endpointError m := by
  have hp : 1 ≤ P.odds ^ m := one_le_pow₀ P.odds_gt_one.le
  have hpos : 0 < 1 - 2 * P.gamma := by linarith [P.gamma_le_quarter]
  have hprev : 0 < 1 + P.odds ^ m := by positivity
  have hnext : 0 < 1 + P.odds ^ m * P.odds := by
    have ho : 0 < P.odds := zero_lt_one.trans P.odds_gt_one
    positivity
  have hodds : (1 - 2 * P.gamma) * P.odds = 1 + 2 * P.gamma := by
    unfold BinarySymmetric.Parameters.odds
    field_simp [hpos.ne']
  have hfactor : (1 - 2 * P.gamma) * (1 + P.odds ^ m * P.odds) =
      (1 - 2 * P.gamma) + P.odds ^ m * (1 + 2 * P.gamma) := by
    calc
      _ = (1 - 2 * P.gamma) + P.odds ^ m * ((1 - 2 * P.gamma) * P.odds) := by ring
      _ = _ := by rw [hodds]
  unfold BinarySymmetric.Parameters.endpointError
  rw [pow_succ, mul_one_div]
  apply (div_le_div_iff₀ hnext hprev).mpr
  rw [one_mul, hfactor]
  nlinarith [mul_nonneg P.gamma_pos.le (sub_nonneg.mpr hp)]

theorem endpointCap_epsilon_lt_error (P : Parameters) (m : ℕ)
    (hm : m ≤ P.certificate.M) :
    P.certificate.epsilon < P.binarySymmetric.endpointError m := by
  have hM := PDMenu.menuEndpoint_pos P
  have hfloor := PDMenu.menuEpsilon_floor P
  have hsucc := PDMenu.endpointError_div_odds_le_succ P.binarySymmetric (P.certificate.M - 1)
  rw [Nat.sub_add_cancel hM] at hsucc
  exact (hfloor.trans_le hsucc).trans_le (P.binarySymmetric.endpointError_strictAnti.antitone hm)

theorem endpointCap_calibration_room (P : Parameters) (m : ℕ)
    (hm : m ≤ P.certificate.M) :
    P.binarySymmetric.endpointError (m + 1) + P.certificate.gamma * P.certificate.epsilon ≤
      P.binarySymmetric.endpointError m - P.certificate.gamma * P.certificate.epsilon := by
  have hcontract := endpointError_succ_contract P.binarySymmetric m
  have heps := endpointCap_epsilon_lt_error P m hm
  have hmul := mul_le_mul_of_nonneg_left heps.le P.certificate.gamma_pos.le
  change P.binarySymmetric.endpointError (m + 1) ≤
    (1 - 2 * P.certificate.gamma) * P.binarySymmetric.endpointError m at hcontract
  nlinarith


-- Initial unchanged body from Paid.PDROC_EndpointBounds_002

theorem endpointCap_incrementMax (B : BinarySymmetric.Parameters) :
    B.experiment.channelIncrementMax = B.h := by
  apply le_antisymm
  · unfold BinaryExperiment.channelIncrementMax
    apply Finset.sup'_le
    intro y _
    change |Real.log (B.experiment.channelReal true y / B.experiment.channelReal false y)| ≤ B.h
    exact (B.abs_logIncrement_eq_h y).le
  · have h := B.experiment.channelLogIncrement_abs_le true (0 : Fin 2)
    change |Real.log (B.experiment.channelReal true (0 : Fin 2) /
      B.experiment.channelReal false (0 : Fin 2))| ≤ _ at h
    rwa [B.abs_logIncrement_eq_h] at h

/-- A nonexit at any deterministic cap forces a centered lower deviation.
The quota condition is later discharged using the original certificate Q. -/
theorem endpointCap_nonexit_subset (B : BinarySymmetric.Parameters) (level n : ℕ)
    (hquota : (level : ℝ) ≤ (B.gamma : ℝ) * n) (x : Bool) :
    {tape | (n : ℕ∞) < B.experiment.posteriorThresholdStop (B.endpointError level) tape} ⊆
      {tape | B.kappa * (n : ℝ) / 2 ≤
        ∑ k ∈ Finset.range n, B.experiment.centeredNegativeIncrement x k tape} := by
  intro tape hbefore
  have hscore := B.experiment.logOddsScore_before_stop (B.endpointError level) tape n hbefore
  rw [B.endpointThreshold] at hscore
  have hnorm := B.experiment.prefixLogSum_norm_le_score ((), tape) x n
  change ‖∑ k ∈ Finset.range n, B.experiment.tapeLogIncrement x k tape‖ ≤
    |B.experiment.logOddsScore tape n| +
      |Real.log (B.experiment.priorReal true / B.experiment.priorReal false)| at hnorm
  have hprior : Real.log (B.experiment.priorReal true / B.experiment.priorReal false) = 0 := by
    norm_num [BinaryExperiment.priorReal, B.prior_eq_half]
  rw [hprior, abs_zero, add_zero, Real.norm_eq_abs] at hnorm
  have hlevel : (level : ℝ) * B.h ≤ B.kappa * (n : ℝ) / 2 := by
    have h := mul_le_mul_of_nonneg_right hquota B.h_pos.le
    unfold BinarySymmetric.Parameters.kappa
    nlinarith
  have hsum : (∑ k ∈ Finset.range n, B.experiment.tapeLogIncrement x k tape) <
      B.kappa * (n : ℝ) / 2 :=
    (lt_of_le_of_lt ((le_abs_self _).trans hnorm) hscore).trans_le hlevel
  have heq : (∑ k ∈ Finset.range n, B.experiment.centeredNegativeIncrement x k tape) =
      (n : ℝ) * B.kappa - ∑ k ∈ Finset.range n, B.experiment.tapeLogIncrement x k tape := by
    simp only [BinaryExperiment.centeredNegativeIncrement, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, B.divergence_eq_kappa]
  change B.kappa * (n : ℝ) / 2 ≤ _
  rw [heq]
  linarith

theorem endpointCap_tape_overflow_real (P : Parameters) (m : ℕ)
    (hm : m ≤ P.certificate.M) (x : Bool) :
    (P.binarySymmetric.experiment.tapeLaw x).real
      {tape | (P.certificate.Q : ℕ∞) <
        P.binarySymmetric.experiment.posteriorThresholdStop
          (P.binarySymmetric.endpointError (m + 1)) tape} ≤
      Real.exp (-(P.certificate.gamma : ℝ) ^ 2 * P.certificate.Q / 2) := by
  have hquota : ((m + 1 : ℕ) : ℝ) ≤
      (P.binarySymmetric.gamma : ℝ) * P.certificate.Q := by
    have hmM : (m : ℚ) + 1 ≤ (P.certificate.M : ℚ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hm 1
    have hmQ : (m : ℚ) + 1 ≤ P.certificate.gamma * P.certificate.Q :=
      hmM.trans (endpointCap_menu_drift P)
    exact_mod_cast hmQ
  have hsubset := endpointCap_nonexit_subset P.binarySymmetric (m + 1) P.certificate.Q hquota x
  have hmeasure := measureReal_mono (μ := P.binarySymmetric.experiment.tapeLaw x) hsubset (measure_ne_top _ _)
  have hhoeffding := P.binarySymmetric.experiment.centeredNegativeIncrement_hoeffding x P.certificate.Q
    (P.binarySymmetric.kappa * (P.certificate.Q : ℝ) / 2)
    (div_nonneg (mul_nonneg P.binarySymmetric.kappa_pos.le (Nat.cast_nonneg _)) (by norm_num))
  have hQ : (0 : ℝ) < P.certificate.Q := by exact_mod_cast P.certificate.Q_pos
  have hh := P.binarySymmetric.h_pos
  rw [endpointCap_incrementMax] at hhoeffding
  have hexponent : -(P.binarySymmetric.kappa * (P.certificate.Q : ℝ) / 2) ^ 2 /
      (2 * (P.certificate.Q : ℝ) * P.binarySymmetric.h ^ 2) =
      -(P.certificate.gamma : ℝ) ^ 2 * P.certificate.Q / 2 := by
    unfold BinarySymmetric.Parameters.kappa
    change -(2 * (P.certificate.gamma : ℝ) * P.binarySymmetric.h *
      (P.certificate.Q : ℝ) / 2) ^ 2 / (2 * (P.certificate.Q : ℝ) * P.binarySymmetric.h ^ 2) = _
    field_simp [hQ.ne', hh.ne']
  rw [hexponent] at hhoeffding
  exact hmeasure.trans hhoeffding

/-- The original D23 tail on the actual fair-seed times iid-tape law,
with the original m+1 hitting test and original Q. -/
theorem endpointCap_conditional_overflow (P : Parameters) (m : ℕ)
    (hm : m ≤ P.certificate.M) (x : Bool) :
    P.binarySymmetric.experiment.conditionalLaw BinarySymmetric.Parameters.fairGuessLaw x
      {sample | (P.binarySymmetric.symmetricHittingTest (m + 1)).rule.stop () sample.2 > P.certificate.Q} ≤
        ENNReal.ofReal (Real.exp (-(P.certificate.gamma : ℝ) ^ 2 * P.certificate.Q / 2)) := by
  have h := ENNReal.ofReal_le_ofReal (endpointCap_tape_overflow_real P m hm x)
  simp only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
  change BinarySymmetric.Parameters.fairGuessLaw.prod (P.binarySymmetric.experiment.tapeLaw x)
    {sample : Bool × P.binarySymmetric.experiment.Tape | (P.certificate.Q : ℕ∞) <
      P.binarySymmetric.experiment.posteriorThresholdStop
        (P.binarySymmetric.endpointError (m + 1)) sample.2} ≤ _
  have heq : {sample : Bool × P.binarySymmetric.experiment.Tape | (P.certificate.Q : ℕ∞) <
      P.binarySymmetric.experiment.posteriorThresholdStop
        (P.binarySymmetric.endpointError (m + 1)) sample.2} =
      Set.univ ×ˢ {tape | (P.certificate.Q : ℕ∞) <
        P.binarySymmetric.experiment.posteriorThresholdStop
          (P.binarySymmetric.endpointError (m + 1)) tape} := by
    ext sample
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and]
  rw [heq, Measure.prod_prod, measure_univ, one_mul]
  exact h


-- Initial unchanged body from Paid.PDROC_EndpointBounds_003

/-- Agreement includes the boundary T=Q and is pointwise on every tape.
The infinite-T case belongs to the overflow branch instead. -/
theorem endpointCap_decision_eq_on_hit (P : Parameters) (m : ℕ)
    (tie : Bool) (tape : P.binarySymmetric.experiment.Tape)
    (hstop : P.binarySymmetric.experiment.posteriorThresholdStop
      (P.binarySymmetric.endpointError (m + 1)) tape ≤ P.certificate.Q) :
    (P.cappedTest m).rule.decision tie tape =
      (P.binarySymmetric.hittingTestOnBool (m + 1)).rule.decision tie tape := by
  have hfinite : P.binarySymmetric.experiment.posteriorThresholdStop
      (P.binarySymmetric.endpointError (m + 1)) tape ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) hstop
  have hcast := ENat.natCast_toNat_eq_self.mpr hfinite
  have hhit := P.binarySymmetric.experiment.posteriorThresholdStop_hits
    (P.binarySymmetric.endpointError (m + 1)) tape _ hcast.symm
  rw [P.binarySymmetric.endpointThreshold] at hhit
  have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) * P.binarySymmetric.h :=
    mul_pos (by positivity) P.binarySymmetric.h_pos
  have hnonzero : P.binarySymmetric.experiment.logOddsScore tape
      (P.binarySymmetric.experiment.posteriorThresholdStop
        (P.binarySymmetric.endpointError (m + 1)) tape).toNat ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hhit
    linarith
  have hcap : P.cappedStop m tape = P.binarySymmetric.experiment.posteriorThresholdStop
      (P.binarySymmetric.endpointError (m + 1)) tape := min_eq_left hstop
  change P.cappedDecision m tie tape = decide (0 ≤ P.binarySymmetric.experiment.logOddsScore tape
    (P.binarySymmetric.experiment.posteriorThresholdStop
      (P.binarySymmetric.endpointError (m + 1)) tape).toNat)
  simp only [PaperProofs.Paid.Parameters.cappedDecision, hcap, hnonzero, ↓reduceIte]

/-- Truncation changes an error only on strict overflow; no exceptional
tapes are removed from the pointwise agreement used here. -/
theorem endpointCap_error_le_endpoint_add_exp (P : Parameters) (m : ℕ)
    (hm : m ≤ P.certificate.M) (x : Bool) :
    P.binarySymmetric.experiment.conditionalError BinarySymmetric.Parameters.fairGuessLaw (P.cappedTest m) x ≤
      ENNReal.ofReal (P.binarySymmetric.endpointError (m + 1) : ℝ) +
        ENNReal.ofReal (Real.exp (-(P.certificate.gamma : ℝ) ^ 2 * P.certificate.Q / 2)) := by
  let μ := P.binarySymmetric.experiment.conditionalLaw BinarySymmetric.Parameters.fairGuessLaw x
  let oldError : Set (Bool × P.binarySymmetric.experiment.Tape) :=
    {sample | (P.binarySymmetric.hittingTestOnBool (m + 1)).rule.decision sample.1 sample.2 ≠ x}
  let overflow : Set (Bool × P.binarySymmetric.experiment.Tape) :=
    {sample | (P.binarySymmetric.symmetricHittingTest (m + 1)).rule.stop () sample.2 > P.certificate.Q}
  have hsubset : {sample | (P.cappedTest m).rule.decision sample.1 sample.2 ≠ x} ⊆ oldError ∪ overflow := by
    intro sample herr
    by_cases hstop : P.binarySymmetric.experiment.posteriorThresholdStop
        (P.binarySymmetric.endpointError (m + 1)) sample.2 ≤ P.certificate.Q
    · apply Or.inl
      change (P.binarySymmetric.hittingTestOnBool (m + 1)).rule.decision sample.1 sample.2 ≠ x
      change (P.cappedTest m).rule.decision sample.1 sample.2 ≠ x at herr
      rwa [endpointCap_decision_eq_on_hit P m sample.1 sample.2 hstop] at herr
    · exact Or.inr (lt_of_not_ge hstop)
  have hold : μ oldError = ENNReal.ofReal (P.binarySymmetric.endpointError (m + 1) : ℝ) := by
    change P.binarySymmetric.experiment.conditionalError BinarySymmetric.Parameters.fairGuessLaw
      (P.binarySymmetric.hittingTestOnBool (m + 1)) x = _
    rw [hittingTestOnBool_conditionalError]
    exact P.binarySymmetric.symmetricHitting_conditionalError_eq (m + 1) (by omega) x
  change μ _ ≤ _
  calc
    μ _ ≤ μ (oldError ∪ overflow) := measure_mono hsubset
    _ ≤ μ oldError + μ overflow := measure_union_le _ _
    _ ≤ ENNReal.ofReal (P.binarySymmetric.endpointError (m + 1) : ℝ) +
        ENNReal.ofReal (Real.exp (-(P.certificate.gamma : ℝ) ^ 2 * P.certificate.Q / 2)) := by
      rw [hold]
      exact add_le_add le_rfl (endpointCap_conditional_overflow P m hm x)

theorem endpointCap_error_le_endpoint_add_target (P : Parameters) (m : ℕ)
    (hm : m ≤ P.certificate.M) (x : Bool) :
    P.binarySymmetric.experiment.conditionalError BinarySymmetric.Parameters.fairGuessLaw (P.cappedTest m) x ≤
      ENNReal.ofReal ((P.binarySymmetric.endpointError (m + 1) +
        P.certificate.gamma * P.certificate.epsilon : ℚ) : ℝ) := by
  have htarget : (1 / 2 : ℝ) ^ P.certificate.E ≤
      ((P.certificate.gamma * P.certificate.epsilon : ℚ) : ℝ) := by
    have hcast := (Rat.cast_le (K := ℝ)).mpr (endpointCap_binary_le_target P)
    simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hcast
  have hexp := (endpointCap_exp_le_exp P).trans ((endpointCap_exp_le_binary P).trans htarget)
  have h := (endpointCap_error_le_endpoint_add_exp P m hm x).trans
    (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hexp))
  have hp : (0 : ℝ) ≤ (P.binarySymmetric.endpointError (m + 1) : ℚ) := by
    exact_mod_cast (P.binarySymmetric.endpointError_pos (m + 1)).le
  have ht : (0 : ℝ) ≤ ((P.certificate.gamma * P.certificate.epsilon : ℚ) : ℝ) := by
    exact_mod_cast (mul_pos P.certificate.gamma_pos P.certificate.epsilon_pos).le
  simpa only [Rat.cast_add, ENNReal.ofReal_add hp ht] using h

/-- Once the independent rational DP has its actual error law, the
numerical q-bound follows; this helper does not assume the q-bound itself. -/
theorem endpointCap_dp_bound_of_error_law (P : Parameters) (m : ℕ)
    (hm : m ≤ P.certificate.M)
    (hlaw : P.binarySymmetric.experiment.conditionalError BinarySymmetric.Parameters.fairGuessLaw
      (P.cappedTest m) true = ENNReal.ofReal (P.cappedError m : ℝ)) :
    P.cappedError m ≤ P.binarySymmetric.endpointError (m + 1) +
      P.certificate.gamma * P.certificate.epsilon := by
  have h := endpointCap_error_le_endpoint_add_target P m hm true
  rw [hlaw] at h
  have hr : (0 : ℝ) ≤ ((P.binarySymmetric.endpointError (m + 1) +
      P.certificate.gamma * P.certificate.epsilon : ℚ) : ℝ) := by
    exact_mod_cast add_nonneg (P.binarySymmetric.endpointError_pos (m + 1)).le
      (mul_pos P.certificate.gamma_pos P.certificate.epsilon_pos).le
  exact_mod_cast (ENNReal.ofReal_le_ofReal_iff hr).mp h


-- Initial unchanged body from Paid.PDROC_EndpointBounds_004

/-- Exact assembly with only the actual rational-array semantic gap
left explicit. This is a conditional component, not original D23 closure. -/
theorem boundedEndpointClaims_of_dp_law (P : Parameters)
    (hdp : ∀ m : ℕ, 1 ≤ m → m ≤ P.certificate.M →
      (∀ x : Bool, P.binarySymmetric.experiment.conditionalError BinarySymmetric.Parameters.fairGuessLaw
        (P.cappedTest m) x = ENNReal.ofReal (P.cappedError m : ℝ)) ∧ 0 ≤ P.cappedError m) :
    P.BoundedEndpointClaims := by
  intro m hm hM
  obtain ⟨hlaw, hnonneg⟩ := hdp m hm hM
  have hbound := endpointCap_dp_bound_of_error_law P m hM (hlaw true)
  have hroom := endpointCap_calibration_room P m hM
  refine ⟨endpointCap_conditional_overflow P m hM,
    endpointCap_exp_le_exp P, endpointCap_exp_le_binary P,
    endpointCap_binary_le_target P, hlaw, hnonneg,
    endpointError_succ_contract P.binarySymmetric m, hbound, hroom, ?_⟩
  have hgap := mul_pos P.certificate.gamma_pos P.certificate.epsilon_pos
  linarith


end PDROC
