module

public import PaperProofs.Common.NormalCharges
public import PaperProofs.Common.NativeContracts
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory

namespace PaperProofs.Paid

open Common

/-- Fee-independent data of the original explicit certificate in Appendix D.
All comparisons used for the finite searches below are rational. -/
structure CertificateInput where
  stages : ℕ
  stages_pos : 0 < stages
  gamma : ℚ
  gamma_pos : 0 < gamma
  gamma_le_quarter : gamma ≤ 1 / 4
  risk : ℚ
  risk_pos : 0 < risk
  risk_le : risk ≤ 1 / 64

namespace CertificateInput

def odds (D : CertificateInput) : ℚ := (1 + 2 * D.gamma) / (1 - 2 * D.gamma)

theorem denominator_pos (D : CertificateInput) : 0 < 1 - 2 * D.gamma := by
  linarith [D.gamma_le_quarter]

theorem odds_gt_one (D : CertificateInput) : 1 < D.odds := by
  unfold odds
  apply (lt_div_iff₀ D.denominator_pos).mpr
  linarith [D.gamma_pos]

theorem odds_pos (D : CertificateInput) : 0 < D.odds := lt_trans zero_lt_one D.odds_gt_one

def rocError (D : CertificateInput) (m : ℕ) : ℚ := 1 / (1 + D.odds ^ m)

theorem rocError_pos (D : CertificateInput) (m : ℕ) : 0 < D.rocError m :=
  one_div_pos.mpr (add_pos zero_lt_one (pow_pos D.odds_pos m))

def varianceBase (D : CertificateInput) : ℚ := 1 - 4 * D.gamma ^ 2

theorem varianceBase_nonneg (D : CertificateInput) : 0 ≤ D.varianceBase := by
  have hprod := mul_le_mul_of_nonneg_right D.gamma_le_quarter D.gamma_pos.le
  dsimp [varianceBase]
  nlinarith [D.gamma_le_quarter]

theorem varianceBase_lt_one (D : CertificateInput) : D.varianceBase < 1 := by
  dsimp [varianceBase]
  nlinarith [sq_pos_of_pos D.gamma_pos]

def MajorityQualifies (D : CertificateInput) (t : ℕ) : Prop :=
  1 ≤ t ∧ Odd t ∧ D.varianceBase ^ t ≤ (D.risk / (2 * (D.stages : ℚ))) ^ 2

instance majorityQualifies_decidable (D : CertificateInput) : DecidablePred D.MajorityQualifies :=
  fun _ => by unfold MajorityQualifies; infer_instance

theorem exists_majorityQualifies (D : CertificateInput) : ∃ t, D.MajorityQualifies t := by
  have hN : 0 < (D.stages : ℚ) := by exact_mod_cast D.stages_pos
  have htarget : 0 < (D.risk / (2 * (D.stages : ℚ))) ^ 2 :=
    sq_pos_of_pos (div_pos D.risk_pos (mul_pos (by norm_num) hN))
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one htarget D.varianceBase_lt_one
  refine ⟨2 * n + 1, by omega, ⟨n, by omega⟩, ?_⟩
  exact (pow_le_pow_of_le_one D.varianceBase_nonneg D.varianceBase_lt_one.le
    (by omega : n ≤ 2 * n + 1)).trans hn.le

/-- The original least positive odd integer; the search tests rational powers. -/
def t0 (D : CertificateInput) : ℕ := Nat.find D.exists_majorityQualifies

theorem t0_spec (D : CertificateInput) : D.MajorityQualifies D.t0 :=
  Nat.find_spec D.exists_majorityQualifies

theorem t0_min (D : CertificateInput) {t : ℕ} (ht : D.MajorityQualifies t) : D.t0 ≤ t :=
  Nat.find_min' D.exists_majorityQualifies ht

theorem t0_pos (D : CertificateInput) : 0 < D.t0 := D.t0_spec.1

/-- The exact ratio c/Lambda after cancelling the positive review price. -/
def menuRatio (D : CertificateInput) : ℚ :=
  D.risk / (4 * (D.stages : ℚ) * (D.t0 : ℚ))

theorem menuRatio_pos (D : CertificateInput) : 0 < D.menuRatio := by
  have hN : 0 < (D.stages : ℚ) := by exact_mod_cast D.stages_pos
  have ht : 0 < (D.t0 : ℚ) := by exact_mod_cast D.t0_pos
  exact div_pos D.risk_pos (mul_pos (mul_pos (by norm_num) hN) ht)

def epsilon (D : CertificateInput) : ℚ := D.menuRatio / 3

theorem epsilon_pos (D : CertificateInput) : 0 < D.epsilon :=
  div_pos D.menuRatio_pos (by norm_num)

theorem exists_menuEndpoint (D : CertificateInput) : ∃ m, D.rocError m ≤ D.menuRatio := by
  have hinv : D.odds⁻¹ < 1 := (inv_lt_one₀ D.odds_pos).mpr D.odds_gt_one
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one D.menuRatio_pos hinv
  refine ⟨m, ?_⟩
  have hpow : 0 < D.odds ^ m := pow_pos D.odds_pos m
  have hbound : D.rocError m ≤ (D.odds⁻¹) ^ m := by
    unfold rocError
    rw [inv_pow, ← one_div]
    exact one_div_le_one_div_of_le hpow (by linarith)
  exact hbound.trans hm.le

def M (D : CertificateInput) : ℕ := Nat.find D.exists_menuEndpoint

theorem M_spec (D : CertificateInput) : D.rocError D.M ≤ D.menuRatio :=
  Nat.find_spec D.exists_menuEndpoint

theorem M_min (D : CertificateInput) {m : ℕ} (hm : D.rocError m ≤ D.menuRatio) : D.M ≤ m :=
  Nat.find_min' D.exists_menuEndpoint hm

def ExponentQualifies (D : CertificateInput) (e : ℕ) : Prop :=
  1 ≤ e ∧ (1 / 2 : ℚ) ^ e ≤ D.gamma * D.epsilon

instance exponentQualifies_decidable (D : CertificateInput) : DecidablePred D.ExponentQualifies :=
  fun _ => by unfold ExponentQualifies; infer_instance

theorem exists_exponentQualifies (D : CertificateInput) : ∃ e, D.ExponentQualifies e := by
  have htarget : 0 < D.gamma * D.epsilon := mul_pos D.gamma_pos D.epsilon_pos
  obtain ⟨e, he⟩ := exists_pow_lt_of_lt_one htarget (by norm_num : (1 / 2 : ℚ) < 1)
  refine ⟨e + 1, by omega, ?_⟩
  exact (pow_le_pow_of_le_one (by norm_num : (0 : ℚ) ≤ 1 / 2) (by norm_num)
    (by omega : e ≤ e + 1)).trans he.le

def E (D : CertificateInput) : ℕ := Nat.find D.exists_exponentQualifies

theorem E_spec (D : CertificateInput) : D.ExponentQualifies D.E :=
  Nat.find_spec D.exists_exponentQualifies

theorem E_min (D : CertificateInput) {e : ℕ} (he : D.ExponentQualifies e) : D.E ≤ e :=
  Nat.find_min' D.exists_exponentQualifies he

/-- Only this fee-independent Q qualifies the original resources in Appendix D. -/
def Q (D : CertificateInput) : ℕ :=
  max 1 (max (Nat.ceil (((D.M : ℚ) + 1) / D.gamma))
    (Nat.ceil ((2 * (D.E : ℚ)) / D.gamma ^ 2)))

theorem Q_pos (D : CertificateInput) : 0 < D.Q := lt_of_lt_of_le (by norm_num) (le_max_left _ _)

end CertificateInput

/-- The restricted homogeneous shared-pool model, with K<N. The correction
price is intentionally a separate argument, so setting it to zero changes
neither the experiment, original contract, accounting function nor risk. -/
structure Parameters where
  certificate : CertificateInput
  tools : ℕ
  tools_lt_stages : tools < certificate.stages
  reviewFee : ℚ
  reviewFee_pos : 0 < reviewFee

namespace Parameters

def sharedInstance (P : Parameters) : Instance where
  toolCount := P.tools
  compatibility := List.replicate P.certificate.stages Finset.univ

theorem stageCount_eq (P : Parameters) : P.sharedInstance.stageCount = P.certificate.stages := by
  simp [sharedInstance, Instance.stageCount]

theorem eligible_eq_univ (P : Parameters) (i : P.sharedInstance.Stage) :
    P.sharedInstance.eligible i = Finset.univ := by
  have h : P.sharedInstance.eligible i ∈ P.sharedInstance.compatibility := List.get_mem _ i
  change P.sharedInstance.eligible i ∈ List.replicate P.certificate.stages Finset.univ at h
  exact List.eq_of_mem_replicate h

def experiment (P : Parameters) : Statistics.BinaryExperiment where
  alphabetSize := 2
  priorOne := 1 / 2
  prior_pos := by norm_num
  prior_lt_one := by norm_num
  channel x y :=
    if y.val = (if x then 1 else 0) then 1 / 2 + P.certificate.gamma
    else 1 / 2 - P.certificate.gamma
  channel_pos := by
    intro x y
    split_ifs <;> linarith [P.certificate.gamma_pos, P.certificate.gamma_le_quarter]
  channel_sum := by
    intro x
    cases x <;> norm_num [Fin.sum_univ_two]
  channel_distinct := by
    intro heq
    have h := congrFun heq (0 : Fin 2)
    norm_num at h
    linarith [P.certificate.gamma_pos]
  observationFee := P.reviewFee
  observationFee_pos := P.reviewFee_pos

def input (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) : StatisticalInput P.sharedInstance where
  experiment := fun _ => P.experiment
  correctionFee := fun _ _ => fee
  correctionFee_nonneg := fun _ _ => hfee

theorem input_same_experiment (P : Parameters) (fee fee' : ℚ)
    (hfee : 0 ≤ fee) (hfee' : 0 ≤ fee') :
    (P.input fee hfee).experiment = (P.input fee' hfee').experiment := rfl

theorem actual_correctionFee (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (i : P.sharedInstance.Stage) (r : P.sharedInstance.Tool) :
    (P.input fee hfee).fees.correction i r = fee := rfl

abbrev PaymentContract (P : Parameters) := {C : Contract P.sharedInstance // C.IsCurrentPayment}

def paymentContract (P : Parameters) (quota : P.sharedInstance.Stage → ℕ) (H H0 : ℕ) :
    P.PaymentContract :=
  ⟨⟨.early, .currentWindow, .currentWindow, quota, H, H0⟩, ⟨⟨rfl, rfl⟩, rfl⟩⟩

/-- Exactly the existing real-policy constrained infimum, with the same
current-payment contract and actual-execution billing. Normal C0 fees remain
the independent NormalCharges interface, as in the frozen variable bill. -/
noncomputable def paidValue (P : Parameters) (C : P.PaymentContract)
    (mode : Native.ResourceMode) (accounting : Native.NormalAccounting P.sharedInstance)
    (fee : ℚ) (hfee : 0 ≤ fee) : ℝ≥0∞ :=
  Native.value (P.input fee hfee) C.val mode accounting (ENNReal.ofReal (P.certificate.risk : ℝ))

noncomputable def nativeValue (P : Parameters) (C : P.PaymentContract)
    (accounting : Native.NormalAccounting P.sharedInstance) (fee : ℚ) (hfee : 0 ≤ fee) : ℝ≥0∞ :=
  P.paidValue C .native accounting fee hfee

noncomputable def uncappedValue (P : Parameters) (C : P.PaymentContract)
    (accounting : Native.NormalAccounting P.sharedInstance) (fee : ℚ) (hfee : 0 ≤ fee) : ℝ≥0∞ :=
  P.paidValue C .uncapped accounting fee hfee

noncomputable def freeValue (P : Parameters) (C : P.PaymentContract)
    (mode : Native.ResourceMode) (accounting : Native.NormalAccounting P.sharedInstance) : ℝ≥0∞ :=
  P.paidValue C mode accounting 0 (by norm_num)

theorem uncappedValue_le_nativeValue (P : Parameters) (C : P.PaymentContract)
    (accounting : Native.NormalAccounting P.sharedInstance) (fee : ℚ) (hfee : 0 ≤ fee) :
    P.uncappedValue C accounting fee hfee ≤ P.nativeValue C accounting fee hfee :=
  Native.value_uncapped_le_native (P.input fee hfee) C.val accounting _

noncomputable def h (P : Parameters) : ℝ := Real.log (P.certificate.odds : ℝ)
noncomputable def kappa (P : Parameters) : ℝ := 2 * (P.certificate.gamma : ℝ) * P.h
noncomputable def a (P : Parameters) : ℝ := (P.reviewFee : ℝ) / P.kappa

theorem h_pos (P : Parameters) : 0 < P.h := by
  apply Real.log_pos
  exact_mod_cast P.certificate.odds_gt_one

theorem kappa_pos (P : Parameters) : 0 < P.kappa := by
  have hgamma : 0 < (P.certificate.gamma : ℝ) := by exact_mod_cast P.certificate.gamma_pos
  exact mul_pos (mul_pos (by norm_num) hgamma) P.h_pos

theorem a_pos (P : Parameters) : 0 < P.a := by
  have hc : 0 < (P.reviewFee : ℝ) := by exact_mod_cast P.reviewFee_pos
  exact div_pos hc P.kappa_pos

/-- The original baseline B and multiplier Lambda retain their c dependence. -/
def B (P : Parameters) : ℚ :=
  P.reviewFee * (P.certificate.stages : ℚ) * (P.certificate.t0 : ℚ)

def Lambda (P : Parameters) : ℚ := 4 * P.B / P.certificate.risk

theorem B_pos (P : Parameters) : 0 < P.B := by
  have hN : 0 < (P.certificate.stages : ℚ) := by exact_mod_cast P.certificate.stages_pos
  have ht : 0 < (P.certificate.t0 : ℚ) := by exact_mod_cast P.certificate.t0_pos
  exact mul_pos (mul_pos P.reviewFee_pos hN) ht

theorem Lambda_pos (P : Parameters) : 0 < P.Lambda :=
  div_pos (mul_pos (by norm_num) P.B_pos) P.certificate.risk_pos

theorem priceRatio_eq (P : Parameters) : P.reviewFee / P.Lambda = P.certificate.menuRatio := by
  have hc : P.reviewFee ≠ 0 := P.reviewFee_pos.ne'
  have hN : (P.certificate.stages : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt P.certificate.stages_pos)
  have ht : (P.certificate.t0 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt P.certificate.t0_pos)
  have hr : P.certificate.risk ≠ 0 := P.certificate.risk_pos.ne'
  unfold Lambda B CertificateInput.menuRatio
  field_simp [hc, hN, ht, hr]

theorem epsilon_formula (P : Parameters) :
    P.certificate.epsilon = P.reviewFee / (3 * P.Lambda) := by
  rw [CertificateInput.epsilon, ← P.priceRatio_eq]
  ring

theorem M_original_spec (P : Parameters) :
    P.certificate.rocError P.certificate.M ≤ P.reviewFee / P.Lambda := by
  rw [P.priceRatio_eq]
  exact P.certificate.M_spec

theorem M_original_min (P : Parameters) {m : ℕ}
    (hm : P.certificate.rocError m ≤ P.reviewFee / P.Lambda) : P.certificate.M ≤ m := by
  rw [P.priceRatio_eq] at hm
  exact P.certificate.M_min hm

theorem E_original_spec (P : Parameters) : 1 ≤ P.certificate.E ∧
    (1 / 2 : ℚ) ^ P.certificate.E ≤
      P.certificate.gamma * (P.reviewFee / (3 * P.Lambda)) := by
  have h := P.certificate.E_spec
  unfold CertificateInput.ExponentQualifies at h
  rwa [P.epsilon_formula] at h

theorem Q_ge_one (P : Parameters) : 1 ≤ P.certificate.Q := le_max_left _ _

theorem Q_ge_menu_ceil (P : Parameters) :
    Nat.ceil (((P.certificate.M : ℚ) + 1) / P.certificate.gamma) ≤ P.certificate.Q :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem Q_ge_tail_ceil (P : Parameters) :
    Nat.ceil ((2 * (P.certificate.E : ℚ)) / P.certificate.gamma ^ 2) ≤ P.certificate.Q :=
  (le_max_right _ _).trans (le_max_right _ _)

/-- Only the arithmetic portion of the original cap check. This proposition
does not establish any controller's normal-call certificate or lawful Steps. -/
structure NativeCapQualification (P : Parameters) (C : P.PaymentContract) : Prop where
  stage_quota : ∀ i, P.certificate.Q ≤ C.val.reviewQuota i
  total_calls : C.val.normalCallBound + P.certificate.stages * P.certificate.Q + P.tools ≤
    C.val.totalCallCap

end Parameters
end PaperProofs.Paid

