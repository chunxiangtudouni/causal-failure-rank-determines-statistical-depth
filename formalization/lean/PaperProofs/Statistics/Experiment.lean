module

public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import Mathlib.Data.ENat.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
Finite binary experiments from `model.tex:11-18` and `prices.tex:10-19`.
The finite KL formula is defined independently of any claimed sequential-test
bound. The stopping-rule interface below retains arbitrary private seeds and
infinite stopping times. No sequential-information or SPRT theorem is assumed.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace PaperProofs.Statistics

/-- The rational, full-support, informative experiment at one fresh stage. -/
structure BinaryExperiment where
  alphabetSize : ℕ
  priorOne : ℚ
  prior_pos : 0 < priorOne
  prior_lt_one : priorOne < 1
  channel : Bool → Fin alphabetSize → ℚ
  channel_pos : ∀ x y, 0 < channel x y
  channel_sum : ∀ x, ∑ y, channel x y = 1
  channel_distinct : channel false ≠ channel true
  observationFee : ℚ
  observationFee_pos : 0 < observationFee

namespace BinaryExperiment

def prior (E : BinaryExperiment) (x : Bool) : ℚ :=
  if x then E.priorOne else 1 - E.priorOne

def priorReal (E : BinaryExperiment) (x : Bool) : ℝ := E.prior x

def channelReal (E : BinaryExperiment) (x : Bool) (y : Fin E.alphabetSize) : ℝ :=
  E.channel x y

theorem prior_pos' (E : BinaryExperiment) (x : Bool) : 0 < E.prior x := by
  cases x
  · exact sub_pos.mpr E.prior_lt_one
  · exact E.prior_pos

theorem priorReal_pos (E : BinaryExperiment) (x : Bool) : 0 < E.priorReal x := by
  change 0 < (E.prior x : ℝ)
  exact_mod_cast E.prior_pos' x

theorem channelReal_pos (E : BinaryExperiment) (x : Bool) (y : Fin E.alphabetSize) :
    0 < E.channelReal x y := by
  change 0 < (E.channel x y : ℝ)
  exact_mod_cast E.channel_pos x y

theorem channelReal_sum (E : BinaryExperiment) (x : Bool) :
    ∑ y, E.channelReal x y = 1 := by
  change ∑ y, (E.channel x y : ℝ) = 1
  exact_mod_cast E.channel_sum x

theorem observationFee_real_pos (E : BinaryExperiment) : 0 < (E.observationFee : ℝ) := by
  exact_mod_cast E.observationFee_pos

/-- `D_ix = KL(P_i^x || P_i^(1-x))`, the finite full-support formula. -/
noncomputable def divergence (E : BinaryExperiment) (x : Bool) : ℝ :=
  ∑ y, E.channelReal x y * Real.log (E.channelReal x y / E.channelReal (!x) y)

theorem divergence_eq_sum_klFun (E : BinaryExperiment) (x : Bool) :
    E.divergence x =
      ∑ y, E.channelReal (!x) y *
        InformationTheory.klFun (E.channelReal x y / E.channelReal (!x) y) := by
  have hterm (y : Fin E.alphabetSize) :
      E.channelReal (!x) y *
          InformationTheory.klFun (E.channelReal x y / E.channelReal (!x) y) =
        E.channelReal x y * Real.log (E.channelReal x y / E.channelReal (!x) y) +
          E.channelReal (!x) y - E.channelReal x y := by
    have hcancel : E.channelReal (!x) y *
        (E.channelReal x y / E.channelReal (!x) y) = E.channelReal x y := by
      field_simp [ne_of_gt (E.channelReal_pos (!x) y)]
    unfold InformationTheory.klFun
    calc
      _ = (E.channelReal (!x) y *
              (E.channelReal x y / E.channelReal (!x) y)) *
              Real.log (E.channelReal x y / E.channelReal (!x) y) +
            E.channelReal (!x) y - E.channelReal (!x) y *
              (E.channelReal x y / E.channelReal (!x) y) := by ring
      _ = _ := by rw [hcancel]
  symm
  simp_rw [hterm]
  simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, E.channelReal_sum, divergence]

theorem divergence_nonneg (E : BinaryExperiment) (x : Bool) : 0 ≤ E.divergence x := by
  rw [E.divergence_eq_sum_klFun]
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg (E.channelReal_pos (!x) y).le
    (InformationTheory.klFun_nonneg
      (div_pos (E.channelReal_pos x y) (E.channelReal_pos (!x) y)).le)

theorem divergence_pos (E : BinaryExperiment) (x : Bool) : 0 < E.divergence x := by
  have hdistinct : E.channel x ≠ E.channel (!x) := by
    cases x
    · exact E.channel_distinct
    · exact Ne.symm E.channel_distinct
  obtain ⟨y, hy⟩ := not_forall.mp (fun h => hdistinct (funext h))
  have hyreal : E.channelReal x y ≠ E.channelReal (!x) y := by
    change (E.channel x y : ℝ) ≠ (E.channel (!x) y : ℝ)
    exact_mod_cast hy
  have hratio : E.channelReal x y / E.channelReal (!x) y ≠ 1 := by
    intro h
    exact hyreal ((div_eq_one_iff_eq (ne_of_gt (E.channelReal_pos (!x) y))).mp h)
  have hratio_nonneg := (div_pos (E.channelReal_pos x y) (E.channelReal_pos (!x) y)).le
  have hkl_ne : InformationTheory.klFun
      (E.channelReal x y / E.channelReal (!x) y) ≠ 0 := by
    intro h
    exact hratio ((InformationTheory.klFun_eq_zero_iff hratio_nonneg).mp h)
  have hkl_pos : 0 < InformationTheory.klFun
      (E.channelReal x y / E.channelReal (!x) y) :=
    lt_of_le_of_ne (InformationTheory.klFun_nonneg hratio_nonneg) (Ne.symm hkl_ne)
  rw [E.divergence_eq_sum_klFun]
  apply Finset.sum_pos'
  · intro z _
    exact mul_nonneg (E.channelReal_pos (!x) z).le
      (InformationTheory.klFun_nonneg
        (div_pos (E.channelReal_pos x z) (E.channelReal_pos (!x) z)).le)
  · exact ⟨y, Finset.mem_univ y, mul_pos (E.channelReal_pos (!x) y) hkl_pos⟩

/-- The ordered-price input `A_i`, without a real-valued KL oracle in the input. -/
noncomputable def coefficient (E : BinaryExperiment) : ℝ :=
  (E.observationFee : ℝ) * ∑ x : Bool, E.priorReal x / E.divergence x

theorem coefficient_pos (E : BinaryExperiment) : 0 < E.coefficient := by
  apply mul_pos E.observationFee_real_pos
  apply Finset.sum_pos
  · intro x _
    exact div_pos (E.priorReal_pos x) (E.divergence_pos x)
  · exact Finset.univ_nonempty

/-- A possibly infinite observation count is charged before any conversion to real cost. -/
noncomputable def observationCharge (E : BinaryExperiment) (samples : ℕ∞) : ℝ≥0∞ :=
  if samples = ⊤ then ⊤ else ENNReal.ofReal (E.observationFee : ℝ) * samples.toNat

@[simp] theorem observationCharge_top (E : BinaryExperiment) : E.observationCharge ⊤ = ⊤ := by
  simp [observationCharge]

@[simp] theorem observationCharge_zero (E : BinaryExperiment) : E.observationCharge 0 = 0 := by
  simp [observationCharge]

@[simp] theorem observationCharge_nat (E : BinaryExperiment) (n : ℕ) :
    E.observationCharge n = ENNReal.ofReal (E.observationFee : ℝ) * n := by
  simp [observationCharge]

abbrev Tape (E : BinaryExperiment) := ℕ → Fin E.alphabetSize

/-- The rule sees its private seed and only the observed prefix of the current tape. -/
def IsStoppingRule (E : BinaryExperiment) {Seed : Type*}
    (stop : Seed → E.Tape → ℕ∞) : Prop :=
  ∀ seed tape tape' (n : ℕ), (∀ k < n, tape k = tape' k) →
    (stop seed tape ≤ n ↔ stop seed tape' ≤ n)

/-- Decisions at finite stopping times cannot inspect unobserved tape entries. -/
def IsStoppedDecision (E : BinaryExperiment) {Seed : Type*}
    (stop : Seed → E.Tape → ℕ∞) (decision : Seed → E.Tape → Bool) : Prop :=
  ∀ seed tape tape' (n : ℕ), stop seed tape = n → stop seed tape' = n →
    (∀ k < n, tape k = tape' k) → decision seed tape = decision seed tape'

/-- Pure rules conditional on arbitrary private randomness; independence of the seed
and the fresh fact/tape belongs to the common probability model, not this data type. -/
structure SequentialRule (E : BinaryExperiment) (Seed : Type*) where
  stop : Seed → E.Tape → ℕ∞
  decision : Seed → E.Tape → Bool
  stopping : E.IsStoppingRule stop
  stoppedDecision : E.IsStoppedDecision stop decision

end BinaryExperiment

end PaperProofs.Statistics
