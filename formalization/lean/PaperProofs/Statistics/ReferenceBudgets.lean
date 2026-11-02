module

public import PaperProofs.Statistics.ControllerThresholds
public import Mathlib.Data.PNat.Basic

/-!
The numerical risk-budget part of price-proofs.tex:169--238. Branch labels
are the actual correct/error reports and the three original rank cases.
Every labelled sequence is permitted by the lemmas, so no favorable path
restriction is imposed. Extracting these labels from Native.Policy, proving
conditional error bounds, and proving overflow probabilities remain separate.

Infinite rank uses no test and keeps r. No-tool error ends the constructed
reference run; it does not become a zero-risk continuation. A positive finite
bad depth uses exactly p_j and min(1/4,r/(2p_j)) on the error branch.
-/

@[expose] public section

namespace PaperProofs.Statistics

inductive ReferenceBudgetCase where
  | infiniteRank
  | noTool
  | finiteBad (depth : ℕ+)
  deriving DecidableEq

abbrev ReferenceBudgetEvent := ReferenceBudgetCase × Bool

def referenceBudgetTarget (kind : ReferenceBudgetCase) (risk : ℚ) : Option ℚ :=
  match kind with
  | .infiniteRank => none
  | .noTool => some (risk / 2)
  | .finiteBad depth => some (controllerTarget risk depth.val)

/-- `error = true` is an actually reported error. None is termination after
the unrepairable no-tool error, and never a successful continuation budget. -/
def referenceBudgetStep (kind : ReferenceBudgetCase) (error : Bool) (risk : ℚ) : Option ℚ :=
  match kind with
  | .infiniteRank => some risk
  | .noTool => if error then none else some (risk / 2)
  | .finiteBad depth => some (if error then controllerBadRisk risk (controllerTarget risk depth.val) else risk / 2)

def referenceBudgetPath (initial : ℚ) : List ReferenceBudgetEvent → Option ℚ
  | [] => some initial
  | event :: rest => (referenceBudgetStep event.1 event.2 initial).bind
      (fun child => referenceBudgetPath child rest)

def ReferenceBudgetValid (risk : ℚ) : Prop := 0 < risk ∧ risk ≤ 1 / 4

theorem referenceBudgetStep_valid_floor (kind : ReferenceBudgetCase) (error : Bool)
    (risk child : ℚ) (hvalid : ReferenceBudgetValid risk)
    (hstep : referenceBudgetStep kind error risk = some child) :
    ReferenceBudgetValid child ∧ risk / 2 ≤ child := by
  cases kind with
  | infiniteRank =>
    have heq : risk = child := Option.some.inj hstep
    subst child
    exact ⟨hvalid, by have hr := hvalid.1; linarith⟩
  | noTool =>
    cases error with
    | false =>
      have heq : risk / 2 = child := Option.some.inj hstep
      subst child
      exact ⟨⟨by have hr := hvalid.1; linarith, by have hr := hvalid.2; linarith⟩, le_rfl⟩
    | true => cases hstep
  | finiteBad depth =>
    cases error with
    | false =>
      have heq : risk / 2 = child := Option.some.inj hstep
      subst child
      exact ⟨⟨by have hr := hvalid.1; linarith, by have hr := hvalid.2; linarith⟩, le_rfl⟩
    | true =>
      have heq : controllerBadRisk risk (controllerTarget risk depth.val) = child := Option.some.inj hstep
      subst child
      have hb := controllerBadRisk_bounds risk (controllerTarget risk depth.val) hvalid.1 hvalid.2
        (controllerTarget_pos risk depth.val) (controllerTarget_le_quarter risk depth.val)
      exact ⟨⟨hvalid.1.trans_le hb.1, hb.2⟩, (by have hr := hvalid.1; linarith : risk / 2 ≤ risk).trans hb.1⟩

theorem referenceBudgetTarget_valid_floor (kind : ReferenceBudgetCase) (risk target : ℚ)
    (hvalid : ReferenceBudgetValid risk) (htarget : referenceBudgetTarget kind risk = some target) :
    0 < target ∧ target ≤ 1 / 4 ∧ risk / 6 ≤ target := by
  cases kind with
  | infiniteRank => cases htarget
  | noTool =>
    have heq : risk / 2 = target := Option.some.inj htarget
    subst target
    have hr := hvalid.1
    have hq := hvalid.2
    exact ⟨by linarith, by linarith, by linarith⟩
  | finiteBad depth =>
    have heq : controllerTarget risk depth.val = target := Option.some.inj htarget
    subst target
    exact ⟨controllerTarget_pos risk depth.val, controllerTarget_le_quarter risk depth.val,
      controllerTarget_floor risk hvalid.1 hvalid.2 depth.val depth.pos⟩

/-- The path floor is a theorem of the real update function for every report
and rank-case sequence. It is not an input assumption about reached paths. -/
theorem referenceBudgetPath_valid_floor (events : List ReferenceBudgetEvent) (initial current : ℚ)
    (hvalid : ReferenceBudgetValid initial) (hpath : referenceBudgetPath initial events = some current) :
    ReferenceBudgetValid current ∧ initial / (2 : ℚ) ^ events.length ≤ current := by
  induction events generalizing initial with
  | nil =>
    have heq : initial = current := Option.some.inj hpath
    subst current
    simpa only [List.length_nil, pow_zero, div_one] using (And.intro hvalid (le_refl initial))
  | cons event rest ih =>
    change (referenceBudgetStep event.1 event.2 initial).bind
      (fun child => referenceBudgetPath child rest) = some current at hpath
    obtain ⟨child, hstep, hrestpath⟩ := Option.bind_eq_some_iff.mp hpath
    have hchild := referenceBudgetStep_valid_floor event.1 event.2 initial child hvalid hstep
    have hrest := ih child hchild.1 hrestpath
    refine ⟨hrest.1, ?_⟩
    calc
      initial / (2 : ℚ) ^ (event :: rest).length = (initial / 2) / (2 : ℚ) ^ rest.length := by
        rw [List.length_cons, pow_succ]
        ring
      _ ≤ child / (2 : ℚ) ^ rest.length := div_le_div_of_nonneg_right hchild.2 (by positivity)
      _ ≤ current := hrest.2

theorem referenceBudgetPath_target_floor (events : List ReferenceBudgetEvent) (initial current target : ℚ)
    (hvalid : ReferenceBudgetValid initial) (hpath : referenceBudgetPath initial events = some current)
    (kind : ReferenceBudgetCase) (htarget : referenceBudgetTarget kind current = some target) :
    initial / (6 * (2 : ℚ) ^ events.length) ≤ target := by
  have hp := referenceBudgetPath_valid_floor events initial current hvalid hpath
  have ht := referenceBudgetTarget_valid_floor kind current target hp.1 htarget
  calc
    _ = (initial / (2 : ℚ) ^ events.length) / 6 := by ring
    _ ≤ current / 6 := div_le_div_of_nonneg_right hp.2 (by norm_num)
    _ ≤ target := ht.2.2

theorem referenceBudgetPath_floor_up_to (events : List ReferenceBudgetEvent) (N : ℕ)
    (hlen : events.length ≤ N) (initial current : ℚ)
    (hvalid : ReferenceBudgetValid initial) (hpath : referenceBudgetPath initial events = some current) :
    initial / (2 : ℚ) ^ N ≤ current := by
  have hp := referenceBudgetPath_valid_floor events initial current hvalid hpath
  calc
    _ ≤ initial / (2 : ℚ) ^ events.length :=
      div_le_div_of_nonneg_left hvalid.1.le (by positivity) (pow_le_pow_right₀ (by norm_num) hlen)
    _ ≤ current := hp.2

/-- Original initial allocation R/2 and original C_N = 6*2^(N+1).
The external reference parameter R is rational, as its executable state is. -/
theorem referenceBudgetPath_original_floor (referenceRisk : ℚ) (hpositive : 0 < referenceRisk)
    (hsmall : referenceRisk ≤ 1 / 2) (events : List ReferenceBudgetEvent) (N : ℕ)
    (hlen : events.length ≤ N) (current : ℚ)
    (hpath : referenceBudgetPath (referenceRisk / 2) events = some current) :
    referenceRisk / (2 : ℚ) ^ (N + 1) ≤ current := by
  have hv : ReferenceBudgetValid (referenceRisk / 2) := ⟨by linarith, by linarith⟩
  have h := referenceBudgetPath_floor_up_to events N hlen (referenceRisk / 2) current hv hpath
  simpa only [pow_succ, div_div, mul_comm] using h

theorem referenceBudgetPath_original_target_floor (referenceRisk : ℚ) (hpositive : 0 < referenceRisk)
    (hsmall : referenceRisk ≤ 1 / 2) (events : List ReferenceBudgetEvent) (N : ℕ)
    (hlen : events.length ≤ N) (current target : ℚ)
    (hpath : referenceBudgetPath (referenceRisk / 2) events = some current)
    (kind : ReferenceBudgetCase) (htarget : referenceBudgetTarget kind current = some target) :
    referenceRisk / (6 * (2 : ℚ) ^ (N + 1)) ≤ target := by
  have hv : ReferenceBudgetValid (referenceRisk / 2) := ⟨by linarith, by linarith⟩
  have hp := referenceBudgetPath_valid_floor events (referenceRisk / 2) current hv hpath
  have hfloor := referenceBudgetPath_original_floor referenceRisk hpositive hsmall events N hlen current hpath
  have ht := referenceBudgetTarget_valid_floor kind current target hp.1 htarget
  calc
    _ = (referenceRisk / (2 : ℚ) ^ (N + 1)) / 6 := by ring
    _ ≤ current / 6 := div_le_div_of_nonneg_right hfloor (by norm_num)
    _ ≤ target := ht.2.2

theorem referenceBudgetPath_original_floor_real (referenceRisk : ℚ) (hpositive : 0 < referenceRisk)
    (hsmall : referenceRisk ≤ 1 / 2) (events : List ReferenceBudgetEvent) (N : ℕ)
    (hlen : events.length ≤ N) (current : ℚ)
    (hpath : referenceBudgetPath (referenceRisk / 2) events = some current) :
    (referenceRisk : ℝ) / (2 : ℝ) ^ (N + 1) ≤ (current : ℝ) := by
  have h := (Rat.cast_le (K := ℝ)).mpr
    (referenceBudgetPath_original_floor referenceRisk hpositive hsmall events N hlen current hpath)
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using h

theorem referenceBudgetPath_original_target_floor_real (referenceRisk : ℚ) (hpositive : 0 < referenceRisk)
    (hsmall : referenceRisk ≤ 1 / 2) (events : List ReferenceBudgetEvent) (N : ℕ)
    (hlen : events.length ≤ N) (current target : ℚ)
    (hpath : referenceBudgetPath (referenceRisk / 2) events = some current)
    (kind : ReferenceBudgetCase) (htarget : referenceBudgetTarget kind current = some target) :
    (referenceRisk : ℝ) / (6 * (2 : ℝ) ^ (N + 1)) ≤ (target : ℝ) := by
  have h := (Rat.cast_le (K := ℝ)).mpr
    (referenceBudgetPath_original_target_floor referenceRisk hpositive hsmall events N hlen current target hpath kind htarget)
  simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat] using h

/-- The original real-delta path floor follows from an explicitly calibrated
initial budget. No assertion that an arbitrary real delta/2 is rational is used. -/
theorem referenceBudgetPath_real_delta_floor (delta : ℝ) (initial : ℚ)
    (hvalid : ReferenceBudgetValid initial) (hcalibration : delta / 2 ≤ (initial : ℝ))
    (events : List ReferenceBudgetEvent) (N : ℕ) (hlen : events.length ≤ N) (current : ℚ)
    (hpath : referenceBudgetPath initial events = some current) :
    delta / (2 : ℝ) ^ (N + 1) ≤ (current : ℝ) := by
  have hQ := referenceBudgetPath_floor_up_to events N hlen initial current hvalid hpath
  have hR : (initial : ℝ) / (2 : ℝ) ^ N ≤ (current : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hQ
    simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using h
  calc
    _ = (delta / 2) / (2 : ℝ) ^ N := by rw [pow_succ]; ring
    _ ≤ (initial : ℝ) / (2 : ℝ) ^ N := div_le_div_of_nonneg_right hcalibration (by positivity)
    _ ≤ _ := hR

theorem referenceBudgetPath_real_delta_target_floor (delta : ℝ) (initial : ℚ)
    (hvalid : ReferenceBudgetValid initial) (hcalibration : delta / 2 ≤ (initial : ℝ))
    (events : List ReferenceBudgetEvent) (N : ℕ) (hlen : events.length ≤ N) (current target : ℚ)
    (hpath : referenceBudgetPath initial events = some current) (kind : ReferenceBudgetCase)
    (htarget : referenceBudgetTarget kind current = some target) :
    delta / (6 * (2 : ℝ) ^ (N + 1)) ≤ (target : ℝ) := by
  have hp := referenceBudgetPath_valid_floor events initial current hvalid hpath
  have hf := referenceBudgetPath_real_delta_floor delta initial hvalid hcalibration events N hlen current hpath
  have htQ := (referenceBudgetTarget_valid_floor kind current target hp.1 htarget).2.2
  have htR : (current : ℝ) / 6 ≤ (target : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr htQ
    simpa only [Rat.cast_div, Rat.cast_ofNat] using h
  calc
    _ = (delta / (2 : ℝ) ^ (N + 1)) / 6 := by ring
    _ ≤ (current : ℝ) / 6 := div_le_div_of_nonneg_right hf (by norm_num)
    _ ≤ _ := htR

def referenceQuotaConstant (N : ℕ) : ℚ := 6 * (2 : ℚ) ^ (N + 1)

/-- This is exactly the dyadic condition that the original E_delta certifies
for each tested target: 2*N ≤ 2^E * target. It follows from the budget path. -/
theorem referenceBudgetPath_dyadic_target (referenceRisk : ℚ) (hpositive : 0 < referenceRisk)
    (hsmall : referenceRisk ≤ 1 / 2) (N exponent : ℕ)
    (hqualifies : DyadicQualifies (2 * N * referenceQuotaConstant N) (referenceRisk : ℝ) exponent)
    (events : List ReferenceBudgetEvent) (hlen : events.length ≤ N) (current target : ℚ)
    (hpath : referenceBudgetPath (referenceRisk / 2) events = some current)
    (kind : ReferenceBudgetCase) (htarget : referenceBudgetTarget kind current = some target) :
    (2 * N : ℝ) ≤ (2 : ℝ) ^ exponent * (target : ℝ) := by
  have hC : (0 : ℝ) < (referenceQuotaConstant N : ℝ) := by
    simp only [referenceQuotaConstant, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
    positivity
  have hf : (referenceRisk : ℝ) / (referenceQuotaConstant N : ℝ) ≤ (target : ℝ) := by
    simpa only [referenceQuotaConstant, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat] using
      referenceBudgetPath_original_target_floor_real referenceRisk hpositive hsmall events N hlen current target hpath kind htarget
  have hq : (2 * N : ℝ) * (referenceQuotaConstant N : ℝ) ≤ (2 : ℝ) ^ exponent * (referenceRisk : ℝ) := by
    simpa only [DyadicQualifies, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using hqualifies
  calc
    _ ≤ ((2 : ℝ) ^ exponent * (referenceRisk : ℝ)) / (referenceQuotaConstant N : ℝ) :=
      (le_div_iff₀ hC).mpr hq
    _ = (2 : ℝ) ^ exponent * ((referenceRisk : ℝ) / (referenceQuotaConstant N : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hf (by positivity)

/-- Conservative rationalization preserves the original real-delta dyadic
exponent and proves its tested-target condition on every constructed budget
path. It does not replace R/C_N by the generally false larger delta/C_N. -/
theorem exists_referenceRisk_same_exponent_targets (delta : ℝ) (hdelta : 0 < delta)
    (hsmall : delta ≤ 1 / 2) (N : ℕ) (hN : 0 < N) (exponent : ℕ)
    (hminimal : IsMinimalDyadicExponent (2 * N * referenceQuotaConstant N) delta exponent) :
    ∃ referenceRisk : ℚ, 0 < referenceRisk ∧ referenceRisk ≤ 1 / 2 ∧
      delta / 2 ≤ (referenceRisk : ℝ) ∧ (referenceRisk : ℝ) ≤ delta ∧
      IsMinimalDyadicExponent (2 * N * referenceQuotaConstant N) (referenceRisk : ℝ) exponent ∧
      ∀ (events : List ReferenceBudgetEvent) (_hlen : events.length ≤ N) (current target : ℚ),
        referenceBudgetPath (referenceRisk / 2) events = some current →
        ∀ kind : ReferenceBudgetCase, referenceBudgetTarget kind current = some target →
          (2 * N : ℝ) ≤ (2 : ℝ) ^ exponent * (target : ℝ) := by
  have hC : (0 : ℚ) < 2 * N * referenceQuotaConstant N := by
    have hNQ : (0 : ℚ) < N := by exact_mod_cast hN
    unfold referenceQuotaConstant
    positivity
  obtain ⟨r, hr, hhalf, hrdelta, hsame⟩ := exists_rationalRisk_preserves_minimal_exponent
    (2 * N * referenceQuotaConstant N) hC delta hdelta exponent hminimal
  have hrsmall : r ≤ 1 / 2 := by
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hrdelta.trans hsmall
  refine ⟨r, hr, hrsmall, hhalf, hrdelta, hsame, ?_⟩
  intro events hlen current target hpath kind htarget
  exact referenceBudgetPath_dyadic_target r hr hrsmall N exponent hsame.2.1 events hlen current target hpath kind htarget

end PaperProofs.Statistics
