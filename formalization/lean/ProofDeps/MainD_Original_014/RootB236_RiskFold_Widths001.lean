module

public import RootB234_ECost_Widths001
public import PaperProofs.Statistics.ReferenceBudgets

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootB236.RiskFold

open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Statistics RationalControllerComputation

def denBits (risk : Rat) : Nat := natBits risk.den

theorem den_mul_le (x y : Rat) : (x*y).den ≤ x.den*y.den := by
  rw [Rat.mul_den]
  exact Nat.div_le_self _ _

theorem den_mul_nat (risk : Rat) (factor : Nat) : (risk*(factor : Rat)).den ≤ risk.den := by
  simpa only [Rat.den_natCast,Nat.mul_one] using den_mul_le risk (factor : Rat)

theorem bits_mul_nat (risk : Rat) (factor : Nat) : denBits (risk*(factor : Rat)) ≤ denBits risk :=
  PSTRTMArithmetic008.natBits_mono (den_mul_nat risk factor)

theorem bits_half (risk : Rat) : denBits (risk/2) ≤ denBits risk+2 := by
  have half : (1/(2 : Rat)).den=2 := by norm_num
  have same : risk/2=risk*(1/2) := by ring
  have bound : (risk/2).den ≤ risk.den*2 := by
    rw [same]
    simpa only [half] using den_mul_le risk (1/2)
  have monotone := PSTRTMArithmetic008.natBits_mono bound
  have product := PA17TMRatArithmeticNativeSize007.natBits_mul_le risk.den 2
  have two : natBits 2=2 := rfl
  change denBits (risk/2) ≤ natBits (risk.den*2) at monotone
  change natBits (risk.den*2) ≤ denBits risk+natBits 2 at product
  rw [two] at product
  omega

theorem original_bad_factor (risk : Rat) (depth : Nat) :
    controllerBadRisk risk (controllerTarget risk depth)=
      min (1/4) (risk*((2*(1+controllerB risk depth) : Nat) : Rat)) := by
  unfold controllerBadRisk controllerTarget
  congr 1
  push_cast
  have positive : (0 : Rat)<1+(controllerB risk depth : Rat) := by positivity
  field_simp
  ring

theorem bits_bad (risk : Rat) (depth : Nat) :
    denBits (controllerBadRisk risk (controllerTarget risk depth)) ≤ denBits risk+3 := by
  rw [original_bad_factor]
  by_cases capped : (1/4 : Rat) ≤ risk*((2*(1+controllerB risk depth) : Nat) : Rat)
  · rw [min_eq_left capped]
    have quarter : denBits (1/(4 : Rat))=3 := by norm_num [denBits,natBits]
    rw [quarter]
    omega
  · rw [min_eq_right (le_of_not_ge capped)]
    exact (bits_mul_nat risk _).trans (Nat.le_add_right _ _)

theorem step_den_bits (kind : ReferenceBudgetCase) (error : Bool) (risk child : Rat)
    (actual : referenceBudgetStep kind error risk=some child) : denBits child ≤ denBits risk+3 := by
  cases kind with
  | infiniteRank =>
    have same : risk=child := Option.some.inj actual
    subst child
    omega
  | noTool =>
    cases error with
    | false =>
      have same : risk/2=child := Option.some.inj actual
      subst child
      have half := bits_half risk
      omega
    | true => cases actual
  | finiteBad depth =>
    cases error with
    | false =>
      have same : risk/2=child := Option.some.inj actual
      subst child
      have half := bits_half risk
      omega
    | true =>
      have same : controllerBadRisk risk (controllerTarget risk depth.val)=child := Option.some.inj actual
      subst child
      exact bits_bad risk depth.val

theorem path_den_bits (events : List ReferenceBudgetEvent) (initial current : Rat)
    (actual : referenceBudgetPath initial events=some current) :
    denBits current ≤ denBits initial+3*events.length := by
  induction events generalizing initial with
  | nil =>
    have same : initial=current := Option.some.inj actual
    subst current
    simp
  | cons event later ih =>
    obtain ⟨child,step,rest⟩ := Option.bind_eq_some_iff.mp actual
    have first := step_den_bits event.1 event.2 initial child step
    have remaining := ih child rest
    simp only [List.length_cons]
    omega

theorem numerator_le_den (risk : Rat) (nonnegative : 0 ≤ risk) (small : risk ≤ 1) :
    risk.num.natAbs ≤ risk.den := by
  have sign : 0 ≤ risk.num := Rat.num_nonneg.mpr nonnegative
  have absolute : ((risk.num.natAbs : Nat) : Rat)=(risk.num : Rat) := by
    have lifted := congrArg (fun value : Int => (value : Rat)) (Int.natAbs_of_nonneg sign)
    simpa only [Int.cast_natCast] using lifted
  have ratio : (risk.num : Rat)/(risk.den : Rat) ≤ 1 := by rw [risk.num_div_den]; exact small
  have positive : (0 : Rat)<(risk.den : Rat) := by exact_mod_cast risk.pos
  have numerator := (div_le_one positive).mp ratio
  rw [←absolute] at numerator
  exact_mod_cast numerator

theorem valid_width (risk : Rat) (valid : ReferenceBudgetValid risk) :
    RatInput.Encoder.fieldSize risk ≤ 2*denBits risk := by
  have bound := PSTRTMArithmetic008.natBits_mono (numerator_le_den risk valid.1.le (by linarith [valid.2]))
  rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
  unfold RootB23.WordOddsBits.width
  change natBits risk.num.natAbs+denBits risk ≤ _
  change natBits risk.num.natAbs ≤ denBits risk at bound
  omega

/-- Every report sequence is allowed; None is genuine termination.
The original valid_floor theorem is used only inside a Some-path proof. -/
theorem original_path_width (budget : Rat) (events : List ReferenceBudgetEvent) (current : Rat)
    (valid : 0<budget ∧ budget≤1/2) (actual : referenceBudgetPath (budget/2) events=some current) :
    RatInput.Encoder.fieldSize current ≤ 2*RatInput.Encoder.fieldSize budget+6*events.length+4 := by
  have initial : ReferenceBudgetValid (budget/2) := by
    constructor <;> linarith [valid.1,valid.2]
  have currentValid := (referenceBudgetPath_valid_floor events (budget/2) current initial actual).1
  have width := valid_width current currentValid
  have path := path_den_bits events (budget/2) current actual
  have half := bits_half budget
  have denominator : denBits budget ≤ RatInput.Encoder.fieldSize budget := by
    rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
    unfold RootB23.WordOddsBits.width denBits
    omega
  omega

end RootB236.RiskFold
