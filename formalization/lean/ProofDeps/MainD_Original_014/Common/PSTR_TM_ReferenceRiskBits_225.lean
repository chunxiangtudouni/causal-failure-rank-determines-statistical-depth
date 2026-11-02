module
public import Common.PSTR_TM_Arithmetic_008
public import Common.PSTR_TM_ThresholdDenominatorRaw_202
public import PaperProofs.Statistics.ReferenceBudgets

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMReferenceRiskBits225
open PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Statistics

/-! Canonical-denominator growth of the ORIGINAL risk update functions.
These are mathematical input-width bounds, not implementations of Rat
arithmetic. Actual multiply/compare/gcd/division/transport remain required.
The no-tool error remains NONE termination; no zero continuation is added. -/

theorem den_mul_nat_le (risk : Rat) (factor : Nat) :
    (risk*(factor : Rat)).den ≤ risk.den := by
  rw [Rat.den_mul]
  simp only [Rat.den_natCast,Nat.mul_one]
  exact Nat.div_le_self _ _

theorem den_half_le (risk : Rat) : (risk/2).den ≤ 2*risk.den := by
  rw [div_eq_mul_inv,Rat.den_mul]
  have hh : ((2 : Rat)⁻¹).den = 2 := by norm_num [Rat.den_inv]
  rw [hh]
  exact (Nat.div_le_self _ _).trans (by omega)

theorem bad_expression_mul_nat (risk : Rat) (depth : Nat) :
    risk/(2*controllerTarget risk depth) = risk*((2*(controllerB risk depth+1) : Nat) : Rat) := by
  rw [PSTRTMThresholdDenominatorRaw202.target_denominator_identity,div_eq_mul_inv]
  simp only [one_div,mul_inv_rev,inv_inv]
  push_cast
  ring

theorem valid_den_ge_four (risk : Rat) (hr : 0 < risk) (hq : risk ≤ 1/4) : 4 ≤ risk.den := by
  have hn : 0 < risk.num := Rat.num_pos.mpr hr
  have hc := (Rat.le_iff risk (1/4)).mp hq
  norm_num at hc
  have hd : (4 : Int) ≤ (risk.den : Int) := by omega
  exact_mod_cast hd

theorem badRisk_den_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hq : risk ≤ 1/4) :
    (controllerBadRisk risk (controllerTarget risk depth)).den ≤ risk.den := by
  by_cases hc : (1/4 : Rat) ≤ risk/(2*controllerTarget risk depth)
  · rw [controllerBadRisk,min_eq_left hc]
    have hd : (1/4 : Rat).den = 4 := by
      norm_num [div_eq_mul_inv,Rat.den_mul,Rat.den_inv]
    rw [hd]
    exact valid_den_ge_four risk hr hq
  · rw [controllerBadRisk,min_eq_right (le_of_lt (lt_of_not_ge hc)),bad_expression_mul_nat]
    exact den_mul_nat_le _ _

theorem reference_step_den_le (kind : ReferenceBudgetCase) (error : Bool) (risk child : Rat)
    (hv : ReferenceBudgetValid risk) (hs : referenceBudgetStep kind error risk = some child) :
    child.den ≤ 2*risk.den := by
  cases kind with
  | infiniteRank =>
    have he : risk = child := Option.some.inj hs
    subst child
    omega
  | noTool =>
    cases error with
    | false =>
      have he : risk/2 = child := Option.some.inj hs
      subst child
      exact den_half_le risk
    | true => cases hs
  | finiteBad depth =>
    cases error with
    | false =>
      have he : risk/2 = child := Option.some.inj hs
      subst child
      exact den_half_le risk
    | true =>
      have he : controllerBadRisk risk (controllerTarget risk depth.val) = child := Option.some.inj hs
      subst child
      have hb := badRisk_den_le risk depth.val hv.1 hv.2
      omega

theorem reference_path_den_le (events : List ReferenceBudgetEvent) (initial current : Rat)
    (hv : ReferenceBudgetValid initial) (hp : referenceBudgetPath initial events = some current) :
    current.den ≤ 2^events.length*initial.den := by
  induction events generalizing initial with
  | nil =>
    have he : initial = current := Option.some.inj hp
    subst current
    simp
  | cons event later ih =>
    change (referenceBudgetStep event.1 event.2 initial).bind
      (fun child => referenceBudgetPath child later) = some current at hp
    obtain ⟨child,hstep,hpath⟩ := Option.bind_eq_some_iff.mp hp
    have hchild := referenceBudgetStep_valid_floor event.1 event.2 initial child hv hstep
    have hrest := ih child hchild.1 hpath
    have hden := reference_step_den_le event.1 event.2 initial child hv hstep
    calc
      current.den ≤ 2^later.length*child.den := hrest
      _ ≤ 2^later.length*(2*initial.den) := Nat.mul_le_mul_left _ hden
      _ = 2^(event::later).length*initial.den := by rw [List.length_cons,pow_succ]; ring

private theorem natBits_pow_two_mul_le (n k : Nat) : natBits (2^k*n) ≤ natBits n+k := by
  have hn := PSTRTMCodec001.natBits_bound n
  have hp := Nat.mul_lt_mul_of_pos_left hn (by positivity : 0 < 2^k)
  apply PSTRTMArithmetic008.natBits_le_of_lt_pow
  · simpa only [Nat.pow_add,Nat.mul_comm] using hp
  · have hb : 0 < natBits n := by simp [natBits]
    omega

theorem reference_path_den_bits_le (events : List ReferenceBudgetEvent) (initial current : Rat)
    (hv : ReferenceBudgetValid initial) (hp : referenceBudgetPath initial events = some current) :
    natBits current.den ≤ natBits initial.den+events.length :=
  (PSTRTMArithmetic008.natBits_mono (reference_path_den_le events initial current hv hp)).trans
    (natBits_pow_two_mul_le initial.den events.length)

theorem valid_num_abs_le_den (risk : Rat) (hv : ReferenceBudgetValid risk) : risk.num.natAbs ≤ risk.den := by
  have hn : 0 ≤ risk.num := Rat.num_nonneg.mpr hv.1.le
  have hq : risk ≤ 1 := hv.2.trans (by norm_num)
  have hm := Rat.num_le_denom_iff.mpr hq
  have ha : (risk.num.natAbs : Int) ≤ (risk.den : Int) := by
    rw [Int.natAbs_of_nonneg hn]
    exact hm
  exact_mod_cast ha

/-- Every successful original budget path has LINEAR event-count encoded
risk width. The original labelled paths include every good/bad rank case;
their extraction from a native run stays a separate parent obligation. -/
theorem reference_path_datumBits_le (events : List ReferenceBudgetEvent) (initial current : Rat)
    (hv : ReferenceBudgetValid initial) (hp : referenceBudgetPath initial events = some current) :
    PSTRTMLength004.datumBits (.rational current) ≤
      4*(natBits initial.den+events.length)+4 := by
  have hvalid := (referenceBudgetPath_valid_floor events initial current hv hp).1
  have hnum := PSTRTMArithmetic008.natBits_mono (valid_num_abs_le_den current hvalid)
  have hden := reference_path_den_bits_le events initial current hv hp
  simp only [PSTRTMLength004.datumBits]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMReferenceRiskBits225
