module

public import RootB234_PrepEntry_StageChannelsPublic_069
public import RootB23_WordOddsBits_Core_001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.ChannelWidth

open PaperProofs.Common.Native PSTRWordBool RationalControllerComputation
open PaperProofs.Statistics
open RootB23.WordOddsBits PSTRTMArithmetic008 PA17TMRatArithmeticNativeSize007

def denominatorProduct (values : List Rat) : Nat := (values.map Rat.den).prod

def denominatorBits (values : List Rat) : Nat :=
  (values.map (fun q => natBits q.den)).sum

theorem denominatorProduct_pos (values : List Rat) : 0 < denominatorProduct values := by
  induction values with
  | nil => decide
  | cons q values ih =>
    exact Nat.mul_pos q.den_pos ih

theorem denominator_dvd_product (values : List Rat) (q : Rat) (present : q ∈ values) :
    q.den ∣ denominatorProduct values :=
  List.dvd_prod (List.mem_map.mpr ⟨q,present,rfl⟩)

theorem denominatorProduct_bits_le (values : List Rat) :
    natBits (denominatorProduct values) ≤ 1 + denominatorBits values := by
  induction values with
  | nil => decide
  | cons q values ih =>
    have step := natBits_mul_le q.den (denominatorProduct values)
    change natBits (q.den * denominatorProduct values) ≤
      1 + (natBits q.den + denominatorBits values)
    omega

theorem abs_denominator (q : Rat) : (|q|).den = q.den := by
  by_cases sign : 0 ≤ q
  · rw [abs_of_nonneg sign]
  · rw [abs_of_neg (lt_of_not_ge sign),Rat.neg_den]

theorem sum_denominator_dvd (values : List Rat) (D : Nat)
    (bounded : ∀ q ∈ values,q.den ∣ D) : values.sum.den ∣ D := by
  induction values with
  | nil => exact one_dvd D
  | cons q values ih =>
    exact (Rat.add_den_dvd_lcm q values.sum).trans
      (Nat.lcm_dvd (bounded q List.mem_cons_self)
        (ih (fun r present => bounded r (List.mem_cons_of_mem q present))))

theorem nonnegative_num_le_twice_den (q : Rat) (nonnegative : 0 ≤ q) (bounded : q ≤ 2) :
    q.num.natAbs ≤ 2*q.den := by
  have sign := Rat.num_nonneg.mpr nonnegative
  have cross := (Rat.le_iff q 2).mp bounded
  norm_num at cross
  have integerBound : (q.num.natAbs : Int) ≤ 2*(q.den : Int) := by
    rw [Int.natAbs_of_nonneg sign]
    exact cross
  exact_mod_cast integerBound

/-- A bounded nonnegative rational sharing D has additive canonical width. -/
theorem width_le_common_denominator (q : Rat) (D : Nat) (positive : 0 < D)
    (divides : q.den ∣ D) (nonnegative : 0 ≤ q) (bounded : q ≤ 2) :
    RatInput.Encoder.fieldSize q ≤ 2 + 2*natBits D := by
  have denominator := Nat.le_of_dvd positive divides
  have numerator := (nonnegative_num_le_twice_den q nonnegative bounded).trans
    (Nat.mul_le_mul_left 2 denominator)
  have numeratorBits := (natBits_mono numerator).trans (natBits_mul_le 2 D)
  have denBits := natBits_mono denominator
  rw [ratInput_fieldSize_eq]
  unfold width
  have twoBits : natBits 2 = 2 := rfl
  omega

end RootB234.ChannelWidth
