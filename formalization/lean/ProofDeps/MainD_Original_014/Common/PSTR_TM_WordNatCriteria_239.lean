module
public import Common.PSTR_TM_ThresholdOutputBits_238

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMWordNatCriteria239
open PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Statistics
open scoped BigOperators

/-! Exact ORIGINAL word predicates expressed through the already existing
raw Nat sub/mul/le operators. These are value/codec bridges, not an actual
word program or free marshaling. All fields must still be parsed, retained,
copied, serialized and consumed by real calls. No new subtraction operator
is implemented: mature A17 Sub016f handles the required D-N on ALL inputs. -/

def complementNumerator (p : Rat) : Nat := p.den-p.num.natAbs

theorem numerator_lt_den (p : Rat) (hp : 0 < p) (hone : p < 1) : p.num.natAbs < p.den := by
  have hn := Rat.num_pos.mpr hp
  have h := Rat.num_lt_denom_iff.mpr hone
  have ha : (p.num.natAbs : Int) = p.num := Int.natAbs_of_nonneg hn.le
  rw [←ha] at h
  exact_mod_cast h

theorem complement_pos (p : Rat) (hp : 0 < p) (hone : p < 1) : 0 < complementNumerator p :=
  Nat.sub_pos_of_lt (numerator_lt_den p hp hone)

theorem one_sub_fields (p : Rat) (hp : 0 < p) (hone : p < 1) :
    (1-p).num.natAbs = complementNumerator p ∧ (1-p).den = p.den := by
  have hn := Rat.num_pos.mpr hp
  have ha : (p.num.natAbs : Int) = p.num := Int.natAbs_of_nonneg hn.le
  have hlt := numerator_lt_den p hp hone
  have hnum : (1-p).num = (complementNumerator p : Int) := by
    rw [PSTRTMArithmetic008.one_sub_num,complementNumerator,Int.natCast_sub hlt.le,ha]
  exact ⟨by rw [hnum]; exact Int.natAbs_natCast _,PSTRTMArithmetic008.one_sub_den p⟩

theorem inverse_datum_bits (r : Rat) (hr : 0 < r) :
    encodeDatum (.rational r⁻¹) = [true,false]++encodeNat r.den++encodeNat r.num.natAbs := by
  have hn := Rat.num_pos.mpr hr
  have hs : r.num.sign = 1 := Int.sign_eq_one_iff_pos.mpr hn
  have hnum : (r⁻¹).num = (r.den : Int) := by rw [Rat.num_inv,hs,Int.one_mul]
  have hden : (r⁻¹).den = r.num.natAbs := by
    simp only [Rat.den_inv,ne_of_gt hn,ite_false]
  have hpos : ¬r⁻¹ < 0 := not_lt.mpr (inv_pos.mpr hr).le
  simp [encodeDatum,hnum,hden,hpos]

theorem one_sub_ratio (p : Rat) (hp : 0 < p) (hone : p < 1) :
    1-p = (complementNumerator p : Rat)/p.den := by
  have hd : 0 < (p.den : Rat) := Nat.cast_pos.mpr p.den_pos
  calc
    1-p = 1-(p.num.natAbs : Rat)/p.den :=
      congrArg (fun value : Rat => 1-value) (PSTRTMThresholdSeed155.positive_ratio p hp)
    _ = (p.den : Rat)/p.den-(p.num.natAbs : Rat)/p.den := by rw [div_self (ne_of_gt hd)]
    _ = ((p.den : Rat)-(p.num.natAbs : Rat))/p.den := (sub_div _ _ _).symm
    _ = _ := by rw [complementNumerator,Nat.cast_sub (numerator_lt_den p hp hone).le]

theorem lower_ratio (p : Rat) (hp : 0 < p) (hone : p < 1) :
    p/(1-p) = (p.num.natAbs : Rat)/(complementNumerator p : Rat) := by
  have hd : 0 < (p.den : Rat) := Nat.cast_pos.mpr p.den_pos
  calc
    p/(1-p) = ((p.num.natAbs : Rat)/p.den)/((complementNumerator p : Rat)/p.den) :=
      congrArg₂ (fun a b : Rat => a/b) (PSTRTMThresholdSeed155.positive_ratio p hp) (one_sub_ratio p hp hone)
    _ = _ := div_div_div_cancel_right₀ (ne_of_gt hd) _ _

theorem upper_ratio (p : Rat) (hp : 0 < p) (hone : p < 1) :
    (1-p)/p = (complementNumerator p : Rat)/(p.num.natAbs : Rat) := by
  have hd : 0 < (p.den : Rat) := Nat.cast_pos.mpr p.den_pos
  calc
    (1-p)/p = ((complementNumerator p : Rat)/p.den)/((p.num.natAbs : Rat)/p.den) :=
      congrArg₂ (fun a b : Rat => a/b) (one_sub_ratio p hp hone) (PSTRTMThresholdSeed155.positive_ratio p hp)
    _ = _ := div_div_div_cancel_right₀ (ne_of_gt hd) _ _

theorem lower_nat_iff (q p : Rat) (hq : 0 < q) (hp : 0 < p) (hone : p < 1) :
    q ≤ p/(1-p) ↔ q.num.natAbs*complementNumerator p ≤ q.den*p.num.natAbs := by
  have hb : 0 < (q.den : Rat) := Nat.cast_pos.mpr q.den_pos
  have hd : 0 < (complementNumerator p : Rat) := Nat.cast_pos.mpr (complement_pos p hp hone)
  have he : (q ≤ p/(1-p)) =
      ((q.num.natAbs : Rat)/q.den ≤ (p.num.natAbs : Rat)/(complementNumerator p : Rat)) :=
    congrArg₂ (fun a b : Rat => a ≤ b) (PSTRTMThresholdSeed155.positive_ratio q hq) (lower_ratio p hp hone)
  calc
    _ ↔ q.num.natAbs*complementNumerator p ≤ p.num.natAbs*q.den := by
      rw [he,div_le_div_iff₀ hb hd]
      norm_cast
    _ ↔ _ := by rw [Nat.mul_comm p.num.natAbs q.den]

theorem upper_nat_iff (q p : Rat) (hq : 0 < q) (hp : 0 < p) (hone : p < 1) :
    (1-p)/p ≤ q ↔ q.den*complementNumerator p ≤ q.num.natAbs*p.num.natAbs := by
  have hb : 0 < (q.den : Rat) := Nat.cast_pos.mpr q.den_pos
  have hc : 0 < (p.num.natAbs : Rat) := Nat.cast_pos.mpr (PSTRTMThresholdSeed155.numerator_pos p hp)
  have he : ((1-p)/p ≤ q) =
      ((complementNumerator p : Rat)/(p.num.natAbs : Rat) ≤ (q.num.natAbs : Rat)/q.den) :=
    congrArg₂ (fun a b : Rat => a ≤ b) (upper_ratio p hp hone) (PSTRTMThresholdSeed155.positive_ratio q hq)
  calc
    _ ↔ complementNumerator p*q.den ≤ q.num.natAbs*p.num.natAbs := by
      rw [he,div_le_div_iff₀ hc hb]
      norm_cast
    _ ↔ _ := by rw [Nat.mul_comm (complementNumerator p) q.den]

theorem wordHits_nat_iff (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord)
    (ht : 0 < target) (hquarter : target ≤ 1/4) :
    E.rationalWordHits target word = true ↔
      (E.rationalWordOdds word).num.natAbs*complementNumerator target ≤
        (E.rationalWordOdds word).den*target.num.natAbs ∨
      (E.rationalWordOdds word).den*complementNumerator target ≤
        (E.rationalWordOdds word).num.natAbs*target.num.natAbs := by
  have hone : target < 1 := hquarter.trans_lt (by norm_num)
  simp only [BinaryExperiment.rationalWordHits,decide_eq_true_eq]
  exact or_congr (lower_nat_iff _ _ (E.rationalWordOdds_pos word) ht hone)
    (upper_nat_iff _ _ (E.rationalWordOdds_pos word) ht hone)

theorem wordMAP_nat_iff (E : BinaryExperiment) (word : E.StoppedWord) :
    E.rationalWordMAP word = true ↔ (E.rationalWordOdds word).den ≤ (E.rationalWordOdds word).num.natAbs := by
  simp only [BinaryExperiment.rationalWordMAP,decide_eq_true_eq]
  have hb : 0 < ((E.rationalWordOdds word).den : Rat) := Nat.cast_pos.mpr (E.rationalWordOdds word).den_pos
  have he : (1 ≤ E.rationalWordOdds word) =
      (1 ≤ ((E.rationalWordOdds word).num.natAbs : Rat)/(E.rationalWordOdds word).den) :=
    congrArg (fun q : Rat => 1 ≤ q) (PSTRTMThresholdSeed155.positive_ratio _ (E.rationalWordOdds_pos word))
  rw [he,le_div_iff₀ hb,one_mul]
  norm_cast

theorem wordOdds_positive_product (E : BinaryExperiment) (word : E.StoppedWord) :
    E.rationalWordOdds word = E.prior true*(E.prior false)⁻¹*
      (∏ k : Fin word.1, E.channel true (word.2 k)*(E.channel false (word.2 k))⁻¹) := by
  simp only [BinaryExperiment.rationalWordOdds,div_eq_mul_inv]
  ring

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMWordNatCriteria239
