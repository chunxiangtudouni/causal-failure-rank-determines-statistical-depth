module
public import Common.PSTR_TM_ThresholdDenominatorRaw_202

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdOddsFields211
open PaperProofs.Common.Native.RationalControllerComputation

def oddsValue (risk : Rat) (depth : Nat) : Nat :=
  4*(PaperProofs.Statistics.controllerB risk depth + 1) - 1

theorem oddsValue_pos (risk : Rat) (depth : Nat) : 0 < oddsValue risk depth := by
  dsimp only [oddsValue]
  omega

/-- Original odds expressions have special canonical fields; using this
identity still requires the actual D-1 producer and physical serializers. -/
theorem controller_odds_identity (risk : Rat) (depth : Nat) :
    (1 - PaperProofs.Statistics.controllerTarget risk depth) /
        PaperProofs.Statistics.controllerTarget risk depth = (oddsValue risk depth : Rat) := by
  simp only [PSTRTMThresholdDenominatorRaw202.target_denominator_identity,oddsValue]
  let D : Nat := 4*(PaperProofs.Statistics.controllerB risk depth + 1)
  change (1 - 1/(D : Rat))/(1/(D : Rat)) = ((D - 1 : Nat) : Rat)
  have hd : 1 < D := by dsimp only [D]; omega
  have hz : (D : Rat) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  rw [Nat.cast_sub (show 1 ≤ D by omega),Nat.cast_one]
  field_simp [hz]

theorem controller_inverse_odds_identity (risk : Rat) (depth : Nat) :
    PaperProofs.Statistics.controllerTarget risk depth /
        (1 - PaperProofs.Statistics.controllerTarget risk depth) = 1/(oddsValue risk depth : Rat) := by
  calc
    PaperProofs.Statistics.controllerTarget risk depth /
        (1 - PaperProofs.Statistics.controllerTarget risk depth) =
        ((1 - PaperProofs.Statistics.controllerTarget risk depth) /
          PaperProofs.Statistics.controllerTarget risk depth)⁻¹ := (inv_div _ _).symm
    _ = 1/(oddsValue risk depth : Rat) := by rw [controller_odds_identity,one_div]

theorem odds_datum_bits (risk : Rat) (depth : Nat) :
    encodeDatum (.rational ((1 - PaperProofs.Statistics.controllerTarget risk depth) /
        PaperProofs.Statistics.controllerTarget risk depth)) =
      [true,false] ++ encodeNat (oddsValue risk depth) ++ encodeNat 1 := by
  rw [controller_odds_identity]
  have hn : ¬(oddsValue risk depth : Rat) < 0 := not_lt.mpr (Nat.cast_nonneg _)
  simp [encodeDatum,hn]

theorem inverse_odds_datum_bits (risk : Rat) (depth : Nat) :
    encodeDatum (.rational (PaperProofs.Statistics.controllerTarget risk depth /
        (1 - PaperProofs.Statistics.controllerTarget risk depth))) =
      [true,false] ++ encodeNat 1 ++ encodeNat (oddsValue risk depth) := by
  rw [controller_inverse_odds_identity,one_div]
  have hp := oddsValue_pos risk depth
  have hn : ¬(oddsValue risk depth : Rat)⁻¹ < 0 :=
    not_lt.mpr (inv_nonneg.mpr (Nat.cast_nonneg _))
  simp [encodeDatum,Rat.inv_natCast_num_of_pos hp,Rat.inv_natCast_den_of_pos hp,hn]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdOddsFields211
