module

public import RootB234_ChannelWidth_Den001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.ChannelWidth

open PaperProofs.Common.Native PSTRWordBool RationalControllerComputation
open PaperProofs.Statistics
open RootB23.WordOddsBits PSTRTMLength004

/-- Both original probability vectors, before the archive reversal. -/
def originalChannels (E : BinaryExperiment) : List Rat :=
  PrepEntry.StageChannels.values E false ++ PrepEntry.StageChannels.values E true

def commonDenominator (E : BinaryExperiment) : Nat := denominatorProduct (originalChannels E)

def originalDenominatorBits (E : BinaryExperiment) : Nat := denominatorBits (originalChannels E)

/-- The two actual prepend archives expose aligned entries in this order. -/
def reversePrefixAbs (E : BinaryExperiment) (k : Nat) : Rat :=
  ((((List.finRange E.alphabetSize).reverse.take k).map
    (fun y => |E.channel true y-E.channel false y|)).sum)

def materialLength (E : BinaryExperiment) : Nat :=
  ((rawExperiment E).flatMap encodeDatum).length

theorem original_channel_member (E : BinaryExperiment) (truth : Bool) (y : Fin E.alphabetSize) :
    E.channel truth y ∈ originalChannels E := by
  cases truth with
  | false =>
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨y,by simp,rfl⟩
  | true =>
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨y,by simp,rfl⟩

theorem channel_denominator_dvd (E : BinaryExperiment) (truth : Bool) (y : Fin E.alphabetSize) :
    (E.channel truth y).den ∣ commonDenominator E :=
  denominator_dvd_product _ _ (original_channel_member E truth y)

theorem difference_denominator_dvd (E : BinaryExperiment) (y : Fin E.alphabetSize) :
    (|E.channel true y-E.channel false y|).den ∣ commonDenominator E := by
  rw [abs_denominator]
  exact (Rat.sub_den_dvd_lcm _ _).trans
    (Nat.lcm_dvd (channel_denominator_dvd E true y) (channel_denominator_dvd E false y))

theorem reversePrefix_denominator_dvd (E : BinaryExperiment) (k : Nat) :
    (reversePrefixAbs E k).den ∣ commonDenominator E := by
  apply sum_denominator_dvd
  intro q present
  obtain ⟨y,_inside,rfl⟩ := List.mem_map.mp present
  exact difference_denominator_dvd E y

theorem reversePrefix_nonnegative (E : BinaryExperiment) (k : Nat) :
    0 ≤ reversePrefixAbs E k := by
  apply List.sum_nonneg
  intro q present
  obtain ⟨y,_inside,rfl⟩ := List.mem_map.mp present
  exact abs_nonneg _

theorem full_abs_sum_le_two (E : BinaryExperiment) :
    ((List.finRange E.alphabetSize).map
      (fun y => |E.channel true y-E.channel false y|)).sum ≤ 2 := by
  calc
    _ ≤ ((List.finRange E.alphabetSize).map
      (fun y => E.channel true y+E.channel false y)).sum := by
      apply List.sum_le_sum
      intro y _inside
      exact abs_le.mpr ⟨by linarith [E.channel_pos true y],
        by linarith [E.channel_pos false y]⟩
    _ = 2 := by
      rw [←List.ofFn_eq_map,List.sum_ofFn,Finset.sum_add_distrib,
        E.channel_sum true,E.channel_sum false]
      norm_num

/-- No upper bound on k is needed: take truncates, including at zero. -/
theorem reversePrefix_le_two (E : BinaryExperiment) (k : Nat) :
    reversePrefixAbs E k ≤ 2 := by
  have selectedBound := ((List.take_sublist k (List.finRange E.alphabetSize).reverse).map
    (fun y => |E.channel true y-E.channel false y|)).sum_le_sum (by
      intro q present
      obtain ⟨y,_inside,rfl⟩ := List.mem_map.mp present
      exact abs_nonneg _)
  have full : reversePrefixAbs E k ≤ ((List.finRange E.alphabetSize).map
      (fun y => |E.channel true y-E.channel false y|)).sum := by
    simpa only [reversePrefixAbs,List.map_reverse,List.sum_reverse] using selectedBound
  exact full.trans (full_abs_sum_le_two E)

/-- Additive width in the bits of the original denominators, independent of k. -/
theorem reversePrefix_additive (E : BinaryExperiment) (k : Nat) :
    RatInput.Encoder.fieldSize (reversePrefixAbs E k) ≤ 4+2*originalDenominatorBits E := by
  have rationalBound := width_le_common_denominator (reversePrefixAbs E k) (commonDenominator E)
    (denominatorProduct_pos _) (reversePrefix_denominator_dvd E k)
    (reversePrefix_nonnegative E k) (reversePrefix_le_two E k)
  have bits := denominatorProduct_bits_le (originalChannels E)
  change natBits (commonDenominator E) ≤ 1+originalDenominatorBits E at bits
  omega

theorem denominatorBits_le_fields (values : List Rat) :
    denominatorBits values ≤ (values.flatMap (fun q => encodeDatum (.rational q))).length := by
  induction values with
  | nil => exact Nat.zero_le _
  | cons q values ih =>
    have length := encodeDatum_rational_length q
    simp only [denominatorBits,List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append]
    change natBits q.den + denominatorBits values ≤ _
    omega

theorem rawExperiment_eq_header_channels (E : BinaryExperiment) :
    rawExperiment E = [.natural E.alphabetSize,.rational E.priorOne,.rational E.observationFee] ++
      (originalChannels E).map Datum.rational := by
  simp only [rawExperiment,originalChannels,PrepEntry.StageChannels.values,
    List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_append,List.map_map]
  rfl

theorem originalDenominatorBits_le_material (E : BinaryExperiment) :
    originalDenominatorBits E ≤ materialLength E := by
  have encoded := denominatorBits_le_fields (originalChannels E)
  unfold materialLength
  rw [rawExperiment_eq_header_channels,List.flatMap_append,List.length_append]
  simp only [List.flatMap_map]
  exact encoded.trans (Nat.le_add_left _ _)

theorem reversePrefix_linear (E : BinaryExperiment) (k : Nat) :
    RatInput.Encoder.fieldSize (reversePrefixAbs E k) ≤ 4*(materialLength E+1) := by
  have additive := reversePrefix_additive E k
  have original := originalDenominatorBits_le_material E
  omega

theorem reversePrefix_full_eq_twice_TV (E : BinaryExperiment) :
    reversePrefixAbs E E.alphabetSize = 2*E.channelTV := by
  unfold reversePrefixAbs
  rw [List.take_of_length_le (by simp),List.map_reverse,List.sum_reverse,
    ←List.ofFn_eq_map,List.sum_ofFn]
  have swap : (∑ y : Fin E.alphabetSize,|E.channel true y-E.channel false y|) =
      ∑ y : Fin E.alphabetSize,|E.channel false y-E.channel true y| :=
    Finset.sum_congr rfl (fun y _ => abs_sub_comm _ _)
  rw [swap]
  unfold BinaryExperiment.channelTV
  ring

/-- The original certificate is sumAbs squared divided by two. -/
theorem channelDriftLower_formula (E : BinaryExperiment) :
    E.channelDriftLower = (reversePrefixAbs E E.alphabetSize)^2/2 := by
  rw [reversePrefix_full_eq_twice_TV]
  unfold BinaryExperiment.channelDriftLower
  ring

theorem channelDriftLower_additive (E : BinaryExperiment) :
    RatInput.Encoder.fieldSize E.channelDriftLower ≤ 11+4*originalDenominatorBits E := by
  have base := reversePrefix_additive E E.alphabetSize
  rw [ratInput_fieldSize_eq] at base
  have square := mul_width_le (reversePrefixAbs E E.alphabetSize) (reversePrefixAbs E E.alphabetSize)
  have quotient := div_width_le
    (reversePrefixAbs E E.alphabetSize*reversePrefixAbs E E.alphabetSize) 2
  have twoWidth : width (2 : Rat) = 3 := rfl
  rw [channelDriftLower_formula,ratInput_fieldSize_eq,pow_two]
  omega

theorem channelDriftLower_linear (E : BinaryExperiment) :
    RatInput.Encoder.fieldSize E.channelDriftLower ≤ 16*(materialLength E+1) := by
  have additive := channelDriftLower_additive E
  have original := originalDenominatorBits_le_material E
  omega

end RootB234.ChannelWidth
