module
public import Structure.PA17_TM_Division_Front_007a
public import Structure.PA17_TM_Division_Loop_002h

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionFrontLayout011
open PaperProofs.Common.Native.RationalControllerComputation

def originalBits (a b : Nat) : List Bool :=
  PA17TMDivisionCodec003.firstBits (PA17TMDivisionFront007.frontPairs a b)

def actualResident (a b : Nat) : List (Bool × Bool) :=
  PA17TMDivisionInit004.residentHigh (PA17TMDivisionFront007.frontPairs a b)

theorem original_archive (a b : Nat) :
    PA17TMDivisionInit004.archivePairs (PA17TMDivisionFront007.frontPairs a b) =
      PA17TMDivisionLoop002.archiveFor (originalBits a b).reverse [] := by
  simp only [PA17TMDivisionLoop002.archiveFor, List.reverse_reverse, List.map_nil,
    List.append_nil, originalBits, PA17TMDivisionCodec003.firstBits,
    PA17TMDivisionInit004.archivePairs, List.map_map, Function.comp_def]

/-- Only the whole-tape identities of the two actual producers are used.
No nonblank data is erased, no tape is copied and no head is relocated. -/
theorem front_loop_tape (a b : Nat) :
    (PA17TMDivisionFront007.frontFinal a b).Tape =
      PA17TMDivisionLoop002.loopTape []
        (PA17TMDivisionLoop002.archiveFor (originalBits a b).reverse [])
        (actualResident a b) [] := by
  rw [PA17TMDivisionFront007.front_final_tape, original_archive]
  exact (PA17TMDivisionLoop002.loopTape_original_layout _ _).symm

theorem originalBits_length (a b : Nat) :
    (originalBits a b).length = max (natBits a) (natBits b) := by
  rw [originalBits, PA17TMDivisionCodec003.firstBits_length, PA17TMDivisionFront007.frontPairs_length]

theorem originalBits_value (a b : Nat) :
    PSTRTMIncrement009.valueDigits (originalBits a b) = a := by
  rw [originalBits, PA17TMDivisionCodec003.firstBits_value,
    (PA17TMDivisionFront007.frontPairs_values a b).1]

theorem actualResident_firstValue (a b : Nat) :
    PSTRTMBinaryAdd024.firstValue (actualResident a b) = 0 :=
  PA17TMDivisionFront007.front_resident_firstValue a b

theorem actualResident_secondValue (a b : Nat) :
    PSTRTMBinaryAdd024.secondValue (actualResident a b) = b :=
  PA17TMDivisionFront007.front_resident_secondValue a b

theorem actualResident_length (a b : Nat) :
    (actualResident a b).length = max (natBits a) (natBits b) + 1 :=
  PA17TMDivisionFront007.front_resident_length a b

theorem originalMSB_length_le (a b : Nat) :
    (originalBits a b).reverse.length ≤ (actualResident a b).length := by
  rw [List.length_reverse, originalBits_length, actualResident_length]
  omega

/-- The original zero-divisor branch is read from the initial comparison
of the actual zero remainder against the actual resident divisor track. -/
theorem actual_zeroMode (a b : Nat) :
    decide ((PSTRTMCompareCode054.resultRelation 0 (actualResident a b)).val = 0) =
      decide (b = 0) := by
  rw [PSTRTMCompareValue056.resultRelation_classify,
    actualResident_firstValue, actualResident_secondValue]
  by_cases hb : b = 0
  · simp [PSTRTMCompareValue056.classify, hb]
  · have hp : 0 < b := Nat.pos_of_ne_zero hb
    have hn : (0 : Nat) ≠ b := by omega
    simp [PSTRTMCompareValue056.classify, hb, hp, hn]

theorem original_max_room (a b : Nat) :
    max (natBits a) (natBits b) + 2 ≤ natBits a + natBits b + 1 := by
  have ha : 1 ≤ natBits a := Nat.succ_le_succ (Nat.zero_le (Nat.log2 a))
  have hb : 1 ≤ natBits b := Nat.succ_le_succ (Nat.zero_le (Nat.log2 b))
  rcases le_total (natBits a) (natBits b) with hab | hba
  · rw [max_eq_right hab]
    omega
  · rw [max_eq_left hba]
    omega

theorem originalInput_length (a b : Nat) :
    (encodeNat a ++ encodeNat b).length = 2 * (natBits a + natBits b + 1) := by
  simp only [List.length_append, PSTRTMLength004.encodeNat_length]
  omega

theorem originalSize_positive (a b : Nat) : 1 ≤ natBits a + natBits b + 1 := by
  omega

/-- All input geometry and the real initial comparison mode are produced
from the original two naturals, without extra loop-entry qualifications. -/
theorem original_loop_entry (a b : Nat) :
    (PA17TMDivisionFront007.frontFinal a b).Tape =
      PA17TMDivisionLoop002.loopTape []
        (PA17TMDivisionLoop002.archiveFor (originalBits a b).reverse [])
        (actualResident a b) [] ∧
    PSTRTMIncrement009.valueDigits (originalBits a b) = a ∧
    PSTRTMBinaryAdd024.firstValue (actualResident a b) = 0 ∧
    PSTRTMBinaryAdd024.secondValue (actualResident a b) = b ∧
    (originalBits a b).length = max (natBits a) (natBits b) ∧
    (actualResident a b).length = max (natBits a) (natBits b) + 1 ∧
    (originalBits a b).reverse.length ≤ (actualResident a b).length ∧
    decide ((PSTRTMCompareCode054.resultRelation 0 (actualResident a b)).val = 0) = decide (b = 0) :=
  ⟨front_loop_tape a b, originalBits_value a b, actualResident_firstValue a b,
    actualResident_secondValue a b, originalBits_length a b, actualResident_length a b,
    originalMSB_length_le a b, actual_zeroMode a b⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionFrontLayout011
