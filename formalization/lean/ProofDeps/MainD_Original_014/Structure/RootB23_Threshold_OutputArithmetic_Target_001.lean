module

public import Structure.RootB23_Threshold_BTarget_002

/-! The actual copied-B field is transformed into the canonical target
Rat Datum. Prefix5 creates its own five cells by real relocation; the
single original FALSE guard and the arbitrary external archive survive. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section
namespace RootB23.Threshold.OutputArithmetic.Target
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)

def denominator (n : Nat) : Nat := 4 * (n + 1)

def value (n : Nat) : Rat := 1 / (denominator n : Rat)

def tail (n : Nat) : List Bool := false :: (encodeNat 1 ++ encodeNat (denominator n))

def rawCode : Machine 82 := PSTRTMSeq005.seqMachine
  PSTRTMThresholdDenominatorFrame199.denominatorMachine PSTRTMUnblock018.unblockMachine

def code : Machine 636 := PSTRTMSeq005.seqMachine rawCode PA17TMRatArithmeticPrefix5060.prefixMachine

theorem two_right_blanks (left word : List Bool) :
    Tape.mk₂ left (word ++ [false,false]) = Tape.mk₂ left word := by
  calc
    _ = Tape.mk₂ left (word ++ [false]) := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        PA17TMRatArithmeticPrefix5060.far_false left (word ++ [false])
    _ = _ := PA17TMRatArithmeticPrefix5060.far_false left word

theorem denominator_width (n : Nat) : natBits (denominator n) ≤ natBits n + 3 := by
  have successor := PSTRTMArithmetic008.natBits_add_le n 1
  have unit : natBits 1 = 1 := by decide
  rw [unit] at successor
  have twice := PSTRTMThresholdDenominatorFrame199.double_width (n + 1) (by omega)
  have four := PSTRTMThresholdDenominatorFrame199.double_width (2 * (n + 1)) (by omega)
  have identity : 2 * (2 * (n + 1)) = denominator n := by unfold denominator; omega
  rw [identity, twice] at four
  omega

theorem bits (n : Nat) :
    encodeDatum (.rational (value n)) = PA17TMRatArithmeticPrefix5060.fragment ++ encodeNat (denominator n) := by
  have positive : 0 < denominator n := by unfold denominator; omega
  have numerator : (value n).num = 1 := by
    unfold value
    rw [one_div]
    exact Rat.inv_natCast_num_of_pos positive
  have den : (value n).den = denominator n := by
    unfold value
    rw [one_div]
    exact Rat.inv_natCast_den_of_pos positive
  have nonnegative : 0 ≤ value n := by
    unfold value
    exact div_nonneg (by norm_num) (Nat.cast_nonneg _)
  rw [PA17TMRatArithmeticPrefix5060.fragment_original_datum]
  simp [encodeDatum, not_lt.mpr nonnegative, numerator, den]

theorem true_tag (n : Nat) : encodeDatum (.rational (value n)) = true :: tail n := by
  rw [bits, PA17TMRatArithmeticPrefix5060.fragment_original_datum]
  rfl

private theorem arithmetic_cost (width den : Nat) (small : den + 1 ≤ 4 * (width + 1)) :
    64 * (width + 1) + 32 * (den + 1) ^ 2 + 128 * (den + 1) ^ 2 ≤ 4096 * (width + 1) ^ 2 := by
  have square := Nat.pow_le_pow_left small 2
  nlinarith only [square, Nat.zero_le (width ^ 2)]

/-- A fixed637-label machine, before every arbitrary archive and every
Nat B including zero. It really computes D, unblocks D, relocates it and
writes the complete canonical Rat tag/sign/unit-numerator prefix. -/
theorem bounded (archive : List Bool) (n : Nat) :
    BoundedRun code
      (Tape.mk₂ (false :: archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload n))) 636
      (Tape.mk₂ (false :: archive) (encodeDatum (.rational (value n))))
      (4096 * (natBits n + 1) ^ 2) := by
  have denRun := PSTRTMThresholdDenominatorFrame199.denominator_runsFrom archive n
  have denState : PSTRTMThresholdDenominatorFrame199.denominatorFinal archive n =
      ⟨62, (PSTRTMThresholdDenominatorFrame199.denominatorFinal archive n).Tape⟩ := rfl
  rw [PSTRTMThresholdDenominatorFrame199.denominator_final_tape] at denState
  rw [denState] at denRun
  have denBound : BoundedRun PSTRTMThresholdDenominatorFrame199.denominatorMachine
      (Tape.mk₂ (false :: archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload n))) 62
      (Tape.mk₂ (false :: archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (denominator n))))
      (64 * (natBits n + 1)) :=
    ⟨PSTRTMThresholdDenominatorFrame199.denominatorTrace archive n, denRun,
      PSTRTMThresholdDenominatorFrame199.denominator_length_le archive n⟩
  have rawRun := PA17TMRatArithmeticUnblock004.originalNat_runsFrom (denominator n) archive []
  have rawTime := PA17TMRatArithmeticUnblock004.framed_time_le archive
    (PSTRTMNatValue017.rawPayload (denominator n)) []
  simp only [PSTRTMNatValue017.rawPayload, List.length_ofFn] at rawTime
  have rawBound : BoundedRun PSTRTMUnblock018.unblockMachine
      (Tape.mk₂ (false :: archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (denominator n)))) 19
      (Tape.mk₂ (false :: archive) (encodeNat (denominator n)))
      (32 * (natBits (denominator n) + 1) ^ 2) := by
    refine ⟨PA17TMRatArithmeticUnblock004.framedTrace archive
      (PSTRTMNatValue017.rawPayload (denominator n)) [], ?_, rawTime⟩
    simpa only [PSTRTMUnblock018.state, List.append_nil, two_right_blanks,
      PA17TMRatArithmeticPrefix5060.far_false] using rawRun
  have prefixedRun := PA17TMRatArithmeticPrefix5060.prefix_bounded (denominator n)
    (by unfold denominator; omega) archive
  have combined := (denBound.seq rawBound).seq prefixedRun
  have port : PSTRTMSeq005.rightLabel (a := 82) (553 : Fin 554) = (636 : Fin 637) := by decide
  rw [port, ← bits] at combined
  have small : natBits (denominator n) + 1 ≤ 4 * (natBits n + 1) := by
    have width := denominator_width n
    omega
  exact combined.mono (arithmetic_cost (natBits n) (natBits (denominator n)) small)

end RootB23.Threshold.OutputArithmetic.Target
