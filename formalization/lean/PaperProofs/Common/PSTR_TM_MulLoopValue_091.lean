module
public import PaperProofs.Common.PSTR_TM_MulLoopLift_090
public import PaperProofs.Common.PSTR_TM_Canonical_020

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulLoopValue091
open PaperProofs.Common.Native.RationalControllerComputation
local notation "Triple" => PSTRTMMulPassCode079.Triple
local notation "CVal" => PSTRTMMulPassCode079.cValue
local notation "AVal" => PSTRTMMulPassCode079.aValue
local notation "BVal" => PSTRTMMulPassCode079.bValue

def halfControl (triples : List Triple) : Fin 4 :=
  PSTRTMMulHalfCode082.finalControl (PSTRTMMulHalfCode082.control false false) triples.reverse
def lowBit (triples : List Triple) : Bool := PSTRTMMulHalfCode082.higher (halfControl triples)
def half (triples : List Triple) : List Triple := PSTRTMMulHalfCode082.halfTriples triples
def padded (triples : List Triple) : List Triple := PSTRTMMulAppendCode086.paddedTriples (half triples)
def passControl (triples : List Triple) : Fin 8 := PSTRTMMulPassCode079.control (lowBit triples) false false
def nextTriples (triples : List Triple) : List Triple := PSTRTMMulPassCode079.resultTriples (passControl triples) (padded triples)

theorem half_length (triples : List Triple) : (half triples).length=triples.length := by
  simp only [half,PSTRTMMulHalfCode082.halfTriples,List.length_reverse,PSTRTMMulHalfValue083.result_length]
theorem padded_length (triples : List Triple) : (padded triples).length=triples.length+1 := by
  simp only [padded,PSTRTMMulAppendCode086.paddedTriples,List.length_append,List.length_cons,List.length_nil,half_length]
theorem next_length (triples : List Triple) : (nextTriples triples).length=triples.length+1 := by
  rw [nextTriples,PSTRTMMulPassValue080.result_length,padded_length]

theorem zero_iff (triples : List Triple) : halfControl triples=0 ↔ BVal triples=0 :=
  PSTRTMMulHalfValue083.actual_zero_iff triples
theorem low_bit (triples : List Triple) : lowBit triples=(BVal triples).testBit 0 :=
  PSTRTMMulHalfValue083.actual_low_bit triples

theorem halve_identity (triples : List Triple) : 2*BVal (half triples)+(lowBit triples).toNat=BVal triples := by
  have hb := PSTRTMMulHalfValue083.bValue_reverse_result (PSTRTMMulHalfCode082.control false false) triples.reverse
  rw [(PSTRTMMulHalfValue083.control_specs false false).1] at hb
  simp only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero,List.reverse_reverse] at hb
  change 2*BVal (half triples)+(lowBit triples).toNat=BVal triples at hb
  exact hb

theorem next_values (triples : List Triple) :
    CVal (nextTriples triples)=CVal triples+(lowBit triples).toNat*AVal triples ∧
    AVal (nextTriples triples)=2*AVal triples ∧ BVal (nextTriples triples)=BVal triples/2 := by
  have hv := PSTRTMMulPassValue080.actual_padded_pass_values (lowBit triples) (half triples)
  have hh := PSTRTMMulHalfValue083.half_values triples
  change CVal (half triples)=CVal triples ∧ AVal (half triples)=AVal triples ∧ BVal (half triples)=BVal triples/2 at hh
  change CVal (nextTriples triples)=CVal (half triples)+(lowBit triples).toNat*AVal (half triples) ∧
    AVal (nextTriples triples)=2*AVal (half triples) ∧ BVal (nextTriples triples)=BVal (half triples) at hv
  rw [hh.1,hh.2.1,hh.2.2] at hv
  exact hv

/-- The actual pass starts only AFTER the actual allocator087 has written
the high zero tuple. Both overflow flags are false as facts of that tape. -/
theorem no_overflow (triples : List Triple) :
    PSTRTMMulPassCode079.finalControl (passControl triples) (padded triples)=passControl triples := by
  have hz := PSTRTMMulPassValue080.appended_zero_noOverflow (passControl triples) (half triples)
  have hm := PSTRTMMulPassValue080.final_mode (passControl triples) (padded triples)
  have hs := PSTRTMMulPassValue080.control_specs (lowBit triples) false false
  change PSTRTMMulPassCode079.aCarry (PSTRTMMulPassCode079.finalControl (passControl triples) (padded triples))=false ∧
    PSTRTMMulPassCode079.cCarry (PSTRTMMulPassCode079.finalControl (passControl triples) (padded triples))=false at hz
  change PSTRTMMulPassCode079.mode (passControl triples)=lowBit triples ∧
    PSTRTMMulPassCode079.aCarry (passControl triples)=false ∧ PSTRTMMulPassCode079.cCarry (passControl triples)=false at hs
  rw [←PSTRTMMulPassValue080.control_eta (PSTRTMMulPassCode079.finalControl (passControl triples) (padded triples))]
  change PSTRTMMulPassCode079.control _ _ _=passControl triples
  rw [hz.1,hz.2,hm,hs.1]
  rfl

theorem accumulator_invariant (triples : List Triple) :
    CVal (nextTriples triples)+AVal (nextTriples triples)*BVal (nextTriples triples)=
      CVal triples+AVal triples*BVal triples := by
  have hv := next_values triples
  have hh := halve_identity triples
  have hd := (PSTRTMMulHalfValue083.half_values triples).2.2
  change BVal (half triples)=BVal triples/2 at hd
  rw [hd] at hh
  rw [hv.1,hv.2.1,hv.2.2]
  nlinarith

theorem bValue_lt_width (triples : List Triple) : BVal triples<2^triples.length := by
  simpa only [PSTRTMMulPassCode079.bValue,List.length_map] using
    PSTRTMCanonical020.valueDigits_lt (triples.map (fun (_,_,b) => b))

/-- The bound is a proof witness from original width, never a supplied
runtime fuel, counter or multiplier-value loop. Each actual step halves B. -/
theorem next_capacity (triples : List Triple) (fuel : Nat) (h : BVal triples<2^(fuel+1)) :
    BVal (nextTriples triples)<2^fuel := by
  rw [(next_values triples).2.2]
  rw [Nat.pow_succ] at h
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulLoopValue091
