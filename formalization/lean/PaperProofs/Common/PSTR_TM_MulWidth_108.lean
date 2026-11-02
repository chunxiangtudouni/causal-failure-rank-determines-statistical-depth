module
public import PaperProofs.Common.PSTR_TM_RawMulResident_099

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulWidth108
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMMulLoopValue091 PSTRTMMulLoopRun093
local notation "Triple" => PSTRTMMulPassCode079.Triple

/-- Actual loop output width growth, derived from its genuine allocation
steps; never extra padding/width supplied in the original input. -/
theorem end_length_le (fuel : Nat) (triples : List Triple) : (endTriples fuel triples).length ≤ triples.length+fuel := by
  induction fuel generalizing triples with
  | zero =>
    simp only [endTriples,half_length,Nat.add_zero]
    exact le_rfl
  | succ fuel ih =>
    by_cases hz : halfControl triples=0
    · simp only [endTriples,hz,↓reduceIte,half_length]
      omega
    · have hn := ih (nextTriples triples)
      rw [next_length] at hn
      simp only [endTriples,hz,↓reduceIte]
      omega

theorem resident_result_length_le (triples : List Triple) : (PSTRTMMulResident094.result triples).length ≤ 2*triples.length := by
  have hl := end_length_le triples.length triples
  change (PSTRTMMulResident094.result triples).length ≤ triples.length+triples.length at hl
  omega

theorem outputTriples_length_le (a b : Nat) :
    (PSTRTMRawMulResident099.outputTriples a b).length ≤ 2*(natBits a+natBits b) := by
  have hl := resident_result_length_le (PSTRTMRawMulResident099.inputTriples a b)
  rw [PSTRTMRawMulResident099.input_length] at hl
  have hp := PSTRTMRawMulResident099.pairs_length_le a b
  change (PSTRTMRawMulResident099.outputTriples a b).length ≤ 2*(PSTRTMRawMulResident099.pairs a b).length at hl
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulWidth108
