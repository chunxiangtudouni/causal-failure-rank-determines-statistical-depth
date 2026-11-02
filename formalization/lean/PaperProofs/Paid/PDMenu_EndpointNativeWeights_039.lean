module

public import PaperProofs.Paid.PenaltyProgram
public import PaperProofs.Statistics.PDROC_Mixture_001
public import PaperProofs.Statistics.PDROC_Attainment_001
public import PaperProofs.Common.NativeBellmanExpectation

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open PaperProofs.Statistics.BinarySymmetric.Parameters

noncomputable def freshEndpointTest (P : Parameters) (n k : ℕ) (fee : ℚ) (hfee : 0 ≤ fee)
    (head : (freshInstance n k).Stage) (m : ℕ) :
    ((P.freshInput n k fee hfee).experiment head).AdmissibleRule Bool :=
  P.binarySymmetric.rocEndpointTest m

theorem freshEndpointTest_bayesError (P : Parameters) (n k : ℕ) (fee : ℚ) (hfee : 0 ≤ fee)
    (head : (freshInstance n k).Stage) (m : ℕ) :
    ((P.freshInput n k fee hfee).experiment head).bayesError fairGuessLaw
      (freshEndpointTest P n k fee hfee head m) = ENNReal.ofReal (P.binarySymmetric.endpointError m : ℝ) := by
  exact PaperProofs.Statistics.PDROC.bayesError_of_conditional P.binarySymmetric.experiment fairGuessLaw
    (P.binarySymmetric.rocEndpointTest m) _ (PDROC.rocEndpointTest_conditionalError P.binarySymmetric m)

theorem freshEndpointTest_bayesCharge (P : Parameters) (n k : ℕ) (fee : ℚ) (hfee : 0 ≤ fee)
    (head : (freshInstance n k).Stage) (m : ℕ) :
    ((P.freshInput n k fee hfee).experiment head).bayesObservationCharge fairGuessLaw
      (freshEndpointTest P n k fee hfee head m) = ENNReal.ofReal (P.binarySymmetric.endpointCharge m : ℝ) := by
  exact PaperProofs.Statistics.PDROC.bayesCharge_of_conditional P.binarySymmetric.experiment fairGuessLaw
    (P.binarySymmetric.rocEndpointTest m) _ (PDROC.rocEndpointTest_expectedCharge P.binarySymmetric m)

theorem freshEndpointTest_correctMass (P : Parameters) (n k : ℕ) (fee : ℚ) (hfee : 0 ≤ fee)
    (head : (freshInstance n k).Stage) (m : ℕ) :
    (fairGuessLaw.prod ((P.freshInput n k fee hfee).stageLaw head))
      (BellmanExpectation.headCorrectGate (P.freshInput n k fee hfee) head (freshEndpointTest P n k fee hfee head m)) =
      ENNReal.ofReal (1 - (P.binarySymmetric.endpointError m : ℝ)) := by
  let q := (fairGuessLaw.prod ((P.freshInput n k fee hfee).stageLaw head))
    (BellmanExpectation.headCorrectGate (P.freshInput n k fee hfee) head (freshEndpointTest P n k fee hfee head m))
  have herror := freshEndpointTest_bayesError P n k fee hfee head m
  have hsum : q + ENNReal.ofReal (P.binarySymmetric.endpointError m : ℝ) = 1 := by
    have h := BellmanExpectation.correctMass_add_bayesError (P.freshInput n k fee hfee) head fairGuessLaw
      (freshEndpointTest P n k fee hfee head m)
    rw [herror] at h
    exact h
  have hqle : q ≤ 1 := (le_self_add : q ≤ q + ENNReal.ofReal (P.binarySymmetric.endpointError m : ℝ)).trans hsum.le
  have hqfinite : q ≠ ⊤ := ne_top_of_le_ne_top (by simp) hqle
  have hp : 0 ≤ (P.binarySymmetric.endpointError m : ℝ) := by exact_mod_cast (P.binarySymmetric.endpointError_pos m).le
  have ht := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add hqfinite ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp, ENNReal.toReal_one] at ht
  calc
    _ = ENNReal.ofReal q.toReal := (ENNReal.ofReal_toReal hqfinite).symm
    _ = _ := congrArg ENNReal.ofReal (by linarith)

end PDMenu
