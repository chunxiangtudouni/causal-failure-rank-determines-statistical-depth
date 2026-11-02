module
public import Structure.PA17_TM_RatArithmetic_ReturnHome_037a

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticReturnHome037

open Turing
open PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticBankWalk033

theorem homeCap_eq (j : Nat) : homeCap j=13*j+51 := by
  simp only [homeCap,firstCap,backwardCap_eq]

/-- A SINGLE actual trace preserves the original counter/header/SX/source
fields, every cache record and arbitrary suffix while physically returning
the head to the original header. j is code, all other arguments describe Tape. -/
theorem returnHome_contract (j : Nat) (first : RecordSpec) (later : List RecordSpec)
    (hj : later.length=j) (sx : Bool) (counter nx dx ny dyTail suffix : List Bool) :
    ∃ trace, PSTRTMSeq005.RunsFrom (returnHomeMachine j)
        ⟨0,homeInput sx counter nx dx ny (false::dyTail) first later suffix⟩ trace
        ⟨homePort j,homeOutput sx counter nx dx ny (false::dyTail) first later suffix⟩ ∧
      trace.length≤totalGap (first::later)+2*totalWidth (first::later)+12*j+
        2*bankWidth nx dx ny (false::dyTail)+49 ∧
      ∀ prefixLength chargedL, visitedSpace (returnHomeMachine j) chargedL (trace.take prefixLength) ≤
        chargedL+2*totalGap (first::later)+4*totalWidth (first::later)+24*j+
          4*bankWidth nx dx ny (false::dyTail)+99 := by
  obtain ⟨trace,hr,hl⟩ := returnHome_bounded j first later hj sx counter nx dx ny dyTail suffix
  refine ⟨trace,hr,hl,?_⟩
  intro prefixLength chargedL
  have hs := PSTRTMTrace002.visitedSpace_le (returnHomeMachine j) chargedL (trace.take prefixLength)
  have ht : (trace.take prefixLength).length≤trace.length := by
    simp only [List.length_take]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticReturnHome037
