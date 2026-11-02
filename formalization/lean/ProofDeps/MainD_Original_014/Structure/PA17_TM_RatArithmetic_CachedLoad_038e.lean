module
public import Structure.PA17_TM_RatArithmetic_CachedLoad_038d

/-! Canonical original-source EOF departure. Unlike the per-bit route,
this path never writes the original FALSE footer TRUE. A real LEFT reaches
SOURCE END; the frozen original route and frozen forwardAny(FALSE) preserve
that physical FALSE cell all the way to the latest cache marker. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
open Turing
open PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticWidth018 (BoundedRun)

def originalEOFCap (j : Nat) : Nat := 12+forwardCap j+1
def originalEOFMachine (route : PA17TMRatArithmeticFarLoad031.FarRoute) (j : Nat) : Machine (originalEOFCap j) :=
  PSTRTMSeq005.seqMachine (a:=12) (b:=forwardCap j)
    (PA17TMRatArithmeticFarLoad031.finalOutMachine route) (forwardMachine j)
def originalEOFPort (j : Nat) : Fin (originalEOFCap j+1) :=
  PSTRTMSeq005.rightLabel (a:=12) (forwardPort j)

theorem original_EOF_bounded (route : PA17TMRatArithmeticFarLoad031.FarRoute)
    (context : List Bool) (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (correct : PA17TMRatArithmeticFarLoad031.RouteCorrect route context finish cost)
    (j : Nat) (records : List RecordSpec) (hj : records.length=j) (left suffix : List Bool) :
    BoundedRun (originalEOFMachine route j)
      (Tape.mk₂ (false::left) (context++false::bankTail records suffix)) (originalEOFPort j)
      (bankEndAny false (finish left []) records suffix)
      (cost+totalGap records+2*totalWidth records+9*j+3) := by
  have hl : BoundedRun PA17TMRatArithmeticParse002.backOneMachine
      (Tape.mk₂ (false::left) (context++false::bankTail records suffix)) 1
      (Tape.mk₂ left (PA17TMRatArithmeticFarLoad031.fieldWord context [] (bankTail records suffix))) 2 :=
    ⟨PA17TMRatArithmeticParse002.backOneTrace left false (context++false::bankTail records suffix),
      PA17TMRatArithmeticParse002.backOne_runsFrom left false (context++false::bankTail records suffix),by rfl⟩
  have ho := correct.out_run left [] (bankTail records suffix)
  have hf := forwardAny_bounded j false records hj (finish left []) suffix
  have result := (hl.seq ho).seq hf
  have hcost : 2+(2*(([] : List Bool).length)+cost)+(totalGap records+2*totalWidth records+9*j+1)≤
      cost+totalGap records+2*totalWidth records+9*j+3 := by simp only [List.length_nil]; omega
  simpa only [originalEOFMachine,originalEOFCap,PA17TMRatArithmeticFarLoad031.finalOutMachine,originalEOFPort,
    bankStartAny] using result.mono hcost

/-- Every actual prefix is charged using the original visitedSpace. The
ending bit may be FALSE for j0, TRUE for a nonempty bank; no FALSE backward
claim or uncharged destination jump is introduced. -/
theorem original_EOF_contract (route : PA17TMRatArithmeticFarLoad031.FarRoute)
    (context : List Bool) (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (correct : PA17TMRatArithmeticFarLoad031.RouteCorrect route context finish cost)
    (j : Nat) (records : List RecordSpec) (hj : records.length=j) (left suffix : List Bool) (inputLength : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (originalEOFMachine route j)
      ⟨0,Tape.mk₂ (false::left) (context++false::bankTail records suffix)⟩ trace
      ⟨originalEOFPort j,bankEndAny false (finish left []) records suffix⟩ ∧
      trace.length≤cost+totalGap records+2*totalWidth records+9*j+3 ∧
      ∀ k, visitedSpace (originalEOFMachine route j) inputLength (trace.take k) ≤
        inputLength+2*(cost+totalGap records+2*totalWidth records+9*j+3)+1 := by
  obtain ⟨trace,hr,hl⟩ := original_EOF_bounded route context finish cost correct j records hj left suffix
  refine ⟨trace,hr,hl,?_⟩
  intro k
  have hs := PSTRTMTrace002.visitedSpace_le (originalEOFMachine route j) inputLength (trace.take k)
  have hk : (trace.take k).length≤trace.length := by simp only [List.length_take]; omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
