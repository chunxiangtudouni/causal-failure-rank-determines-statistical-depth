module
public import Structure.RootB23_Threshold_NumeratorCopy_012
public import Structure.RootB23_Threshold_DenominatorRoute_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.DenominatorCopy
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031 (workSuffix)

def sourceArchive (archive num : List Bool) : List Bool :=
  true::false::false::(PSTRTMRawNat010.leftBlocks num.reverse++false::archive)

def returnCode : Machine 94 := PSTRTMSeq005.seqMachine
  PA17TMRatArithmeticWidth018.scanMachine DenominatorRoute.backCode

/-- The copied NUM is really crossed and rewound before the retained DEN
source is reached. In particular no original cursor is reset for free. -/
theorem return_bounded (archive num den depth b : List Bool) (gap : ℕ) (q : Rat)
    (nonnegative : 0 ≤ q) (depthNonempty : depth≠[]) :
    BoundedRun returnCode
      (Tape.mk₂ (RoutedCopy.destinationLeft 0
        (SourceRoutes.numFinish den depth b gap q (false::archive) num))
        (PA17TMRatArithmeticCopy006.workspace num)) 94
      (Tape.mk₂ (false::sourceArchive archive num)
        (DenominatorRoute.right den depth b num gap q []))
      (2*den.length+2*num.length+DenominatorRoute.cost depth b num gap q+2) := by
  have crossed : BoundedRun PA17TMRatArithmeticWidth018.scanMachine
      (Tape.mk₂ (RoutedCopy.destinationLeft 0
        (SourceRoutes.numFinish den depth b gap q (false::archive) num))
        (PA17TMRatArithmeticCopy006.workspace num)) 1
      (Tape.mk₂ (DenominatorRoute.finish depth b num gap q
        (false::sourceArchive archive num) den) [false]) (2*num.length+2) := by
    refine ⟨PA17TMRatArithmeticWidth018.scanTrace
      (RoutedCopy.destinationLeft 0 (SourceRoutes.numFinish den depth b gap q (false::archive) num))
      num false [],?_,
      by rw [PA17TMRatArithmeticWidth018.scanTrace_length]⟩
    exact PA17TMRatArithmeticWidth018.scan_runsFrom _ _ _ _
  have back:=DenominatorRoute.back_bounded (sourceArchive archive num) den depth b num [] gap q
    nonnegative depthNonempty
  exact (crossed.seq back).mono (by dsimp only [DenominatorRoute.cost,SourceRoutes.denCost];omega)

def outwardMarkerCode : Machine 104 := PSTRTMSeq005.seqMachine
  DenominatorRoute.route.out NumeratorCopy.markerCode
def prepareCode : Machine 205 := PSTRTMSeq005.seqMachine outwardMarkerCode DenominatorRoute.route.back
def copyCode : Machine 1368 := PSTRTMSeq005.seqMachine prepareCode (RoutedCopy.copyMachine DenominatorRoute.route)

def copyCost (den depth b num : List Bool) (gap : ℕ) (q : Rat) : ℕ :=
  4*den.length^2+(2*DenominatorRoute.cost depth b num gap q+45)*den.length+
    5*DenominatorRoute.cost depth b num gap q+33

theorem copy_bounded (archive den depth b num : List Bool) (gap : ℕ) (q : Rat)
    (nonnegative : 0 ≤ q) (depthNonempty : depth≠[]) (bNonempty : b≠[]) :
    BoundedRun copyCode
      (Tape.mk₂ (false::archive) (DenominatorRoute.right den depth b num gap q [])) 1368
      (Tape.mk₂ (RoutedCopy.destinationLeft 0 (DenominatorRoute.finish depth b num gap q
        (false::archive) den)) (PA17TMRatArithmeticCopy006.workspace den))
      (copyCost den depth b num gap q) := by
  have routes:=DenominatorRoute.correct depth b num gap q nonnegative depthNonempty bNonempty
  have out:=routes.out_run (false::archive) den []
  have marked:=NumeratorCopy.marker_bounded
    (DenominatorRoute.finish depth b num gap q (false::archive) den)
  have back:=routes.back_run archive den (workSuffix 0 [])
  have prepared:=((out.seq marked).seq back)
  have copied:=RoutedCopy.copy_bounded DenominatorRoute.route
    (DenominatorRoute.context depth b num gap q) (DenominatorRoute.finish depth b num gap q)
    (DenominatorRoute.cost depth b num gap q) routes archive den 0
  have actual:=prepared.seq copied
  rw [←DenominatorRoute.word] at actual
  exact actual.mono (by
    simp only [copyCost,Nat.add_mul,Nat.mul_zero,Nat.add_zero]
    omega)

def code : Machine 1463 := PSTRTMSeq005.seqMachine returnCode copyCode
def cost (num den depth b : List Bool) (gap : ℕ) (q : Rat) : ℕ :=
  2*den.length+2*num.length+DenominatorRoute.cost depth b num gap q+2+
    copyCost den depth b num gap q

/-- A real extension of the first far copy. The SAME factor, B and both
retained risk sources survive; the two new flagged fields occupy actual
consecutive destinations with their 0010 marker and final OWN00. -/
theorem actual_bounded (archive num den depth b : List Bool) (gap : ℕ) (q : Rat)
    (nonnegative : 0 ≤ q) (depthNonempty : depth≠[]) (bNonempty : b≠[]) :
    BoundedRun code
      (Tape.mk₂ (RoutedCopy.destinationLeft 0
        (SourceRoutes.numFinish den depth b gap q (false::archive) num))
        (PA17TMRatArithmeticCopy006.workspace num)) 1463
      (Tape.mk₂ (RoutedCopy.destinationLeft 0 (DenominatorRoute.finish depth b num gap q
        (false::sourceArchive archive num) den)) (PA17TMRatArithmeticCopy006.workspace den))
      (cost num den depth b gap q) := by
  exact (return_bounded archive num den depth b gap q nonnegative depthNonempty).seq
    (copy_bounded (sourceArchive archive num) den depth b num gap q nonnegative depthNonempty bNonempty)

end RootB23.Threshold.DenominatorCopy
