module
public import Structure.PA17_TM_RatArithmetic_CachedLoad_038e
public import Structure.PA17_TM_RatArithmetic_PairExcursion_041c
public import Structure.PA17_TM_RatArithmetic_CopyLoop_042b

/-! Discharge the frozen041 source interface with actual cached/original
record routes. No source value, width, observed LSB, or record metadata is a
machine parameter. All later copying uses the single frozen042 loop. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
open PA17TMRatArithmeticBankWalk033

def cachedRoute (j : Nat) : PA17TMRatArithmeticPairExcursion041.SourceRoute (cachedOutCap j) (cachedBackCap j) :=
  ⟨cachedOutMachine j,cachedBackMachine j,true,cachedOutPort j,cachedBackPort j⟩

def cachedCost (j : Nat) (records : List RecordSpec) : Nat :=
  totalGap records+2*totalWidth records+12*j+8

theorem cached_correct (j : Nat) (records : List RecordSpec) (hj : records.length=j) :
    PA17TMRatArithmeticPairExcursion041.SourceCorrect (cachedRoute j) (cacheContext records)
      (cachedFinish records) (cachedCost j records) := by
  refine ⟨?_,cachedFinish_cons records,?_,?_⟩
  · cases records <;> rfl
  · intro left later suffix
    have hr := cached_out_bounded j records hj left later suffix
    have hc : 2*later.length+totalGap records+2*totalWidth records+9*j+5≤2*later.length+cachedCost j records := by
      unfold cachedCost
      omega
    simpa only [cachedRoute,PA17TMRatArithmeticPairExcursion041.sourceWord,cachedWord] using hr.mono hc
  · intro archive later suffix
    have hr := cached_back_bounded j records hj archive later suffix
    have hc : 2*later.length+totalGap records+2*totalWidth records+12*j+8≤2*later.length+cachedCost j records := by
      unfold cachedCost
      omega
    simpa only [cachedRoute,PA17TMRatArithmeticPairExcursion041.sourceWord,cachedWord] using hr.mono hc

def originalFarRoute (route : PA17TMRatArithmeticFarLoad031.FarRoute) (j : Nat) :
    PA17TMRatArithmeticPairExcursion041.SourceRoute (originalOutCap j) (originalBackCap j) :=
  ⟨originalOutMachine route j,originalBackMachine route j,true,originalOutPort j,originalBackPort route j⟩

def originalFarCost (cost j : Nat) (first : RecordSpec) (records : List RecordSpec) : Nat :=
  cost+totalGap (first::records)+2*totalWidth (first::records)+12*(j+1)+3

/-- The source marker temporarily TRUE inside finish is real. The actual
back route restores the original FALSE cell. EOF uses the distinct038e
forwardAny(FALSE) path, not an assumed canonical per-bit out finish. -/
theorem originalFar_correct (route : PA17TMRatArithmeticFarLoad031.FarRoute)
    (context : List Bool) (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (correct : PA17TMRatArithmeticFarLoad031.RouteCorrect route context finish cost)
    (j : Nat) (first : RecordSpec) (records : List RecordSpec) (hj : records.length=j) :
    PA17TMRatArithmeticPairExcursion041.SourceCorrect (originalFarRoute route j)
      (originalFarContext context first records) (originalFarFinish finish (first::records))
      (originalFarCost cost j first records) := by
  refine ⟨?_,originalFarFinish_cons finish correct.finish_cons (first::records),?_,?_⟩
  · cases context with
    | nil => rfl
    | cons bit tail =>
      have hb : bit=false := correct.end_false
      subst bit
      rfl
  · intro left remaining suffix
    have hr := original_out_bounded route context finish cost correct j first records hj left remaining suffix
    have hc : 2*remaining.length+cost+totalGap (first::records)+2*totalWidth (first::records)+9*(j+1)+3≤
        2*remaining.length+originalFarCost cost j first records := by unfold originalFarCost; omega
    simpa only [originalFarRoute,PA17TMRatArithmeticPairExcursion041.sourceWord] using hr.mono hc
  · intro archive remaining suffix
    have hr := original_back_bounded route context finish cost correct j first records hj archive remaining suffix
    have hc : 2*remaining.length+cost+totalGap (first::records)+2*totalWidth (first::records)+12*(j+1)+3≤
        2*remaining.length+originalFarCost cost j first records := by unfold originalFarCost; omega
    simpa only [originalFarRoute,PA17TMRatArithmeticPairExcursion041.sourceWord] using hr.mono hc

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
