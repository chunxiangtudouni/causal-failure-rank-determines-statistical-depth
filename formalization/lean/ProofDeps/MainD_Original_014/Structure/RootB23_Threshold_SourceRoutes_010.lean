module
public import Structure.RootB23_Threshold_FactorBack_009
public import Structure.RootB23_Threshold_RoutedLoop_007
public import Structure.PA17_TM_RatArithmetic_FarLoad_031g

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.SourceRoutes
open PaperProofs.Common.Native.RationalControllerComputation Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)

/-- These two route tables are compiled before every input. No field,
gap, width, branch answer or rational value occurs in their code. -/
def numeratorRoute : RoutedCopy.Route :=
  ⟨padMachine (by decide : 67≤100) FactorWalk.numCode,
   padMachine (by decide : 91≤100) FactorBack.numCode,
   padLabel (by decide : 67≤100) 67,padLabel (by decide : 91≤100) 91⟩
def denominatorRoute : RoutedCopy.Route :=
  ⟨padMachine (by decide : 61≤100) FactorWalk.denCode,
   padMachine (by decide : 82≤100) FactorBack.denCode,
   padLabel (by decide : 61≤100) 61,padLabel (by decide : 82≤100) 82⟩

def depthCore (depth b : List Bool) (gap : ℕ) (q : Rat) : List Bool :=
  PSTRTMIncrement009.blocks depth++List.replicate (2*gap+2) false++
    PSTRTMIncrement009.blocks b++encodeDatum (.rational q)
def denContext (depth b : List Bool) (gap : ℕ) (q : Rat) : List Bool :=
  false::true::false::depthCore depth b gap q
def numContext (den depth b : List Bool) (gap : ℕ) (q : Rat) : List Bool :=
  false::true::false::(PSTRTMIncrement009.blocks den++FactorWalk.marker (depthCore depth b gap q))
def denFinish (depth b : List Bool) (gap : ℕ) (q : Rat) (left later : List Bool) : List Bool :=
  PA17TMRatArithmeticParse002.ratLeft (FactorWalk.bBase (FactorWalk.markedLeft left later) depth b gap) q
def numFinish (den depth b : List Bool) (gap : ℕ) (q : Rat) (left later : List Bool) : List Bool :=
  PA17TMRatArithmeticParse002.ratLeft
    (FactorWalk.bBase (FactorWalk.markedLeft (FactorWalk.markedLeft left later) den) depth b gap) q
def denCost (depth b : List Bool) (gap : ℕ) (q : Rat) : ℕ :=
  2*depth.length+2*gap+2*b.length+128*(natBits q.num.natAbs+natBits q.den+1)^2+32
def numCost (den depth b : List Bool) (gap : ℕ) (q : Rat) : ℕ :=
  2*den.length+denCost depth b gap q

theorem den_word (digits depth b : List Bool) (gap : ℕ) (q : Rat) (suffix : List Bool) :
    FactorWalk.denRight digits depth b gap q suffix=
      RoutedCopy.fieldWord (denContext depth b gap q) digits suffix := by
  simp only [FactorWalk.denRight,FactorWalk.marker,FactorWalk.depthRight,FactorWalk.bRight,
    RoutedCopy.fieldWord,denContext,depthCore,List.append_assoc,List.cons_append]
theorem num_word (digits den depth b : List Bool) (gap : ℕ) (q : Rat) (suffix : List Bool) :
    FactorWalk.numRight digits den depth b gap q suffix=
      RoutedCopy.fieldWord (numContext den depth b gap q) digits suffix := by
  simp only [FactorWalk.numRight,FactorWalk.denRight,FactorWalk.marker,FactorWalk.depthRight,FactorWalk.bRight,
    RoutedCopy.fieldWord,numContext,depthCore,List.append_assoc,List.cons_append]

private theorem marked_cons (left later : List Bool) (bit : Bool) :
    FactorWalk.markedLeft (true::bit::left) later=FactorWalk.markedLeft left (bit::later) := by
  simp [FactorWalk.markedLeft,PSTRTMRawNat010.leftBlocks,List.reverse_cons,List.flatMap_append,List.append_assoc]

/-- The concrete NUM out/back paths restore the actual source bit's
temporary FALSE flag, not a guessed home cursor. Width is only a proof
measure; the very same finite table serves all original risk/depth data. -/
theorem numerator_correct (den depth b : List Bool) (gap : ℕ) (q : Rat)
    (nonnegative : 0≤q) (depthNonempty : depth≠[]) (bNonempty : b≠[]) :
    RoutedCopy.RouteCorrect numeratorRoute (numContext den depth b gap q)
      (numFinish den depth b gap q) (numCost den depth b gap q) := by
  refine ⟨rfl,?_,?_,?_⟩
  · intro left bit later
    simp only [numFinish,marked_cons]
  · intro left later suffix
    have actual:=FactorWalk.numerator_bounded left later den depth b suffix gap q nonnegative bNonempty
    rw [num_word] at actual
    have padded:=PA17TMRatArithmeticFarLoad031.bounded_pad (by decide : 67≤100) actual
    exact padded.mono (by dsimp only [numCost,denCost];omega)
  · intro archive later suffix
    have actual:=FactorBack.numerator_bounded archive later den depth b suffix gap q nonnegative depthNonempty
    rw [num_word] at actual
    have padded:=PA17TMRatArithmeticFarLoad031.bounded_pad (by decide : 91≤100) actual
    exact padded.mono (by dsimp only [numCost,denCost];omega)

theorem denominator_correct (depth b : List Bool) (gap : ℕ) (q : Rat)
    (nonnegative : 0≤q) (depthNonempty : depth≠[]) (bNonempty : b≠[]) :
    RoutedCopy.RouteCorrect denominatorRoute (denContext depth b gap q)
      (denFinish depth b gap q) (denCost depth b gap q) := by
  refine ⟨rfl,?_,?_,?_⟩
  · intro left bit later
    simp only [denFinish,marked_cons]
  · intro left later suffix
    have actual:=FactorWalk.denominator_bounded left later depth b suffix gap q nonnegative bNonempty
    rw [den_word] at actual
    have padded:=PA17TMRatArithmeticFarLoad031.bounded_pad (by decide : 61≤100) actual
    exact padded.mono (by dsimp only [denCost];omega)
  · intro archive later suffix
    have actual:=FactorBack.denominator_bounded archive later depth b suffix gap q nonnegative depthNonempty
    rw [den_word] at actual
    have padded:=PA17TMRatArithmeticFarLoad031.bounded_pad (by decide : 82≤100) actual
    exact padded.mono (by dsimp only [denCost];omega)

end RootB23.Threshold.SourceRoutes
