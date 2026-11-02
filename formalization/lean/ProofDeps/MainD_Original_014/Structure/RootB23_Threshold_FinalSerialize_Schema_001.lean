module
public import Structure.RootB23_Threshold_Window_MarshalSerialize_Actual_004
public import Structure.RootB23_Threshold_NatSplice_001
public import Structure.RootB23_Threshold_OutputArithmetic_Target_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.FinalSerialize
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)

def maxLabel (n : Nat) : Fin (n+1) := ⟨n,Nat.lt_succ_self n⟩

def marker (tail : List Bool) : List Bool := false :: false :: true :: false :: tail
def markerLeft (left : List Bool) : List Bool := false :: true :: false :: false :: left

def word (head : List Bool) (rest : List (List Bool)) (tail : List Bool) : List Bool :=
  match rest with
  | [] => PSTRTMIncrement009.blocks head ++ false :: false :: tail
  | next :: later => PSTRTMIncrement009.blocks head ++ marker (word next later tail)

def endLeft (base head : List Bool) (rest : List (List Bool)) : List Bool :=
  match rest with
  | [] => PSTRTMRawNat010.leftBlocks head.reverse ++ base
  | next :: later => endLeft (markerLeft (PSTRTMRawNat010.leftBlocks head.reverse ++ base)) next later

def width (head : List Bool) (rest : List (List Bool)) : Nat := head.length + (rest.map List.length).sum

theorem width_nil (head : List Bool) : width head [] = head.length := by simp only [width,List.map_nil,List.sum_nil,Nat.add_zero]
theorem width_cons (head next : List Bool) (later : List (List Bool)) :
    width head (next :: later) = head.length + width next later := by
  simp only [width,List.map_cons,List.sum_cons]

def nineFields (b : Nat) (t r o i : Rat) : List (List Bool) :=
  [PSTRTMNatValue017.rawPayload b,PA17TMRatArithmeticParse002.numeratorDigits t,
    PA17TMRatArithmeticParse002.denominatorDigits t,PA17TMRatArithmeticParse002.numeratorDigits r,
    PA17TMRatArithmeticParse002.denominatorDigits r,PA17TMRatArithmeticParse002.numeratorDigits o,
    PA17TMRatArithmeticParse002.denominatorDigits o,PA17TMRatArithmeticParse002.numeratorDigits i,
    PA17TMRatArithmeticParse002.denominatorDigits i]

def inputRight (b : Nat) (t r o i : Rat) (suffix : List Bool) : List Bool :=
  word (PSTRTMNatValue017.rawPayload b)
    [PA17TMRatArithmeticParse002.numeratorDigits t,PA17TMRatArithmeticParse002.denominatorDigits t,
      PA17TMRatArithmeticParse002.numeratorDigits r,PA17TMRatArithmeticParse002.denominatorDigits r,
      PA17TMRatArithmeticParse002.numeratorDigits o,PA17TMRatArithmeticParse002.denominatorDigits o,
      PA17TMRatArithmeticParse002.numeratorDigits i,PA17TMRatArithmeticParse002.denominatorDigits i]
    (true :: suffix)

def totalWidth (b : Nat) (t r o i : Rat) : Nat := ((nineFields b t r o i).map List.length).sum

def ownedPrefix : Nat := 7
def tailPadding : Nat := 16

end RootB23.Threshold.FinalSerialize
