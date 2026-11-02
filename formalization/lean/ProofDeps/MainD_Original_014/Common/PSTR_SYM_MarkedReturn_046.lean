module

public import Common.PSTR_SYM_LaneReturn_045

/-! Physical marker consumers. Their scan qualifications follow from the
same actual processed Datum prefix and its paired cells, rather than an
external first-triple/root oracle. The global counter-call control and
the original bootstrap still have to produce these internal entries. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicMarkedReturn

open Turing PSTRTMSeq005 PA17TMRatArithmeticParse002
open PSTRSymbolicLaneScan PSTRSymbolicLaneArchive PSTRSymbolicLaneReturn

theorem datumPairs_head (value : Datum) :
    ∃ (bit : Bool) (later : List (Bool × Bool)), datumPairs value = (false,bit) :: later := by
  cases value with
  | natural number =>
    cases shape : PSTRTMNatValue017.rawPayload number with
    | nil => exact False.elim (rawPayload_nonempty number shape)
    | cons bit later =>
      refine ⟨bit, falsePairs later ++ [(true,false)], ?_⟩
      simp only [datumPairs, shape, naturalPairs, falsePairs, List.map_cons, List.cons_append]
  | rational value =>
    cases shape : denominatorDigits value with
    | nil => exact False.elim (rawPayload_nonempty value.den shape)
    | cons first later =>
      refine ⟨sign value, falsePairs (numeratorDigits value) ++
        ((true,first) :: (falsePairs later ++ [(true,true)])), ?_⟩
      simp [datumPairs, shape, rationalPairs, List.append_assoc]

theorem actual_prefix_reset_reverse (data : List Datum) (earlier later : List (Bool × Bool))
    (shape : allDatumPairs data = earlier ++ later) : seenAfter 0 earlier.reverse = 0 := by
  cases earlier with
  | nil => rfl
  | cons pair remaining =>
    obtain ⟨flag,bit⟩ := pair
    cases data with
    | nil => simp [allDatumPairs] at shape
    | cons value rest =>
      obtain ⟨first, tail, head⟩ := datumPairs_head value
      change datumPairs value ++ allDatumPairs rest = ((flag,bit) :: remaining) ++ later at shape
      rw [head] at shape
      have flags : false = flag := congrArg Prod.fst (List.cons.inj shape).1
      subst flag
      rw [List.reverse_cons, seenAfter_append]
      rfl

def reverseCells (pairs : List (Bool × Bool)) : List Bool :=
  pairs.flatMap (fun pair => [pair.2,pair.1])

theorem reverseCells_append (first second : List (Bool × Bool)) :
    reverseCells (first ++ second) = reverseCells first ++ reverseCells second := by
  simp only [reverseCells, List.flatMap_append]

theorem reverseNavigationCells (pairs : List (Bool × Bool)) :
    (navigationCells pairs).reverse = reverseCells pairs.reverse := by
  induction pairs with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨flag,bit⟩ := pair
    simp only [navigationCells_cons, List.reverse_cons, reverseCells_append, ih, List.append_assoc]
    rfl

def rePair (current : Bool) : List (Bool × Bool) → Bool → List (Bool × Bool)
  | [], endBit => [(current,endBit)]
  | (flag,bit) :: earlier, endBit => (current,bit) :: rePair flag earlier endBit

theorem rePair_cells (current : Bool) (pairs : List (Bool × Bool)) (endBit : Bool) :
    navigationCells (rePair current pairs endBit) = current :: (reverseCells pairs ++ [endBit]) := by
  induction pairs generalizing current with
  | nil => rfl
  | cons pair earlier ih =>
    obtain ⟨flag,bit⟩ := pair
    change current :: bit :: navigationCells (rePair flag earlier endBit) =
      current :: bit :: flag :: (reverseCells earlier ++ [endBit])
    rw [ih]

theorem rePair_flags (current : Bool) (pairs : List (Bool × Bool)) (endBit : Bool) :
    (rePair current pairs endBit).map Prod.fst = current :: pairs.map Prod.fst := by
  induction pairs generalizing current with
  | nil => rfl
  | cons pair earlier ih =>
    obtain ⟨flag,bit⟩ := pair
    change current :: (rePair flag earlier endBit).map Prod.fst = current :: flag :: earlier.map Prod.fst
    rw [ih]

def leftPrefix (earlier : List (Bool × Bool)) : List (Bool × Bool) := rePair false earlier.reverse false
def rightPrefix (earlier : List (Bool × Bool)) (far : Bool) : List (Bool × Bool) := earlier ++ [(false,far)]

theorem leftPrefix_cells (earlier : List (Bool × Bool)) :
    navigationCells (leftPrefix earlier) = false :: ((navigationCells earlier).reverse ++ [false]) := by
  rw [leftPrefix, rePair_cells, ← reverseNavigationCells]

theorem rightPrefix_cells (earlier : List (Bool × Bool)) (far : Bool) :
    navigationCells (rightPrefix earlier far) = navigationCells earlier ++ [false,far] := by
  rw [rightPrefix, navigationCells_append]
  rfl

theorem rightPrefix_reverse (earlier : List (Bool × Bool)) (far : Bool) :
    (navigationCells (rightPrefix earlier far)).reverse = far :: false :: (navigationCells earlier).reverse := by
  rw [rightPrefix_cells, List.reverse_append]
  rfl

theorem leftPrefix_valid (data : List Datum) (earlier later : List (Bool × Bool))
    (shape : allDatumPairs data = earlier ++ later) :
    safeNavigation 0 (leftPrefix earlier) ∧ seenAfter 0 (leftPrefix earlier) = 0 := by
  have sourceSafe : safeNavigation 0 ((false,false) :: earlier.reverse) :=
    ⟨Or.inl rfl, (actual_prefix_safe_both data earlier later shape).2⟩
  have sourceReset : seenAfter 0 ((false,false) :: earlier.reverse) = 0 :=
    actual_prefix_reset_reverse data earlier later shape
  have same := navigation_flags_congr 0 (leftPrefix earlier) ((false,false) :: earlier.reverse)
    (by rw [leftPrefix, rePair_flags]; rfl)
  exact ⟨Eq.mpr same.1 sourceSafe, same.2.trans sourceReset⟩

theorem rightPrefix_valid (data : List Datum) (earlier later : List (Bool × Bool)) (far : Bool)
    (shape : allDatumPairs data = earlier ++ later) :
    safeNavigation 0 (rightPrefix earlier far) ∧ seenAfter 0 (rightPrefix earlier far) = 0 := by
  refine ⟨(safeNavigation_append 0 earlier [(false,far)]).mpr ⟨?_, ?_⟩, ?_⟩
  · exact (actual_prefix_safe_both data earlier later shape).1
  · exact ⟨Or.inl rfl,trivial⟩
  · rw [rightPrefix, seenAfter_append]
    rfl

theorem actual_right_return (data : List Datum) (earlier later : List (Bool × Bool))
    (header suffix : List Bool) (far middle near : Bool)
    (shape : allDatumPairs data = earlier ++ later) :
    RunsFrom (flagWalkMachine true)
      (scanState 0 header (navigationCells earlier ++ false :: far :: true :: middle :: true :: near :: true :: suffix))
      (rightScanTrace 0 header (rightPrefix earlier far) middle near suffix)
      (scanState 6 (near :: true :: middle :: true :: far :: false :: ((navigationCells earlier).reverse ++ header))
        (true :: suffix)) := by
  obtain ⟨safe, reset⟩ := rightPrefix_valid data earlier later far shape
  have actual := right_scan_runsFrom 0 header (rightPrefix earlier far) middle near suffix safe reset
  have front : scanState (readLabel 0) header
      (navigationCells (rightPrefix earlier far) ++ true :: middle :: true :: near :: true :: suffix) =
      scanState 0 header
        (navigationCells earlier ++ false :: far :: true :: middle :: true :: near :: true :: suffix) := by
    rw [rightPrefix_cells, List.append_assoc]
    rfl
  have final : scanState 6
      (near :: true :: middle :: true :: ((navigationCells (rightPrefix earlier far)).reverse ++ header))
      (true :: suffix) =
      scanState 6 (near :: true :: middle :: true :: far :: false :: ((navigationCells earlier).reverse ++ header))
        (true :: suffix) := by
    rw [rightPrefix_reverse]
    rfl
  rw [front, final] at actual
  exact actual

theorem actual_left_root (data : List Datum) (earlier later : List (Bool × Bool))
    (older suffix : List Bool) (rootFirst rootSecond : Bool)
    (shape : allDatumPairs data = earlier ++ later) :
    RunsFrom (flagWalkMachine false)
      (scanState 0 ((navigationCells earlier).reverse ++ false :: true :: rootFirst :: true :: rootSecond :: true :: older)
        (false :: suffix))
      (leftScanTrace 0 older (leftPrefix earlier) rootFirst rootSecond suffix)
      (scanState 6 older (true :: rootSecond :: true :: rootFirst :: true ::
        ((navigationCells (leftPrefix earlier)).reverse ++ suffix))) := by
  obtain ⟨safe, reset⟩ := leftPrefix_valid data earlier later shape
  have actual := left_scan_runsFrom 0 older (leftPrefix earlier) rootFirst rootSecond suffix safe reset
  have front : leftFront 0
      (navigationCells (leftPrefix earlier) ++ true :: rootFirst :: true :: rootSecond :: true :: older) suffix =
      scanState 0 ((navigationCells earlier).reverse ++ false :: true :: rootFirst :: true :: rootSecond :: true :: older)
        (false :: suffix) := by
    rw [leftPrefix_cells]
    simp [leftFront, readLabel, List.append_assoc]
  rw [front] at actual
  exact actual

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicMarkedReturn
