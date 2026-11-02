module

public import Common.PSTR_SYM_CursorReturn_051

/-! ONE actual round of the concrete048 table: marker, left navigation,
six physical RIGHTs, actual header rewind/decrement, physical return and
marker restoration. Entry qualifications describe the internal physical
archive; the original bootstrap/outer loop must still produce them. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicCursorRound

open Turing PSTRTMSeq005 PSTRTMIncrement009 PSTRTMRawNat010
open PSTRSymbolicPairedCursor PSTRSymbolicCarry PSTRSymbolicCounter
open PSTRSymbolicLaneScan PSTRSymbolicLaneArchive PSTRSymbolicMarkedReturn
open PSTRSymbolicCursorCode PSTRSymbolicCursorStages PSTRSymbolicCursorCounter PSTRSymbolicCursorReturn

theorem leftPrefix_reverse_cells (earlier : List (Bool × Bool)) :
    (navigationCells (leftPrefix earlier)).reverse = false :: (navigationCells earlier ++ [false]) := by
  simp [leftPrefix_cells]

/-- The first original paired record starts with a FALSE tag lane. This
also covers an empty earlier prefix because the real marker starts FALSE. -/
theorem actual_marked_stream (data : List Datum) (earlier later : List (Bool × Bool))
    (shape : allDatumPairs data = earlier ++ later) (suffix : List Bool)
    (far middle near : Bool) :
    ∃ tail, navigationCells earlier ++ false :: far :: true :: middle :: true :: near :: true :: suffix =
      false :: tail := by
  cases earlier with
  | nil => exact ⟨far :: true :: middle :: true :: near :: true :: suffix,rfl⟩
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
      exact ⟨bit :: (navigationCells remaining ++ false :: far :: true :: middle :: true :: near :: true :: suffix),rfl⟩

def roundTape (earlier : List (Bool × Bool)) (base digits suffix : List Bool)
    (near middle first far second tag : Bool) : Tape Bool :=
  Tape.mk₂ (near :: true :: middle :: first :: far :: second ::
    ((navigationCells earlier).reverse ++ false :: (leftBlocks digits.reverse ++ false :: base)))
    (tag :: suffix)

theorem actual_round (data : List Datum) (earlier later : List (Bool × Bool))
    (shape : allDatumPairs data = earlier ++ later) (base digits older suffix : List Bool)
    (rootFirst rootSecond rootThird near middle first far second tag : Bool)
    (headerShape : digits.reverse = rootFirst :: rootSecond :: rootThird :: older)
    (positive : true ∈ digits) :
    ∃ (trace : List (TM0.Cfg Bool Label)) (final : TM0.Cfg Bool Label),
      trace.head? = some ⟨.mark 0,roundTape earlier base digits suffix near middle first far second tag⟩ ∧
      trace.IsChain (fun before after => TM0.step machine before = some after) ∧
      trace.getLast? = some final ∧
      final.q = .halt (decide (valueDigits digits = 1)) ∧
      final.Tape = roundTape earlier base (PSTRTMThresholdCountdownCode164.predDigits digits)
        suffix near middle first far second tag ∧
      TM0.step machine final = none ∧
      trace.length ≤ 4 * earlier.length + 10 * digits.length + 65 := by
  let marked := navigationCells earlier ++ false :: far :: true :: middle :: true :: near :: true :: suffix
  let rootOlder := rootThird :: (leftBlocks older ++ false :: base)
  let header := leftBlocks (PSTRTMThresholdCountdownCode164.predDigits digits).reverse ++ false :: base
  let carry := markerCarry tag first second
  let zero := decide (valueDigits digits = 1)
  obtain ⟨counterSuffix,markedShape⟩ := actual_marked_stream data earlier later shape suffix far middle near
  change marked = false :: counterSuffix at markedShape
  have rootBoundary : (navigationCells (leftPrefix earlier)).reverse ++
      far :: true :: middle :: true :: near :: true :: suffix = false :: marked := by
    rw [leftPrefix_reverse_cells]
    simp only [List.cons_append, List.append_assoc]
    rfl
  obtain ⟨outTrace,outEnd,outHead,outChain,outLast,outQ,outTape,outNext,outLength⟩ :=
    actual_mark_left data earlier later shape rootOlder suffix rootFirst rootSecond near middle first far second tag
  have initialHead : outTrace.head? = some
      ⟨.mark 0,roundTape earlier base digits suffix near middle first far second tag⟩ := by
    simpa only [roundTape,headerShape,leftBlocks,rootOlder,List.flatMap_cons,List.cons_append,
      List.nil_append,List.append_assoc] using outHead
  have rootPhysical : outEnd.Tape = rootTape base older counterSuffix rootFirst rootSecond rootThird := by
    rw [outTape,rootBoundary,markedShape]
    rfl
  rw [rootPhysical] at outNext
  obtain ⟨countTrace,countEnd,countHead,countChain,countLast,countQ,countTape,countNext,countLength⟩ :=
    actual_six_counter carry base digits older counterSuffix rootFirst rootSecond rootThird headerShape positive
  have zeroPort : decide ((counterRoundFinal base digits counterSuffix).q.val = 15) = zero := by
    simp only [zero,counterRound_zero_port base digits counterSuffix positive]
  rw [zeroPort] at countNext
  change countEnd.Tape = Tape.mk₂ header (false :: false :: counterSuffix) at countTape
  obtain ⟨backTrace,backEnd,backHead,backChain,backLast,backQ,backTape,backHalt,backLength⟩ :=
    actual_return_halt data earlier later shape header suffix near middle first far second tag zero
  have backEntry : backTrace.head? = some ⟨.one zero (carryLabel (18 : Fin 20) carry),countEnd.Tape⟩ := by
    rw [countTape]
    change backTrace.head? = some ⟨.one zero (carryLabel (18 : Fin 20) carry),Tape.mk₂ header
      (false :: marked)⟩ at backHead
    rw [markedShape] at backHead
    exact backHead
  let throughCount := outTrace ++ countTrace
  have throughChain : throughCount.IsChain (fun before after => TM0.step machine before = some after) := by
    apply List.IsChain.append outChain countChain
    intro before beforeLast after afterHead
    simp only [outLast,Option.mem_some_iff] at beforeLast
    simp only [countHead,Option.mem_some_iff] at afterHead
    subst before
    subst after
    exact outNext
  have throughLast : throughCount.getLast? = some countEnd := by
    simp only [throughCount,List.getLast?_append,countLast,Option.some_or]
  let trace := throughCount ++ backTrace
  have chain : trace.IsChain (fun before after => TM0.step machine before = some after) := by
    apply List.IsChain.append throughChain backChain
    intro before beforeLast after afterHead
    simp only [throughLast,Option.mem_some_iff] at beforeLast
    simp only [backEntry,Option.mem_some_iff] at afterHead
    subst before
    subst after
    exact countNext
  refine ⟨trace,backEnd,?_,chain,?_,backQ,?_,backHalt,?_⟩
  · simp only [trace,throughCount,List.head?_append,initialHead,Option.some_or]
  · simp only [trace,List.getLast?_append,backLast,Option.some_or]
  · exact backTape
  · simp only [trace,throughCount,List.length_append]
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicCursorRound
