module

public import Common.PSTR_SYM_CursorFinite_053

/-! The actual finite round consumes the SAME complete paired Datum
archive. The marker's three cells and all saved bits are extracted from
that archive in the proof, not supplied as new original input fields. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicCursorArchive

open Turing PSTRTMSeq005 PSTRTMRawNat010 PSTRTMIncrement009
open PA17TMRatArithmeticParse002 PSTRSymbolicLaneScan PSTRSymbolicLaneArchive
open PSTRSymbolicMarkedReturn PSTRSymbolicCursorRound PSTRSymbolicCursorFinite

theorem reverse_three {α : Type} (values : List α) (room : 3 ≤ values.length) :
    ∃ first second third older, values.reverse = first :: second :: third :: older := by
  have reversed : 3 ≤ values.reverse.length := by simpa only [List.length_reverse] using room
  cases firstShape : values.reverse with
  | nil => simp only [firstShape,List.length_nil] at reversed; omega
  | cons first remaining =>
    cases remaining with
    | nil => simp only [firstShape,List.length_cons,List.length_nil] at reversed; omega
    | cons second remaining =>
      cases remaining with
      | nil => simp only [firstShape,List.length_cons,List.length_nil] at reversed; omega
      | cons third older => exact ⟨first,second,third,older,rfl⟩

theorem datumPairs_end (value : Datum) :
    ∃ earlier last, datumPairs value = earlier ++ [(true,last)] := by
  cases value with
  | natural number => exact ⟨falsePairs (PSTRTMNatValue017.rawPayload number),false,rfl⟩
  | rational value =>
    cases shape : denominatorDigits value with
    | nil => exact False.elim (rawPayload_nonempty value.den shape)
    | cons first later =>
      refine ⟨[(false,sign value)] ++ falsePairs (numeratorDigits value) ++
        [(true,first)] ++ falsePairs later,true,?_⟩
      simp only [datumPairs,shape,rationalPairs,List.append_assoc]

theorem allDatumPairs_end (data : List Datum) (nonempty : data ≠ []) :
    ∃ earlier last, allDatumPairs data = earlier ++ [(true,last)] := by
  induction data with
  | nil => exact False.elim (nonempty rfl)
  | cons value rest ih =>
    by_cases empty : rest = []
    · subst rest
      simpa only [allDatumPairs,List.flatMap_cons,List.flatMap_nil,List.append_nil] using datumPairs_end value
    · obtain ⟨earlier,last,shape⟩ := ih empty
      refine ⟨datumPairs value ++ earlier,last,?_⟩
      change datumPairs value ++ allDatumPairs rest = _
      rw [shape,List.append_assoc]

theorem actual_archive_tail (data : List Datum) (room : 3 ≤ (allDatumPairs data).length) :
    ∃ earlier near middle first far second,
      allDatumPairs data = earlier ++ [(second,far),(first,middle),(true,near)] := by
  have nonempty : data ≠ [] := by
    intro empty
    subst data
    simp only [allDatumPairs,List.flatMap_nil,List.length_nil] at room
    omega
  obtain ⟨before,last,endShape⟩ := allDatumPairs_end data nonempty
  obtain ⟨nearPair,middlePair,farPair,older,reverseShape⟩ := reverse_three (allDatumPairs data) room
  obtain ⟨nearFlag,near⟩ := nearPair
  obtain ⟨first,middle⟩ := middlePair
  obtain ⟨second,far⟩ := farPair
  have lastShape : (allDatumPairs data).reverse = (true,last) :: before.reverse := by
    rw [endShape,List.reverse_append]
    rfl
  have flags : nearFlag = true := congrArg Prod.fst (List.cons.inj (reverseShape.symm.trans lastShape)).1
  subst nearFlag
  refine ⟨older.reverse,near,middle,first,far,second,?_⟩
  have original := congrArg List.reverse reverseShape
  simpa only [List.reverse_reverse,List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append] using original

def archiveTape (data : List Datum) (base digits suffix : List Bool) (tag : Bool) : Tape Bool :=
  Tape.mk₂ ((navigationCells (allDatumPairs data)).reverse ++ false :: (leftBlocks digits.reverse ++ false :: base))
    (tag :: suffix)

theorem archive_roundTape (data : List Datum) (earlier : List (Bool × Bool))
    (near middle first far second : Bool)
    (shape : allDatumPairs data = earlier ++ [(second,far),(first,middle),(true,near)])
    (base digits suffix : List Bool) (tag : Bool) :
    archiveTape data base digits suffix tag =
      roundTape earlier base digits suffix near middle first far second tag := by
  rw [archiveTape,shape,navigationCells_append,navigationCells_cons,navigationCells_cons,navigationCells_cons]
  change Tape.mk₂ (((navigationCells earlier) ++ [second,far,first,middle,true,near]).reverse ++
    false :: (leftBlocks digits.reverse ++ false :: base)) (tag :: suffix) = _
  rw [List.reverse_append]
  rfl

theorem actual_archive_round (data : List Datum) (base digits suffix : List Bool) (tag : Bool)
    (archiveRoom : 3 ≤ (allDatumPairs data).length) (headerRoom : 3 ≤ digits.length)
    (positive : true ∈ digits) :
    ∃ (trace : List (MachineState support.card)) (final : MachineState support.card),
      RunsFrom cursorMachine ⟨0,archiveTape data base digits suffix tag⟩ trace final ∧
      final.q = labels (.halt (decide (valueDigits digits = 1))) ∧
      final.Tape = archiveTape data base (PSTRTMThresholdCountdownCode164.predDigits digits) suffix tag ∧
      trace.length ≤ 4 * (allDatumPairs data).length + 10 * digits.length + 65 ∧
      ∀ inputLength clock, visitedSpace cursorMachine inputLength (trace.take clock) ≤
        inputLength + 8 * (allDatumPairs data).length + 20 * digits.length + 131 := by
  obtain ⟨earlier,near,middle,first,far,second,shape⟩ := actual_archive_tail data archiveRoom
  obtain ⟨rootFirst,rootSecond,rootThird,older,headerShape⟩ := reverse_three digits headerRoom
  obtain ⟨trace,final,actual,port,tape,clock,cells⟩ :=
    PSTRSymbolicCursorFinite.actual_round data earlier [(second,far),(first,middle),(true,near)] shape
      base digits older suffix rootFirst rootSecond rootThird near middle first far second tag headerShape positive
  rw [← archive_roundTape data earlier near middle first far second shape base digits suffix tag] at actual
  rw [← archive_roundTape data earlier near middle first far second shape base
    (PSTRTMThresholdCountdownCode164.predDigits digits) suffix tag] at tape
  have prefixLength : earlier.length ≤ (allDatumPairs data).length := by
    rw [shape,List.length_append]
    omega
  refine ⟨trace,final,actual,port,tape,?_,?_⟩
  · omega
  · intro inputLength clock
    have bound := cells inputLength clock
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicCursorArchive
