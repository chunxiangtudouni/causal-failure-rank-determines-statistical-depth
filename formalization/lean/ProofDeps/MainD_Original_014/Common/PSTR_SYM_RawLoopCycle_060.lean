module

public import Common.PSTR_SYM_RawLoopCode_059

/-! SOURCEONLY. A real parse/paired-archive/counter-return cycle in the
ONE059 table. The caller must establish the raw remaining-list invariant;
this segment alone does not equate the returned zero bit with raw EOF. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawLoop

open Turing PSTRTMSeq005 PSTRTMRawNat010 PSTRTMIncrement009
open PSTRSymbolicPairedArchive PSTRSymbolicLaneScan PSTRSymbolicLaneArchive
open PSTRSymbolicCursorCode PSTRSymbolicCursorStages PSTRSymbolicCursorArchive

theorem archive_append_reverse (data : List Datum) (value : Datum) :
    (navigationCells (allDatumPairs (data ++ [value]))).reverse =
      (pairedDatum value).reverse ++ (navigationCells (allDatumPairs data)).reverse := by
  simp only [allDatumPairs_cells,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.reverse_append]

def datumEntryTape (data : List Datum) (base digits suffix : List Bool) (value : Datum) : Tape Bool :=
  Tape.mk₂ ((navigationCells (allDatumPairs data)).reverse ++ false :: (leftBlocks digits.reverse ++ false :: base))
    (encodeDatum value ++ suffix)

theorem actual_cycle (data : List Datum) (value : Datum) (base digits suffix : List Bool) (tag : Bool)
    (archiveRoom : 3 ≤ (allDatumPairs (data ++ [value])).length) (headerRoom : 3 ≤ digits.length)
    (positive : true ∈ digits) :
    ∃ (trace : List (TM0.Cfg Bool LoopLabel)) (final : TM0.Cfg Bool LoopLabel),
      trace.head? = some ⟨.datum 0,datumEntryTape data base digits (tag :: suffix) value⟩ ∧
      trace.IsChain (fun before after => TM0.step loopCode before = some after) ∧
      trace.getLast? = some final ∧
      final.q = .cursor (PSTRSymbolicCursorFinite.labels (.halt (decide (valueDigits digits = 1)))) ∧
      final.Tape = archiveTape (data ++ [value]) base (PSTRTMThresholdCountdownCode164.predDigits digits) suffix tag ∧
      TM0.step loopCode final = some
        ⟨if decide (valueDigits digits = 1) then .done true else .datum 0,final.Tape⟩ ∧
      trace.length ≤ 128 * ((encodeDatum value).length + 1)^2 +
        4 * (allDatumPairs (data ++ [value])).length + 10 * digits.length + 65 := by
  let archive := (navigationCells (allDatumPairs data)).reverse ++
    false :: (leftBlocks digits.reverse ++ false :: base)
  obtain ⟨parsedTrace,parsedFinal,parsedRun,parsedTape,parsedTime,_⟩ :=
    raw_datum_parse_compact archive value (tag :: suffix)
  have physical : parsedFinal.Tape = archiveTape (data ++ [value]) base digits suffix tag := by
    rw [parsedTape,archiveTape,archive_append_reverse]
    simp only [archive,List.append_assoc]
  obtain ⟨cursorTrace,cursorFinal,cursorRun,port,cursorTape,cursorTime,_⟩ :=
    actual_archive_round (data ++ [value]) base digits suffix tag archiveRoom headerRoom positive
  have parsedPart := called_endpoints loopCode datumCompactMachine LoopLabel.datum (fun _ => .cursor 0)
    (by intro q bit; rfl) _ _ _ parsedRun
  have cursorPart := called_endpoints loopCode PSTRSymbolicCursorFinite.cursorMachine LoopLabel.cursor cursorFinish
    (by intro q bit; rfl) _ _ _ cursorRun
  let final := tagCfg LoopLabel.cursor cursorFinal
  have bodyHead : (parsedTrace.map (tagCfg LoopLabel.datum)).head? = some
      ⟨.datum 0,datumEntryTape data base digits (tag :: suffix) value⟩ := parsedPart.1
  have cursorHead : (cursorTrace.map (tagCfg LoopLabel.cursor)).head? = some
      ⟨.cursor 0,parsedFinal.Tape⟩ := by
    rw [physical]
    exact cursorPart.1
  have cursorLast : (cursorTrace.map (tagCfg LoopLabel.cursor)).getLast? = some final := cursorPart.2.2.1
  let trace := parsedTrace.map (tagCfg LoopLabel.datum) ++ cursorTrace.map (tagCfg LoopLabel.cursor)
  have chain : trace.IsChain (fun before after => TM0.step loopCode before = some after) := by
    apply List.IsChain.append parsedPart.2.1 cursorPart.2.1
    intro before beforeLast after afterHead
    simp only [parsedPart.2.2.1,Option.mem_some_iff] at beforeLast
    simp only [cursorHead,Option.mem_some_iff] at afterHead
    subst before
    subst after
    exact parsedPart.2.2.2.1
  refine ⟨trace,final,?_,chain,?_,?_,cursorTape,?_,?_⟩
  · simp only [trace,List.head?_append,bodyHead,Option.some_or]
  · simp only [trace,List.getLast?_append,cursorLast,Option.some_or]
  · change LoopLabel.cursor cursorFinal.q = _
    rw [port]
  · exact cursor_return cursorFinal cursorRun.2.2.2 _ port
  · simp only [trace,List.length_append,List.length_map]
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawLoop
