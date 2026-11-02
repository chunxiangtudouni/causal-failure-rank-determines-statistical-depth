module

public import Common.PSTR_WordBool_RawOutput_Finish007
public import Common.PSTR_WordBool_RawOutput_Init008

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace PaperProofs.Common.Native.PSTRWordBool.RawOutput.Extract

open Turing
open PaperProofs.Common.Native.RationalControllerComputation

private def Path (start finish : State) (rest : List State) : Prop :=
  (start :: rest).IsChain Edge ∧ (start :: rest).getLast?=some finish

private theorem join_paths (start middle finish : State) (front back : List State)
    (hf : Path start middle front) (hb : Path middle finish back) :
    Path start finish (front ++ back) := by
  constructor
  · simpa only [List.cons_append] using
      NativeTrace.join_chain (start :: front) middle back hf.2 hf.1 hb.1
  · simpa only [List.cons_append] using
      (NativeTrace.join_last (start :: front) middle back hf.2).trans hb.2

private theorem two_edges (first second third : State) (hf : Edge first second) (hs : Edge second third) :
    Path first third [second,third] :=
  ⟨List.isChain_cons_cons.mpr ⟨hf,List.isChain_cons_cons.mpr ⟨hs,.singleton _⟩⟩,rfl⟩

private theorem one_edge (first second : State) (edge : Edge first second) : Path first second [second] :=
  ⟨List.isChain_cons_cons.mpr ⟨edge,.singleton _⟩,rfl⟩

theorem dataRows_cons (bit : Bool) (later : List Bool) :
    dataRows (bit :: later)=dataRow bit ++ dataRows later := by simp [dataRows]

/-- One actual read, west push, and return. The observed bit is carried
only by finite labels3/4 and5/6; all four scans follow real tape markers. -/
private theorem copy_cycle (previous later : List Bool) (bit : Bool) :
    ∃ rest : List State, Path (loopCfg previous (bit :: later)) (loopCfg (bit :: previous) later) rest ∧
      rest.length=4*previous.length+6 := by
  let n := previous.length
  let work := workLeft previous
  let left := (doneRows n).reverse ++ guardRow.reverse ++ work
  let body := doneRows (n+1) ++ dataRows later
  let bank := guardRow ++ body
  let pointed := cfg 1 left (dataRow bit ++ dataRows later)
  let read := cfg 2 (false :: left) (true :: bit :: (List.replicate 30 false ++ dataRows later))
  let held := shuttleCfg bit n work (dataRows later)
  let guarded := guardCfg bit work body
  let seeking := seekCfg bit previous.reverse [] bank
  let ready := seekCfg bit [] previous bank
  let returning := returnCfg [bit] previous bank
  let boundary := returnCfg (bit :: previous).reverse [] bank
  obtain ⟨scan,scanChain,scanLast,scanClock⟩ := scan_rows n
    (guardRow.reverse ++ work) (dataRow bit ++ dataRows later)
  have scanPath : Path (loopCfg previous (bit :: later)) pointed scan := by
    simpa only [Path,loopCfg,dataRows_cons,pointed,left,n,work,List.append_assoc] using
      And.intro scanChain scanLast
  have readPath : Path pointed held [read,held] := by
    apply two_edges
    · exact source_present left (dataRows later) bit
    · simpa only [held,read,shuttleCfg,left,List.append_assoc] using read_present left (dataRows later) bit
  obtain ⟨shuttleRest,shuttleChain,shuttleLast,shuttleClock⟩ := shuttle_rows bit n work (dataRows later)
  have shuttlePath : Path held guarded shuttleRest := ⟨shuttleChain,shuttleLast⟩
  have guardPath : Path guarded seeking [seeking] := one_edge _ _ (guard_to_seek bit previous body)
  obtain ⟨seekRest,seekChain,seekLast,seekClock⟩ := seek_pairs bit previous.reverse [] bank
  have seekPath : Path seeking ready seekRest := by
    simpa only [Path,seeking,ready,List.reverse_reverse,List.append_nil] using And.intro seekChain seekLast
  have pushPath : Path ready returning [returning] := one_edge _ _ (push_pair bit previous bank)
  obtain ⟨returnRest,returnChain,returnLast,returnClock⟩ := return_pairs [bit] previous bank
  have returnPath : Path returning boundary returnRest := by
    simpa only [Path,returning,boundary,List.reverse_cons,List.reverse_nil,List.nil_append] using
      And.intro returnChain returnLast
  have boundaryPath : Path boundary (loopCfg (bit :: previous) later) [loopCfg (bit :: previous) later] := by
    apply one_edge
    simpa only [boundary,loopCfg,List.length_cons,n,bank,body] using return_boundary (bit :: previous) body
  let first := scan ++ [read,held]
  have h1 := join_paths _ _ _ scan [read,held] scanPath readPath
  have h2 := join_paths _ _ _ first shuttleRest h1 shuttlePath
  have h3 := join_paths _ _ _ (first ++ shuttleRest) [seeking] h2 guardPath
  have h4 := join_paths _ _ _ ((first ++ shuttleRest) ++ [seeking]) seekRest h3 seekPath
  have h5 := join_paths _ _ _ (((first ++ shuttleRest) ++ [seeking]) ++ seekRest) [returning] h4 pushPath
  have h6 := join_paths _ _ _ ((((first ++ shuttleRest) ++ [seeking]) ++ seekRest) ++ [returning]) returnRest h5 returnPath
  have h7 := join_paths _ _ _ (((((first ++ shuttleRest) ++ [seeking]) ++ seekRest) ++ [returning]) ++ returnRest)
    [loopCfg (bit :: previous) later] h6 boundaryPath
  refine ⟨_,h7,?_⟩
  simp only [List.length_append,first,List.length_append,List.length_cons,List.length_nil,
    scanClock,shuttleClock,seekClock,returnClock,List.length_reverse,n]
  omega

private theorem empty_cycle (previous : List Bool) :
    ∃ rest : List State, Path (loopCfg previous []) (finishCfg previous) rest ∧
      rest.length=3*previous.length+6 := by
  let n := previous.length
  let work := workLeft previous
  let left := (doneRows n).reverse ++ guardRow.reverse ++ work
  let pointed := cfg 1 left []
  let read := cfg 2 (false :: left) []
  let erasing := cfg 8 left []
  obtain ⟨scan,scanChain,scanLast,scanClock⟩ := scan_rows n (guardRow.reverse ++ work) []
  have scanPath : Path (loopCfg previous []) pointed scan := by
    simpa only [Path,loopCfg,dataRows,List.flatMap_nil,pointed,left,n,work,List.append_assoc] using
      And.intro scanChain scanLast
  have readPath : Path pointed erasing [read,erasing] :=
    two_edges _ _ _ (source_absent left).1 (source_absent left).2
  obtain ⟨eraseRest,eraseChain,eraseLast,eraseClock⟩ := erase_all n work
  have erasePath : Path erasing (cfg 9 work []) eraseRest := ⟨eraseChain,eraseLast⟩
  obtain ⟨finishRest,finishChain,finishLast,finishClock⟩ := finish_all previous
  have finishPath : Path (cfg 9 work []) (finishCfg previous) finishRest := ⟨finishChain,finishLast⟩
  have h1 := join_paths _ _ _ scan [read,erasing] scanPath readPath
  have h2 := join_paths _ _ _ (scan ++ [read,erasing]) eraseRest h1 erasePath
  have h3 := join_paths _ _ _ ((scan ++ [read,erasing]) ++ eraseRest) finishRest h2 finishPath
  refine ⟨_,h3,?_⟩
  simp only [List.length_append,List.length_cons,List.length_nil,scanClock,eraseClock,finishClock,n]
  omega

private theorem loop_path (previous remaining : List Bool) :
    ∃ rest : List State, Path (loopCfg previous remaining) (finishCfg (remaining.reverse ++ previous)) rest ∧
      rest.length=loopClock previous remaining := by
  induction remaining generalizing previous with
  | nil =>
    obtain ⟨rest,path,clock⟩ := empty_cycle previous
    refine ⟨rest,path,?_⟩
    simpa [loopClock] using clock
  | cons bit later ih =>
    obtain ⟨front,frontPath,frontClock⟩ := copy_cycle previous later bit
    obtain ⟨back,backPath,backClock⟩ := ih (bit :: previous)
    have joined := join_paths _ _ _ front back frontPath backPath
    refine ⟨front ++ back,?_,?_⟩
    · simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using joined
    · rw [List.length_append,frontClock,backClock,clock_step]

/-- The complete actual eleven-label source trajectory. The next compiler
expands these SAME macros into actual finite Bool TM0 instructions. -/
theorem source_path (bits : List Bool) :
    ∃ rest : List State,
      (TM1.init (Γ := Bool) (Λ := Label) (σ := Unit)
        (FiniteTrackCodec.encodedInput (0 : Fin 16) bits) :: rest).IsChain Edge ∧
      (TM1.init (Γ := Bool) (Λ := Label) (σ := Unit)
        (FiniteTrackCodec.encodedInput (0 : Fin 16) bits) :: rest).getLast?=some (finishCfg bits) ∧
      rest.length=2*bits.length^2+7*bits.length+7 := by
  obtain ⟨rest,path,clock⟩ := loop_path [] bits.reverse
  refine ⟨loopCfg [] bits.reverse :: rest,
    List.isChain_cons_cons.mpr ⟨initial_step bits,path.1⟩,?_,?_⟩
  · simpa only [List.getLast?_cons_cons,List.reverse_reverse,List.append_nil] using path.2
  · simp only [List.length_cons,clock,loopClock,List.length_nil,List.length_reverse]
    ring

end PaperProofs.Common.Native.PSTRWordBool.RawOutput.Extract
