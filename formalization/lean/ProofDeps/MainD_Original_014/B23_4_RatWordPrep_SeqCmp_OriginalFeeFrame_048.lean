module

public import B23_4_RatWordPrep_SeqCmp_StackFrame_047

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.OriginalFee

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

variable {C : Type*}

theorem program_accesses (point : Label) : Frame.AccessesOnly Work (program (C := C) .halt point) := by
  cases point with
  | front point =>
    cases point with
    | front point =>
      cases point with
      | prior point => fin_cases point <;> exact of_decide_eq_true rfl
      | encoder point =>
        cases point with
        | collect point | num point | den point => fin_cases point <;> exact of_decide_eq_true rfl
        | reverseNum | reverseDen | finish | done => exact of_decide_eq_true rfl
      | done => exact of_decide_eq_true rfl
    | native point => fin_cases point <;> exact of_decide_eq_true rfl
    | done => exact of_decide_eq_true rfl
  | read point =>
    cases point with
    | boot | done => exact of_decide_eq_true rfl
    | parse point | extract point => fin_cases point <;> exact of_decide_eq_true rfl
  | done => exact of_decide_eq_true rfl

theorem statementClock_cached8 (cache : List Bool) (current : State C) :
    Cost.statementClock (program .halt) (Frame.configuration 8 cache current)=
      Cost.statementClock (program .halt) current := by
  cases current with
  | mk position memory contents =>
    cases position with
    | none => rfl
    | some point =>
      exact Frame.clock_configuration Work 8 (by decide) cache _ (program_accesses point) memory contents

theorem traceClockSum_cached8 (cache : List Bool) (run : List (State C)) :
    Cost.traceClockSum (program .halt) (run.map (Frame.configuration 8 cache))=
      Cost.traceClockSum (program .halt) run := by
  induction run with
  | nil => rfl
  | cons current later ih =>
    cases later with
    | nil => rfl
    | cons next rest =>
      change Cost.statementClock (program .halt) (Frame.configuration 8 cache current)+
        Cost.traceClockSum (program .halt) ((next::rest).map (Frame.configuration 8 cache))=
        Cost.statementClock (program .halt) current+Cost.traceClockSum (program .halt) (next::rest)
      rw [statementClock_cached8,ih]

theorem chargedCost_cached8 (cache : List Bool) (run : List (State C)) :
    Cost.chargedCost (program .halt) (run.map (Frame.configuration 8 cache))=
      Cost.chargedCost (program .halt) run := by
  simp only [Cost.chargedCost,List.length_map,traceClockSum_cached8]

/-- Internal entry accepts a physically present cache. The source never
accesses8, so the very same real prefix and exact charged cost are retained.
The original caller still has to produce that cache in its preceding trace. -/
theorem actual_cached8 (memory : RawGetter.Store C) (native : RatInput.Complement.CalleeFlags)
    (reader : RatInput.Complement.Reader) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord)
    (cache : List Bool) :
    ∃ original final beforeRead,Facts (program .halt) memory native reader E target word original final beforeRead ∧
      let run:=original.map (Frame.configuration 8 cache)
      run.head?=some (Frame.configuration 8 cache (entry memory native reader (wordInput E target word))) ∧
      run.IsChain (fun before after => TM2.step (program .halt) before=some after) ∧
      run.getLast?=some (Frame.configuration 8 cache final) ∧
      (Frame.configuration 8 cache final).stk 8=cache ∧
      (Frame.configuration 8 cache final).stk 15=RatInput.Encoder.packet E.observationFee
        (RatInput.Encoder.packet (1-E.priorOne) (RatInput.Encoder.packet E.priorOne [])) ∧
      Cost.traceClockSum (program .halt) run ≤ coefficient^2*((wordInput E target word).length+1)^32 ∧
      Cost.chargedCost (program .halt) run ≤ Cost.chargedCoefficient*((wordInput E target word).length+1)^32 := by
  obtain ⟨original,final,beforeRead,facts⟩:=actual_polynomial memory native reader E target word
  refine ⟨original,final,beforeRead,facts,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [List.head?_map,facts.first,Option.map_some]
  · exact Frame.chain_configuration Work 8 (by decide) cache (program .halt) program_accesses original facts.chain
  · rw [List.getLast?_map,facts.last,Option.map_some]
  · change Function.update final.stk (8 : RatInput.Stack) cache 8=cache
    exact Function.update_self _ _ _
  · change Function.update final.stk 8 cache 15=_
    rw [Function.update_of_ne (by decide : (15:RatInput.Stack)≠8),facts.packet]
  · rw [traceClockSum_cached8]
    exact Cost.traceClockSum_le facts
  · rw [chargedCost_cached8]
    exact Cost.chargedCost_le facts

end B23_4_RatWordPrep.OriginalFee
