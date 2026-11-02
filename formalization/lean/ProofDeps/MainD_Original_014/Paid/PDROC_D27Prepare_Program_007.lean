module

public import Paid.PDROC_D27Prepare_Program_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.D27Prepare.Program

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)
open PDMenu.ComputeFrame

/-- A genuine initial trace reaches page1 with only the six raw values
and literal constants initialized. No certificate or computed datum is read. -/
theorem prologue_trace (c0 c1 c2 c3 c4 c5 : Cell) :
    ∃ (after : State) (trace : List State),
      MemoryMatch after (initializedInputMemory c0 c1 c2 c3 c4 c5) ∧
      after.pc=pc 1 ∧ after.output=[] ∧
      trace.head?=some initial ∧ trace.getLast?=some after ∧
      trace.length=89 ∧
      trace.IsChain (fun first later => step program (sixInput c0 c1 c2 c3 c4 c5) first=some later) ∧
      time program trace ≤ 15*89 ∧
      ∀ state ∈ trace, (∃ count ≤ 87,
        linearExecute (sixInput c0 c1 c2 c3 c4 c5) (prologueBody.take count) initial=some state) ∨ state=after := by
  let input := sixInput c0 c1 c2 c3 c4 c5
  obtain ⟨middle,bodyExecute,middleMatch,middlePc',middleOutput⟩ := prologue_body_realize c0 c1 c2 c3 c4 c5
  have bodyFetch : FetchesCode program initial.pc prologueBody := by
    have h := fetches_page_part 0 (by decide) [] prologueBody (go 1) (by simpa only [pageCode,List.nil_append] using prologue_decompose)
    simpa [initial,pc] using h
  have jumpFetch : program[middle.pc]?=some (.jump (pc 1)) := by
    rw [middlePc']
    have h := fetches_page 0 (by decide) 87 (by decide)
    change program[87]?=some (.jump (pc 1)) at h
    exact h
  let after : State := {middle with pc:=pc 1}
  obtain ⟨body,trace,_,_,bodyLast,_,_,bodyStrict,wholeHead,wholeLast,wholeLength,wholeChain,wholeTime,wholeMembers⟩ :=
    literal_control_trace input prologueBody prologueBody_straight initial middle after bodyFetch bodyExecute
      (jump_step input middle (pc 1) jumpFetch)
  refine ⟨after,trace,?_,rfl,?_,wholeHead,wholeLast,?_,wholeChain,?_,?_⟩
  · exact ⟨middleMatch.heap,middleMatch.live,middleMatch.base⟩
  · exact middleOutput
  · simpa only [prologueBody_length] using wholeLength
  · simpa only [prologueBody_length] using wholeTime
  · intro state member
    rcases wholeMembers state member with inBody|equal
    · left
      simpa only [prologueBody_length] using body_trace_prefix input prologueBody initial middle body bodyLast bodyExecute bodyStrict state inBody
    · exact Or.inr equal


#check prologue_trace

/-- The final page emits exactly the cells0 through12 and fetches HALT.
The input is arbitrary here, as all output cells are read from actual live heap. -/
theorem emitPrepared_trace (input : List Cell) (before : State) (memory : SlotMemory)
    (matched : MemoryMatch before memory) (start : before.pc=pc 45)
    (live : ∀ address < 13, address ∈ memory.present) :
    ∃ (after : State) (trace : List State), MemoryMatch after memory ∧
      after.output=before.output++(List.range 13).map memory.value ∧
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.length=53 ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      program[after.pc]?=some .halt ∧ time program trace ≤ 15*53 ∧
      ∀ state ∈ trace.dropLast, ∃ count < 52,
        linearExecute input (emitPrepared.take count) before=some state := by
  obtain ⟨after,execute,matchAfter,outputAfter,pcAfter⟩ :=
    outputSequence_realize (List.range 13) input before memory matched (by simpa only [List.mem_range] using live)
  have length : emitPrepared.length=52 := rfl
  have fetch : FetchesCode program before.pc emitPrepared := by
    rw [start]
    exact fetches_page_part 45 (by decide) [] emitPrepared [.halt] rfl
  obtain ⟨trace,head,last,traceLength,chain,prefixStates⟩ :=
    literal_fragment_trace_length input emitPrepared (outputSequence_straight (List.range 13)) before after fetch execute
  refine ⟨after,trace,matchAfter,outputAfter,head,last,?_,chain,?_,?_,?_⟩
  · simpa only [length] using traceLength
  · have afterPc : after.pc=pc 45+52 := by simpa only [start,outputSequence_length,List.length_range] using pcAfter
    rw [afterPc]
    exact fetches_page 45 (by decide) 52 (by decide)
  · have bound := time_le_length program trace
    simpa only [traceLength,length] using bound
  · simpa only [length] using prefixStates


#check emitPrepared_trace

end PDROC.D27Prepare.Program
