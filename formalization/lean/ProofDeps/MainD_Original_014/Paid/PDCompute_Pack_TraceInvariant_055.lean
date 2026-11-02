module
public import Paid.PDCompute_Pack_PrefixJoin_016
public import Paid.PDCompute_SolverSmallTraceMemory_061
public import Paid.PDMenu_ComputeFrame_007

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute linearExecute_append)

/-- The existing actual fetched ISA refinement transports ANY proved
successful-prefix invariant, including physical memory and operand bits. -/
theorem linearExecute_trace_invariant (program : Program) (input : List Cell) (code : List Instruction)
    (straight : StraightCode code) (before after : State)
    (fetched : FetchesCode program before.pc code) (run : linearExecute input code before=some after)
    (invariant : State → Prop)
    (prefixes : ∀ count ≤ code.length,∀ state,
      linearExecute input (code.take count) before=some state → invariant state) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace ≤ 15*(code.length+1) ∧ ∀ state∈trace,invariant state := by
  obtain ⟨trace,hh,hl,hchain,ht,actualPrefixes⟩:=linearExecute_trace_time program input code straight before after fetched run
  refine ⟨trace,hh,hl,hchain,ht,?_⟩
  intro state member
  have split:=List.dropLast_append_getLast? after (by rw [hl];simp)
  rw [←split] at member
  rcases List.mem_append.mp member with earlier|last
  · obtain ⟨count,bound,execute⟩:=actualPrefixes state earlier
    exact prefixes count bound.le state execute
  · have eq : state=after:=by simpa only [List.mem_singleton] using last
    subst state
    exact prefixes code.length (le_refl _) after (by simpa only [List.take_length] using run)

theorem invariant_prefix_append (input : List Cell) (first later : List Instruction) (before middle : State)
    (run : linearExecute input first before=some middle) (invariant : State → Prop)
    (firstPrefixes : ∀ count ≤ first.length,∀ state,
      linearExecute input (first.take count) before=some state → invariant state)
    (laterPrefixes : ∀ count ≤ later.length,∀ state,
      linearExecute input (later.take count) middle=some state → invariant state) :
    ∀ count ≤ (first++later).length,∀ state,
      linearExecute input ((first++later).take count) before=some state → invariant state := by
  intro count bound state execute
  by_cases short : count ≤ first.length
  · rw [List.take_append_of_le_length short] at execute
    exact firstPrefixes count short state execute
  · rw [List.take_append,List.take_of_length_le (by omega),linearExecute_append,run,Option.bind_some] at execute
    exact laterPrefixes (count-first.length) (by simp only [List.length_append] at bound;omega) state execute

theorem joinTrace_invariant (first later : List State) (invariant : State → Prop)
    (firstStates : ∀ state∈first,invariant state) (laterStates : ∀ state∈later,invariant state) :
    ∀ state∈joinTrace first later,invariant state := by
  intro state member
  rcases List.mem_append.mp member with earlier|last
  · exact firstStates state (List.mem_of_mem_dropLast earlier)
  · exact laterStates state last

end PDCompute.Pack
