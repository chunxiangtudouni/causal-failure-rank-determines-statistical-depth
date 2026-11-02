module

public import Paid.PDCompute_SolverChoiceLayout_100
public import Paid.PDCompute_SolverHeaderFrame_099

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

/-- Schema for an ACTUAL fetched header-only fragment. This library
predicate is not an original implementation claim or an assumed oracle. -/
def HeaderBlockRun (program : Program) (input : List Cell) (before : State) (base n k : ℕ)
    (values : ℕ → Cell) (finish cost : ℕ) : Prop :=
  ∃ trace : List State, ∃ after : State,
    trace.head?=some before ∧ trace.getLast?=some after ∧
    trace.IsChain (fun first later => step program input first=some later) ∧ time program trace ≤ cost ∧
    Header after base values ∧ after.register .fresh=.natural base ∧ after.pc=finish ∧
    Frame before after base n k ∧ after.output=before.output ∧
    ∀ state ∈ trace,HeaderMemory before state base

/-- Composes independently PROVED actual guard/body traces and the
literal jump of choiceCode. Concrete callers must supply genuine local
execution proofs, not use these premises as a full D27 conclusion. -/
theorem choice_compose_memory (guard : ℕ → ℕ → List Instruction) (first second : ℕ → List Instruction)
    (size : ∀ a b,(guard a b).length=8) (program : Program) (input : List Cell)
    (before : State) (base n k origin firstCost secondCost : ℕ)
    (values firstValues secondValues : ℕ → Cell) (truth : Bool)
    (fetch : FetchesCode program origin (choiceCode guard first second origin))
    (guarded : HeaderBlockRun program input before base n k values
      (if truth then choiceFirstPC origin else choiceSecondPC first origin) 135)
    (firstRun : ∀ state : State, truth=true → state.pc=choiceFirstPC origin →
      Header state base values → state.register .fresh=.natural base → HeaderMemory before state base →
      FetchesCode program state.pc (first (choiceFirstPC origin)) →
      HeaderBlockRun program input state base n k firstValues
        (choiceFirstPC origin+(first (choiceFirstPC origin)).length) firstCost)
    (secondRun : ∀ state : State, truth=false → state.pc=choiceSecondPC first origin →
      Header state base values → state.register .fresh=.natural base → HeaderMemory before state base →
      FetchesCode program state.pc (second (choiceSecondPC first origin)) →
      HeaderBlockRun program input state base n k secondValues (choiceEndPC first second origin) secondCost) :
    HeaderBlockRun program input before base n k (if truth then firstValues else secondValues)
      (choiceEndPC first second origin) (165+firstCost+secondCost) := by
  obtain ⟨guardTrace,tested,guardHead,guardLast,guardChain,guardTime,testedHeader,testedBase,testedPC,guardFrame,guardOutput,guardMemory⟩:=guarded
  have testedMemory:=HeaderMemory.trace_last guardMemory guardLast
  cases truth with
  | false =>
    have atSecond : tested.pc=choiceSecondPC first origin := testedPC
    have secondFetch : FetchesCode program tested.pc (second (choiceSecondPC first origin)) := by
      rw [atSecond]
      exact choice_second_fetch guard first second size program origin fetch
    obtain ⟨body,after,bodyHead,bodyLast,bodyChain,bodyTime,afterHeader,afterBase,afterPC,afterFrame,afterOutput,bodyMemory⟩ :=
      secondRun tested rfl atSecond testedHeader testedBase testedMemory secondFetch
    have joined:=joinTrace_spec program input guardTrace body before tested after 135 secondCost
      guardHead guardLast bodyHead bodyLast guardChain bodyChain guardTime bodyTime
    refine ⟨joinTrace guardTrace body,after,joined.1,joined.2.1,joined.2.2.1,?_,?_,afterBase,afterPC,
      guardFrame.trans afterFrame,afterOutput.trans guardOutput,
      joinTrace_memory guardTrace body before tested base guardLast guardMemory bodyMemory⟩
    · have bound:=joined.2.2.2
      omega
    · exact afterHeader
  | true =>
    have atFirst : tested.pc=choiceFirstPC origin := testedPC
    have firstFetch : FetchesCode program tested.pc (first (choiceFirstPC origin)) := by
      rw [atFirst]
      exact choice_first_fetch guard first second size program origin fetch
    obtain ⟨body,completed,bodyHead,bodyLast,bodyChain,bodyTime,completedHeader,completedBase,completedPC,bodyFrame,bodyOutput,bodyMemory⟩ :=
      firstRun tested rfl atFirst testedHeader testedBase testedMemory firstFetch
    have jumpFetch : program[completed.pc]?=some (.jump (choiceEndPC first second origin)) := by
      rw [completedPC]
      exact choice_jump_fetch guard first second size program origin fetch
    let returned:=jumpResult completed (choiceEndPC first second origin)
    let jumpTrace:=[completed,returned]
    obtain ⟨jumpHead,jumpLast,jumpChain,jumpTime,jumpStorage⟩ :=
      jump_trace_storage program input completed (choiceEndPC first second origin) jumpFetch
    have jumpMemory : ∀ state ∈ jumpTrace,HeaderMemory completed state base := by
      intro state member
      have storage:=jumpStorage state member
      exact HeaderMemory.of_unchanged base storage.1 storage.2.1 storage.2.2
    have jumpFrame : Frame completed returned base n k := ⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩
    have firstJoin:=joinTrace_spec program input guardTrace body before tested completed 135 firstCost
      guardHead guardLast bodyHead bodyLast guardChain bodyChain guardTime bodyTime
    have firstMemory:=joinTrace_memory guardTrace body before tested base guardLast guardMemory bodyMemory
    have secondJoin:=joinTrace_spec program input (joinTrace guardTrace body) jumpTrace before completed returned (135+firstCost) 30
      firstJoin.1 firstJoin.2.1 jumpHead jumpLast firstJoin.2.2.1 jumpChain firstJoin.2.2.2 jumpTime
    refine ⟨joinTrace (joinTrace guardTrace body) jumpTrace,returned,secondJoin.1,secondJoin.2.1,secondJoin.2.2.1,?_,?_,
      completedBase,rfl,guardFrame.trans (bodyFrame.trans jumpFrame),bodyOutput.trans guardOutput,
      joinTrace_memory (joinTrace guardTrace body) jumpTrace before completed base firstJoin.2.1 firstMemory jumpMemory⟩
    · have bound:=secondJoin.2.2.2
      omega
    · exact completedHeader

end PDCompute.Solver
