module

public import Paid.PDCompute_SolverChoiceBits_176
public import Paid.PDCompute_SolverChoicePost_116

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame

/-- Real conditional composition when the selected scan determines
the final Header existentially. Concrete literal executions supply the
two branch proofs; postconditions and bits stay on that SAME trace. -/
theorem choice_compose_post_bits (guard : ℕ → ℕ → List Instruction) (first second : ℕ → List Instruction)
    (size : ∀ a b,(guard a b).length=8) (program : Program) (input : List Cell)
    (before : State) (base n k origin budget firstCost secondCost : ℕ) (values : ℕ → Cell) (truth : Bool)
    (post : (ℕ → Cell) → Prop) (fetch : FetchesCode program origin (choiceCode guard first second origin))
    (endBits : natBits (choiceEndPC first second origin)≤budget)
    (guarded : HeaderBlockBits program input before base n k budget values
      (if truth then choiceFirstPC origin else choiceSecondPC first origin) 135)
    (firstRun : ∀ state : State,truth=true → state.pc=choiceFirstPC origin → Header state base values →
      state.register .fresh=.natural base → HeaderMemory before state base → RootD27.Bits.SafeBits state budget →
      FetchesCode program state.pc (first (choiceFirstPC origin)) →
      ∃ next,HeaderBlockBits program input state base n k budget next
        (choiceFirstPC origin+(first (choiceFirstPC origin)).length) firstCost ∧ post next)
    (secondRun : ∀ state : State,truth=false → state.pc=choiceSecondPC first origin → Header state base values →
      state.register .fresh=.natural base → HeaderMemory before state base → RootD27.Bits.SafeBits state budget →
      FetchesCode program state.pc (second (choiceSecondPC first origin)) →
      ∃ next,HeaderBlockBits program input state base n k budget next (choiceEndPC first second origin) secondCost ∧ post next) :
    ∃ next,HeaderBlockBits program input before base n k budget next (choiceEndPC first second origin) (165+firstCost+secondCost) ∧ post next := by
  obtain ⟨guardTrace,tested,guardHead,guardLast,guardChain,guardTime,testedHeader,testedBase,testedPC,guardFrame,guardOutput,guardMemory,guardSafe⟩:=guarded
  have testedMemory:=HeaderMemory.trace_last guardMemory guardLast
  have testedSafe:=guardSafe tested (List.mem_of_getLast? guardLast)
  cases truth with
  | false =>
    have atSecond : tested.pc=choiceSecondPC first origin := testedPC
    have secondFetch : FetchesCode program tested.pc (second (choiceSecondPC first origin)) := by
      rw [atSecond]
      exact choice_second_fetch guard first second size program origin fetch
    obtain ⟨next,bodyRun,postNext⟩:=secondRun tested rfl atSecond testedHeader testedBase testedMemory testedSafe secondFetch
    obtain ⟨body,after,bodyHead,bodyLast,bodyChain,bodyTime,afterHeader,afterBase,afterPC,afterFrame,afterOutput,bodyMemory,bodySafe⟩:=bodyRun
    have joined:=joinTrace_spec program input guardTrace body before tested after 135 secondCost guardHead guardLast bodyHead bodyLast guardChain bodyChain guardTime bodyTime
    refine ⟨next,?_,postNext⟩
    refine ⟨joinTrace guardTrace body,after,joined.1,joined.2.1,joined.2.2.1,?_,afterHeader,afterBase,afterPC,
      guardFrame.trans afterFrame,afterOutput.trans guardOutput,
      joinTrace_memory guardTrace body before tested base guardLast guardMemory bodyMemory,
      PDCompute.Pack.joinTrace_invariant guardTrace body (fun state=>RootD27.Bits.SafeBits state budget) guardSafe bodySafe⟩
    have bound:=joined.2.2.2
    omega
  | true =>
    have atFirst : tested.pc=choiceFirstPC origin := testedPC
    have firstFetch : FetchesCode program tested.pc (first (choiceFirstPC origin)) := by
      rw [atFirst]
      exact choice_first_fetch guard first second size program origin fetch
    obtain ⟨next,bodyRun,postNext⟩:=firstRun tested rfl atFirst testedHeader testedBase testedMemory testedSafe firstFetch
    obtain ⟨body,completed,bodyHead,bodyLast,bodyChain,bodyTime,completedHeader,completedBase,completedPC,bodyFrame,bodyOutput,bodyMemory,bodySafe⟩:=bodyRun
    have jumpFetch : program[completed.pc]?=some (.jump (choiceEndPC first second origin)) := by
      rw [completedPC]
      exact choice_jump_fetch guard first second size program origin fetch
    let returned:=jumpResult completed (choiceEndPC first second origin)
    let jumpTrace:=[completed,returned]
    obtain ⟨jumpHead,jumpLast,jumpChain,jumpTime,jumpStorage⟩:=jump_trace_storage program input completed (choiceEndPC first second origin) jumpFetch
    have jumpMemory : ∀ state∈jumpTrace,HeaderMemory completed state base := by
      intro state member
      have storage:=jumpStorage state member
      exact HeaderMemory.of_unchanged base storage.1 storage.2.1 storage.2.2
    have completedSafe:=bodySafe completed (List.mem_of_getLast? bodyLast)
    have jumpSafe : ∀ state∈jumpTrace,RootD27.Bits.SafeBits state budget := by
      intro state member
      simp only [jumpTrace,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with same|same
      · subst state
        exact completedSafe
      · subst state
        exact completedSafe.withPC _ endBits
    have jumpFrame : Frame completed returned base n k := ⟨fun _ _=>rfl,fun _ _=>Iff.rfl⟩
    have firstJoin:=joinTrace_spec program input guardTrace body before tested completed 135 firstCost guardHead guardLast bodyHead bodyLast guardChain bodyChain guardTime bodyTime
    have firstMemory:=joinTrace_memory guardTrace body before tested base guardLast guardMemory bodyMemory
    have secondJoin:=joinTrace_spec program input (joinTrace guardTrace body) jumpTrace before completed returned (135+firstCost) 30
      firstJoin.1 firstJoin.2.1 jumpHead jumpLast firstJoin.2.2.1 jumpChain firstJoin.2.2.2 jumpTime
    refine ⟨next,?_,postNext⟩
    refine ⟨joinTrace (joinTrace guardTrace body) jumpTrace,returned,secondJoin.1,secondJoin.2.1,secondJoin.2.2.1,?_,completedHeader,
      completedBase,rfl,guardFrame.trans (bodyFrame.trans jumpFrame),bodyOutput.trans guardOutput,
      joinTrace_memory (joinTrace guardTrace body) jumpTrace before completed base firstJoin.2.1 firstMemory jumpMemory,
      PDCompute.Pack.joinTrace_invariant (joinTrace guardTrace body) jumpTrace (fun state=>RootD27.Bits.SafeBits state budget)
        (PDCompute.Pack.joinTrace_invariant guardTrace body (fun state=>RootD27.Bits.SafeBits state budget) guardSafe bodySafe) jumpSafe⟩
    have bound:=secondJoin.2.2.2
    omega

end PDCompute.Solver
