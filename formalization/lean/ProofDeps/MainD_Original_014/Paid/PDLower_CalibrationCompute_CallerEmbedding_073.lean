module

public import Paid.PDLower_CalibrationCompute_Segment_025
public import Paid.PDLower_CalibrationCompute_StandaloneSegment_057

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

namespace PDLower.CalibrationCompute

/-- A successful preterminal step of a located program must fetch inside
the real code: padding consists of HALT, whose execution cannot succeed. -/
theorem located_step_scope (origin : ℕ) (code : Program) (input : List Cell) (before after : State)
    (actual : step (locatedBlock origin code) input before=some after) :
    origin≤before.pc ∧ before.pc<origin+code.size := by
  obtain ⟨instruction,fetched,executed⟩ := Option.bind_eq_some_iff.mp actual
  constructor
  · by_contra notLower
    have lower : before.pc<origin := by omega
    have halt : (locatedBlock origin code)[before.pc]?=some .halt := by
      unfold locatedBlock
      rw [Array.getElem?_append_left (by simpa only [Array.size_replicate] using lower)]
      simp only [Array.getElem?_replicate,lower,ite_true]
    have equal : instruction=.halt := Option.some.inj (fetched.symm.trans halt)
    subst instruction
    change (none : Option State)=some after at executed
    cases executed
  · obtain ⟨inside,_value⟩ := Array.getElem?_eq_some_iff.mp fetched
    simpa only [locatedBlock,Array.size_append,Array.size_replicate] using inside

theorem located_chain_scope (origin : ℕ) (code : Program) (input : List Cell) (trace : List State)
    (chain : trace.IsChain (fun a b => step (locatedBlock origin code) input a=some b)) :
    ∀ state∈trace.dropLast,origin≤state.pc ∧ state.pc<origin+code.size := by
  revert chain
  induction trace with
  | nil => intro chain; simp
  | cons first rest ih =>
    intro chain
    cases rest with
    | nil => simp
    | cons next rest =>
      have edges := List.isChain_cons_cons.mp chain
      intro state member
      simp only [List.dropLast_cons_cons,List.mem_cons] at member
      rcases member with equal|later
      · subst state
        exact located_step_scope origin code input first next edges.1
      · exact ih edges.2 state later

/-- Embed a proved real calibration fragment into any actual caller and
readonly input. The scope is derived from the original successful chain,
not added as a fetch oracle or a further caller premise. -/
theorem Segment.inCaller {beforeCode suffix : Program} {leftInput rightInput : List Cell}
    {before after : State} {budget : ℕ}
    (actual : Segment beforeCode.size leftInput before after budget) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun a b => step (beforeCode++kernel beforeCode.size++suffix) rightInput a=some b) ∧
      time (beforeCode++kernel beforeCode.size++suffix) trace≤budget+15 := by
  obtain ⟨trace,head,last,chain,cost⟩ := actual
  have embedded := kernel_chain_in_caller beforeCode suffix leftInput rightInput trace
    (located_chain_scope beforeCode.size (kernel beforeCode.size) leftInput trace chain) chain
  exact ⟨trace,head,last,embedded.1,embedded.2.trans (Nat.add_le_add_right cost 15)⟩

theorem Segment.inStandalone {leftInput rightInput : List Cell} {before after : State} {budget : ℕ}
    (actual : Segment 1 leftInput before after budget) :
    StandaloneSegment rightInput before after (budget+15) := by
  exact actual.inCaller (beforeCode:=#[Instruction.jump mainStart]) (suffix:=bootstrap mainStart)

end PDLower.CalibrationCompute
