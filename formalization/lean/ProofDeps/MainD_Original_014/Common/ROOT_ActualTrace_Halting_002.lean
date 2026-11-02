module
public import Common.ROOT_ActualTrace_FirstExit_001

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace ROOT.ActualTrace
universe u
variable {α : Type u}

theorem next_some_of_mem_dropLast (next : α → Option α) : ∀ trace : List α,
    trace.IsChain (fun before after=>next before=some after)→
    ∀ state∈trace.dropLast,∃ successor,next state=some successor := by
  intro trace
  induction trace with
  | nil => intro _ state member;simp at member
  | cons a tail ih =>
    intro chain state member
    cases tail with
    | nil => simp at member
    | cons b rest =>
      rw [List.dropLast_cons_cons] at member
      rcases List.mem_cons.mp member with same|member
      · subst state;exact ⟨b,(List.isChain_cons_cons.mp chain).1⟩
      · exact ih (List.isChain_cons_cons.mp chain).2 state member

/-- A full halting run is a special first exit. Interior nonhalting is
derived from the actual chain, rather than separately assumed. -/
structure FullHaltingRuns (next : α → Option α) (start : α) (trace : List α) : Prop where
  head : trace.head?=some start
  chain : trace.IsChain (fun before after=>next before=some after)
  last : ∀ state,trace.getLast?=some state→next state=none

theorem FullHaltingRuns.firstExit {next : α → Option α} {start : α} {trace : List α}
    (run : FullHaltingRuns next start trace) : FirstExit next (fun state=>next state=none) start trace := by
  refine ⟨run.head,run.chain,run.last,?_⟩
  intro state member halted
  obtain ⟨successor,step⟩:=next_some_of_mem_dropLast next trace run.chain state member
  rw [halted] at step
  cases step

theorem FullHaltingRuns.unique {next : α → Option α} {start : α} {left right : List α}
    (first : FullHaltingRuns next start left) (second : FullHaltingRuns next start right) : left=right:=
  first.firstExit.unique second.firstExit

end ROOT.ActualTrace
