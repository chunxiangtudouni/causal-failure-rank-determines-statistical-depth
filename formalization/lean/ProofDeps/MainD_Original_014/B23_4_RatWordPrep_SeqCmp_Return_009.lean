module

public import B23_4_RatWordPrep_SeqCmp_Public_007

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.SeqCmp

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool

variable {C : Type*}

theorem emit_next (before after : State C) (active : before.l=some .emit)
    (edge : TM2.step (program .halt) before=some after) : after.l=some .done := by
  cases before with
  | mk position memory contents =>
    change position=some .emit at active
    subst position
    exact (congrArg (fun state : State C => state.l) (Option.some.inj edge)).symm

theorem done_next (before after : State C) (active : before.l=some .done)
    (edge : TM2.step (program .halt) before=some after) : after.l=none := by
  cases before with
  | mk position memory contents =>
    change position=some .done at active
    subst position
    exact (congrArg (fun state : State C => state.l) (Option.some.inj edge)).symm

/-- A round returns at emit. Its preceding path cannot already have
executed emit: that would enter done, halt, and lose the active return. -/
theorem no_early_emit (trace : List (State C)) (final : State C)
    (chain : trace.IsChain (fun a b => TM2.step (program .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some .emit) :
    ∀ current∈trace.dropLast,current.l≠some .emit := by
  induction trace with
  | nil => simp
  | cons before rest ih =>
    cases rest with
    | nil => simp
    | cons next rest =>
      obtain ⟨edge,tailChain⟩ := List.isChain_cons_cons.mp chain
      intro current member
      rw [List.dropLast_cons_cons] at member
      rcases List.mem_cons.mp member with rfl | later
      · intro selected
        have nextActive := emit_next current next selected edge
        cases rest with
        | nil =>
          have same : next=final := Option.some.inj last
          rw [←same,nextActive] at active
          cases active
        | cons after rest =>
          obtain ⟨second,backChain⟩ := List.isChain_cons_cons.mp tailChain
          have inactive := done_next next after nextActive second
          cases rest with
          | nil =>
            have same : after=final := Option.some.inj last
            rw [←same,inactive] at active
            cases active
          | cons further rest =>
            have impossible := (List.isChain_cons_cons.mp backChain).1
            cases after with
            | mk position memory contents =>
              change position=none at inactive
              subst position
              cases impossible
      · exact ih tailChain last current later

end B23_4_RatWordPrep.SeqCmp
