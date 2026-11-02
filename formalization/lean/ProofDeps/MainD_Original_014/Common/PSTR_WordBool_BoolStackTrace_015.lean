module

public import Common.PSTR_WordBool_BoolStackRefines_014
public import Common.PSTR_WordBool_NativeTrace_006

/-! Reuse a REAL old Bool-machine path as a real two-stack source path.
The final old NONE executes one extra source macro before true source HALT.
Workspace and the quantitative general stack compiler remain separate. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.BoolStackTrace

open Turing BoolOnStacks BoolStackStep BoolStackRefines

variable {states : Nat}

theorem reconstruct (before : State states) (active : before.l = some ()) :
    cfg (some ()) before.var.1 before.var.2 (before.stk 1) (before.stk 0) = before := by
  cases before with
  | mk label store cells =>
    cases store with
    | mk control scratch =>
      change label = some () at active
      subst label
      have same : PushPop.stackContents (cells 0) (cells 1) = cells := by
        funext slot
        fin_cases slot <;> rfl
      exact congrArg (fun slots => (⟨some (), (control, scratch), slots⟩ : State states)) same

theorem advance (machine : TM0.Machine Bool (Fin (states + 1)))
    (before : State states) (oldAfter : TM0.Cfg Bool (Fin (states + 1)))
    (active : before.l = some ())
    (oldStep : TM0.step machine (representedState before) = some oldAfter) :
    ∃ after, TM2.step (program machine) before = some after ∧
      after.l = some () ∧ representedState after = oldAfter := by
  have canonical := reconstruct before active
  obtain ⟨after, edge, alternatives⟩ := macro_refines machine before.var.1 before.var.2
    (before.stk 1) (before.stk 0)
  rw [canonical] at edge alternatives
  rcases alternatives with stopped | ⟨next, nativeEdge, live, representation⟩
  · rw [oldStep] at stopped
    cases stopped.1
  · have same : next = oldAfter := Option.some.inj (nativeEdge.symm.trans oldStep)
    exact ⟨after, edge, live, representation.trans same⟩

theorem terminate (machine : TM0.Machine Bool (Fin (states + 1)))
    (before : State states) (active : before.l = some ())
    (oldHalt : TM0.step machine (representedState before) = none) :
    ∃ after, TM2.step (program machine) before = some after ∧
      after.l = none ∧ representedState after = representedState before := by
  have canonical := reconstruct before active
  obtain ⟨after, edge, alternatives⟩ := macro_refines machine before.var.1 before.var.2
    (before.stk 1) (before.stk 0)
  rw [canonical] at edge alternatives
  rcases alternatives with stopped | ⟨next, nativeEdge, _, _⟩
  · exact ⟨after, edge, stopped.2.1, stopped.2.2⟩
  · rw [oldHalt] at nativeEdge
    cases nativeEdge

theorem source_halted (machine : TM0.Machine Bool (Fin (states + 1)))
    (final : State states) (done : final.l = none) : TM2.step (program machine) final = none := by
  cases final with
  | mk label store cells =>
    change label = none at done
    subst label
    rfl

theorem lift_path (machine : TM0.Machine Bool (Fin (states + 1)))
    (start : State states) (oldStart oldFinal : TM0.Cfg Bool (Fin (states + 1)))
    (rest : List (TM0.Cfg Bool (Fin (states + 1))))
    (active : start.l = some ()) (representation : representedState start = oldStart)
    (chain : (oldStart :: rest).IsChain (fun before after => TM0.step machine before = some after))
    (last : (oldStart :: rest).getLast? = some oldFinal) :
    ∃ posts final,
      posts.length = rest.length ∧
      (start :: posts).IsChain (fun before after => TM2.step (program machine) before = some after) ∧
      (start :: posts).getLast? = some final ∧ final.l = some () ∧
      representedState final = oldFinal := by
  induction rest generalizing start oldStart with
  | nil =>
    refine ⟨[], start, rfl, List.isChain_singleton _, rfl, active, ?_⟩
    exact representation.trans (Option.some.inj last)
  | cons next rest ih =>
    obtain ⟨oldEdge, oldTail⟩ := List.isChain_cons_cons.mp chain
    have mappedEdge : TM0.step machine (representedState start) = some next := by
      rw [representation]
      exact oldEdge
    obtain ⟨sourceNext, sourceEdge, sourceActive, sourceRepresentation⟩ :=
      advance machine start next active mappedEdge
    obtain ⟨later, final, length, tailChain, tailLast, finalActive, finalRepresentation⟩ :=
      ih sourceNext next sourceActive sourceRepresentation oldTail last
    refine ⟨sourceNext :: later, final, ?_,
      List.isChain_cons_cons.mpr ⟨sourceEdge, tailChain⟩, tailLast,
      finalActive, finalRepresentation⟩
    simp only [List.length_cons, length]

theorem actual_source_trace (machine : TM0.Machine Bool (Fin (states + 1)))
    (input : List Bool) (oldTrace : List (TM0.Cfg Bool (Fin (states + 1))))
    (oldFinal : TM0.Cfg Bool (Fin (states + 1)))
    (first : oldTrace.head? = some (TM0.init input))
    (chain : oldTrace.IsChain (fun before after => TM0.step machine before = some after))
    (last : oldTrace.getLast? = some oldFinal) (halt : TM0.step machine oldFinal = none) :
    ∃ (trace : List (State states)) (final : State states),
      trace.head? = some (TM2.init (Γ := PushPop.Alphabet) (Λ := Unit) (σ := Store states) 0 input) ∧
      trace.IsChain (fun before after => TM2.step (program machine) before = some after) ∧
      trace.getLast? = some final ∧ TM2.step (program machine) final = none ∧
      representedState final = oldFinal ∧ trace.length = oldTrace.length + 1 := by
  cases oldTrace with
  | nil => simp at first
  | cons oldStart rest =>
    have initial : oldStart = TM0.init input := Option.some.inj first
    subst oldStart
    let start : State states := TM2.init 0 input
    obtain ⟨posts, beforeHalt, length, sourceChain, sourceLast, live, representation⟩ :=
      lift_path machine start (TM0.init input) oldFinal rest rfl
        (BoolOnStacks.initial_map input) chain last
    have actualHalt : TM0.step machine (representedState beforeHalt) = none := by
      rw [representation]
      exact halt
    obtain ⟨final, haltEdge, done, unchanged⟩ := terminate machine beforeHalt live actualHalt
    have lastPair : (beforeHalt :: [final]).IsChain
        (fun before after => TM2.step (program machine) before = some after) :=
      List.isChain_cons_cons.mpr ⟨haltEdge, List.isChain_singleton _⟩
    refine ⟨(start :: posts) ++ [final], final, rfl,
      NativeTrace.join_chain _ _ _ sourceLast sourceChain lastPair, ?_,
      source_halted machine final done, unchanged.trans representation, ?_⟩
    · exact List.getLast?_append_cons (start :: posts) final []
    · simp only [List.length_append, List.length_cons, List.length_nil, length]

end PaperProofs.Common.Native.PSTRWordBool.BoolStackTrace
