module

public import Common.PSTR_WordBool_WordNatRun_045

/-! The actual formatter is an active-ended component of ONE fixed caller
machine. The target's caller statement may differ at the unexecuted port6;
the component retains arbitrary finite caller context and every other stack. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.WordNatIO

open Turing
open PaperProofs.Common.Native.RationalControllerComputation

theorem no_early_port (trace : List State) (final : State)
    (chain : trace.IsChain (fun before after => TM2.step (program .halt) before = some after))
    (last : trace.getLast? = some final) (active : final.l = some 6) :
    ∀ current ∈ trace.dropLast, current.l ≠ some 6 := by
  induction trace with
  | nil => simp
  | cons before rest ih =>
    cases rest with
    | nil => simp
    | cons next rest =>
      obtain ⟨edge, tailChain⟩ := List.isChain_cons_cons.mp chain
      intro current present
      rw [List.dropLast_cons_cons] at present
      rcases List.mem_cons.mp present with same | later
      · subst current
        intro port
        have stopped : TM2.step (program .halt) before =
            some (⟨none, before.var, before.stk⟩ : State) := by
          cases before with
          | mk label memory slots =>
            change label = some 6 at port
            subst label
            rfl
        rw [stopped] at edge
        have nextStopped := (Option.some.inj edge).symm
        cases rest with
        | nil =>
          have nextFinal : next = final := Option.some.inj last
          have inactive : final.l = none := by rw [← nextFinal, nextStopped]
          rw [inactive] at active
          cases active
        | cons after rest =>
          have impossible := (List.isChain_cons_cons.mp tailChain).1
          rw [nextStopped] at impossible
          cases impossible
      · exact ih tailChain last current later

variable {C : Type*}

abbrev CallerStatement (C : Type*) := TM2.Stmt Alphabet Label (C × Store)
abbrev CallerState (C : Type*) := TM2.Cfg Alphabet Label (C × Store)

def callerProgram (caller : CallerStatement C) (label : Label) : CallerStatement C :=
  if label = 6 then caller else ContextLift.statement (program .halt label)

theorem actual_caller_format (caller : CallerStatement C) (context : C)
    (background : Stack → List Bool) (memory : Store) (word output : List Bool) :
    ∃ trace : List (CallerState C),
      trace.head? = some (ContextLift.configuration context (state background 0 memory word [] output [])) ∧
      trace.IsChain (fun before after => TM2.step (callerProgram caller) before = some after) ∧
      trace.getLast? = some (ContextLift.configuration context
        (state background 6 (false, false) [] []
          (encodeNat (PSTRTMIncrement009.valueDigits word) ++ output) [])) ∧
      trace.length ≤ 4 * word.length + 11 ∧
      (∀ current ∈ trace, current.var.1 = context) ∧
      (∀ current ∈ trace, ∀ slot,
        (current.stk slot).length ≤ (background slot).length + output.length + 3 * word.length + 3) ∧
      (∀ current ∈ trace, ∀ slot, slot ≠ 3 → slot ≠ 1 → slot ≠ 0 → slot ≠ 12 →
        current.stk slot = background slot) := by
  obtain ⟨trace, first, chain, last, length, bounds, frames⟩ :=
    actual_format_frames .halt background memory word output
  have code : ∀ current ∈ trace.dropLast, ∀ label, current.l = some label →
      callerProgram caller label = ContextLift.statement (program .halt label) := by
    intro current present label selected
    have different : label ≠ 6 := by
      intro equal
      subst label
      exact no_early_port trace _ chain last rfl current present selected
    exact ite_eq_right different
  obtain ⟨liftedFirst, liftedChain, liftedLast, liftedLength, _projection, liftedFrames⟩ :=
    ContextLift.actual_path_on (program .halt) (callerProgram caller) context trace _ _
      first chain last code
  refine ⟨trace.map (ContextLift.configuration context), liftedFirst, liftedChain, liftedLast,
    by omega, ?_, ?_, ?_⟩
  · intro current present
    exact (liftedFrames current present).1
  · intro current present slot
    obtain ⟨old, member, same⟩ := List.mem_map.mp present
    subst current
    exact bounds old member slot
  · intro current present slot notWord notLeft notOutput notCounter
    obtain ⟨old, member, same⟩ := List.mem_map.mp present
    subst current
    exact frames old member slot notWord notLeft notOutput notCounter

end PaperProofs.Common.Native.PSTRWordBool.WordNatIO
