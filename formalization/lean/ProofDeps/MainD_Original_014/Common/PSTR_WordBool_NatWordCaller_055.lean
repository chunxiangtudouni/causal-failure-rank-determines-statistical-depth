module

public import Common.PSTR_WordBool_NatWordRun_054

/-! An actual reader component inside one fixed caller. The final port7
is not executed by this component; its statement may therefore be replaced
by the caller. Arbitrary caller context and all ten other stacks survive
every listed configuration. Fixed syntax bounds permit native040 reuse. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.NatWordIO

open Turing
open PaperProofs.Common.Native.RationalControllerComputation

theorem no_early_port (trace : List State) (final : State)
    (chain : trace.IsChain (fun before after => TM2.step (program .halt) before = some after))
    (last : trace.getLast? = some final) (active : final.l = some 7) :
    ∀ current ∈ trace.dropLast, current.l ≠ some 7 := by
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
            change label = some 7 at port
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

theorem program_actions (caller : Statement) (label : Label) (internal : label ≠ 7) :
    ScannerClock.actions (program caller label) ≤ 5 := by
  fin_cases label <;> norm_num [program, jump, ScannerClock.actions] at *

theorem program_pushes (caller : Statement) (label : Label) (internal : label ≠ 7) :
    AuxWorkspace.pushes (program caller label) ≤ 2 := by
  fin_cases label <;> norm_num [program, jump, AuxWorkspace.pushes] at *

variable {C : Type*}

abbrev CallerStatement (C : Type*) := TM2.Stmt Alphabet Label (C × Store)
abbrev CallerState (C : Type*) := TM2.Cfg Alphabet Label (C × Store)

def callerProgram (caller : CallerStatement C) (label : Label) : CallerStatement C :=
  if label = 7 then caller else ContextLift.statement (program .halt label)

theorem actual_caller_read (caller : CallerStatement C) (context : C)
    (background : Stack → List Bool) (memory : Store) (value width : Nat) (right left : List Bool)
    (same : ListBlank.mk right = ListBlank.mk (encodeNat value)) :
    ∃ (bits : List Bool) (trace : List (CallerState C)),
      trace.head? = some (ContextLift.configuration context
        (state background 0 memory right left [] [] (List.replicate width true) [])) ∧
      trace.IsChain (fun before after => TM2.step (callerProgram caller) before = some after) ∧
      trace.getLast? = some (ContextLift.configuration context
        (state background 7 (false, false) [] [] bits [] (List.replicate width true) [])) ∧
      bits.length = width ∧
      BitVec.ofNat width (PSTRTMIncrement009.valueDigits bits) = BitVec.ofNat width value ∧
      trace.length ≤ left.length + 3 * right.length + 2 * width + 13 ∧
      (∀ current ∈ trace, current.var.1 = context) ∧
      (∀ current ∈ trace, ∀ slot,
        (current.stk slot).length ≤ (background slot).length + right.length + left.length + width) ∧
      (∀ current ∈ trace, ∀ slot, slot ≠ 0 → slot ≠ 1 → slot ≠ 3 → slot ≠ 7 →
        slot ≠ 11 → slot ≠ 12 → current.stk slot = background slot) := by
  obtain ⟨bits, trace, first, chain, last, widthExact, meaning, length, bounded⟩ :=
    actual_read .halt background memory value width right left same
  have code : ∀ current ∈ trace.dropLast, ∀ label, current.l = some label →
      callerProgram caller label = ContextLift.statement (program .halt label) := by
    intro current present label selected
    have different : label ≠ 7 := by
      intro equal
      subst label
      exact no_early_port trace _ chain last rfl current present selected
    exact ite_eq_right different
  obtain ⟨liftedFirst, liftedChain, liftedLast, liftedLength, _projection, liftedFrames⟩ :=
    ContextLift.actual_path_on (program .halt) (callerProgram caller) context trace _ _
      first chain last code
  refine ⟨bits, trace.map (ContextLift.configuration context), liftedFirst, liftedChain, liftedLast,
    widthExact, meaning, by omega, ?_, ?_, ?_⟩
  · intro current present
    exact (liftedFrames current present).1
  · intro current present slot
    obtain ⟨old, member, equal⟩ := List.mem_map.mp present
    subst current
    exact read_bounds_stack background right.length left.length width old (bounded old member) slot
  · intro current present slot notRight notLeft notValue notReverse notWidth notUsed
    obtain ⟨old, member, equal⟩ := List.mem_map.mp present
    subst current
    exact read_bounds_frame background right.length left.length width old (bounded old member)
      slot notRight notLeft notValue notReverse notWidth notUsed

end PaperProofs.Common.Native.PSTRWordBool.NatWordIO
