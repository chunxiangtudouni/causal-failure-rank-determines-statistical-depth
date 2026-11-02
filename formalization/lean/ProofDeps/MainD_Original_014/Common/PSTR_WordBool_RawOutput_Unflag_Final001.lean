module

public import Common.PSTR_TM_UnblockTrace_019
public import Common.PSTR_TM_Seq_005

/-! The last, fully paid Bool-native decoder: the real Unblock019 run is
followed by a fixed two-label scan over its unary header and one final RIGHT.
The transition table receives neither a length nor an output certificate. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawOutput.Unflag

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005

/-- Label 0 reads the actual tape; FALSE charges one RIGHT and enters halt1. -/
def stripMachine : Machine 1 := fun label symbol =>
  if label.val = 0 then some (if symbol then 0 else 1, .move .right) else none

def stripState (label : Fin 2) (left right : List Bool) : MachineState 1 :=
  ⟨label, Tape.mk₂ left right⟩

def stripTrace : Nat → List Bool → List Bool → List (MachineState 1)
  | 0, left, bits => [stripState 0 left (false :: bits), stripState 1 (false :: left) bits]
  | n+1, left, bits =>
      stripState 0 left (List.replicate (n+1) true ++ false :: bits) ::
        stripTrace n (true :: left) bits

theorem strip_head (n : Nat) (left bits : List Bool) :
    (stripTrace n left bits).head? =
      some (stripState 0 left (List.replicate n true ++ false :: bits)) := by
  cases n <;> rfl

theorem strip_length (n : Nat) (left bits : List Bool) :
    (stripTrace n left bits).length = n+2 := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih => simp only [stripTrace, List.length_cons, ih]

theorem strip_last (n : Nat) (left bits : List Bool) :
    (stripTrace n left bits).getLast? =
      some (stripState 1 (false :: (List.replicate n true ++ left)) bits) := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
    have nonempty : stripTrace n (true :: left) bits ≠ [] := by
      intro empty
      have length := strip_length n (true :: left) bits
      simp [empty] at length
    rw [stripTrace, List.getLast?_cons_of_ne_nil nonempty, ih,
      PSTRTMHeader003.replicate_push]

theorem strip_chain (n : Nat) (left bits : List Bool) :
    (stripTrace n left bits).IsChain
      (fun before after => TM0.step stripMachine before = some after) := by
  induction n generalizing left with
  | zero =>
    simp [stripTrace, List.isChain_cons_cons, TM0.step, stripMachine, stripState, Tape.mk₂]
  | succ n ih =>
    rw [stripTrace]
    apply List.isChain_cons.mpr
    constructor
    · intro next present
      rw [strip_head] at present
      have same := Option.mem_some_iff.mp present
      subst next
      simp [TM0.step, stripMachine, stripState, Tape.mk₂, List.replicate_succ]
    · exact ih _

theorem strip_halt (left bits : List Bool) :
    TM0.step stripMachine (stripState 1 left bits) = none := by
  simp [TM0.step, stripMachine, stripState]

/-- The western archive is arbitrary; the final head is exactly past FALSE. -/
theorem strip_runsFrom (n : Nat) (left bits : List Bool) :
    RunsFrom stripMachine
      ⟨0, Tape.mk₂ left (List.replicate n true ++ false :: bits)⟩
      (stripTrace n left bits)
      (stripState 1 (false :: (List.replicate n true ++ left)) bits) :=
  ⟨strip_head n left bits, strip_chain n left bits, strip_last n left bits,
    strip_halt _ _⟩

/-- One fixed transition table with twenty-two labels, including final halt21. -/
def unflagMachine : Machine 21 := seqMachine PSTRTMUnblock018.unblockMachine stripMachine
def unflagEntry : Fin 22 := 0
def unflagHalt : Fin 22 := 21
def unflagCoefficient : Nat := 128

def unflagTrace (bits : List Bool) : List (MachineState 21) :=
  (PSTRTMUnblockTrace019.unblockTrace bits).map (leftCfg (b := 1)) ++
    (stripTrace bits.length [false] bits).map (rightCfg (a := 19))

def unflagFinal (bits : List Bool) : MachineState 21 :=
  rightCfg (a := 19)
    (stripState 1 (false :: (List.replicate bits.length true ++ [false])) bits)

theorem unflag_runs (bits : List Bool) :
    Runs unflagMachine (PSTRTMIncrement009.blocks bits) (unflagTrace bits) (unflagFinal bits) := by
  apply seq_runs PSTRTMUnblock018.unblockMachine stripMachine
    (PSTRTMIncrement009.blocks bits)
    (PSTRTMUnblock018.state 19 [false] (PSTRTMUnblockTrace019.rawWord bits))
    (stripState 1 (false :: (List.replicate bits.length true ++ [false])) bits)
    (PSTRTMUnblockTrace019.unblockTrace bits) (stripTrace bits.length [false] bits)
    (PSTRTMUnblockTrace019.unblock_runs bits)
  simpa only [PSTRTMUnblock018.state, PSTRTMUnblockTrace019.rawWord] using
    strip_runsFrom bits.length [false] bits

theorem unflag_runsFrom (bits : List Bool) :
    RunsFrom unflagMachine ⟨unflagEntry, Tape.mk₁ (PSTRTMIncrement009.blocks bits)⟩
      (unflagTrace bits) (unflagFinal bits) := by
  have actual := unflag_runs bits
  exact ⟨actual.1, actual.2.1, actual.2.2.1, actual.2.2.2.1⟩

theorem unflag_whole_tape (bits : List Bool) :
    (unflagFinal bits).Tape =
      Tape.mk₂ (false :: (List.replicate bits.length true ++ [false])) bits := rfl

theorem unflag_final_label (bits : List Bool) : (unflagFinal bits).q = unflagHalt := rfl

theorem unflag_output (bits : List Bool) :
    (unflagFinal bits).Tape.right₀ = ListBlank.mk bits := by
  simp [unflag_whole_tape, Tape.mk₂]

/-- Every cell east of the returned finite list is genuinely blank. -/
theorem unflag_east_blank (bits : List Bool) (position : Nat) (beyond : bits.length ≤ position) :
    (unflagFinal bits).Tape.right₀.nth position = false := by
  simpa only [unflag_output, ListBlank.nth_mk, Bool.default_bool] using
    List.getI_eq_default bits beyond

theorem unflag_halt (bits : List Bool) : TM0.step unflagMachine (unflagFinal bits) = none :=
  (unflag_runsFrom bits).2.2.2

/-- The sequence's real write-self transfer is counted in this exact length. -/
theorem unflag_length (bits : List Bool) :
    (unflagTrace bits).length = bits.length^2 + 12*bits.length + 7 := by
  simp only [unflagTrace, List.length_append, List.length_map,
    PSTRTMUnblockTrace019.unblock_length, strip_length]
  omega

/-- One and the same real path supplies all output, time, and prefix-space clauses. -/
theorem actual (bits : List Bool) :
    ∃ trace final,
      RunsFrom unflagMachine ⟨unflagEntry, Tape.mk₁ (PSTRTMIncrement009.blocks bits)⟩ trace final ∧
      final.q = unflagHalt ∧ TM0.step unflagMachine final = none ∧
      final.Tape.right₀ = ListBlank.mk bits ∧
      trace.length ≤ unflagCoefficient*(bits.length+1)^2 ∧
      ∀ inputLen clock,
        visitedSpace unflagMachine inputLen (trace.take clock) ≤
          inputLen + 2*unflagCoefficient*(bits.length+1)^2 + 1 := by
  refine ⟨unflagTrace bits, unflagFinal bits, unflag_runsFrom bits,
    unflag_final_label bits, unflag_halt bits, unflag_output bits, ?_, ?_⟩
  · rw [unflag_length]
    unfold unflagCoefficient
    nlinarith
  · intro inputLen clock
    have space := PSTRTMTrace002.visitedSpace_le unflagMachine inputLen ((unflagTrace bits).take clock)
    have shortPrefix : ((unflagTrace bits).take clock).length ≤ (unflagTrace bits).length :=
      List.length_take_le' _ _
    rw [unflag_length] at shortPrefix
    unfold unflagCoefficient
    nlinarith

/-- All finite code and the common positive coefficient precede ALL bit lists. -/
theorem fixed_unflag :
    ∃ (cap : Nat) (machine : Machine cap) (entry halt : Fin (cap+1)) (c : Nat),
      0 < c ∧ ∀ bits : List Bool,
        ∃ trace final,
          RunsFrom machine ⟨entry, Tape.mk₁ (PSTRTMIncrement009.blocks bits)⟩ trace final ∧
          final.q = halt ∧ TM0.step machine final = none ∧
          final.Tape.right₀ = ListBlank.mk bits ∧
          trace.length ≤ c*(bits.length+1)^2 ∧
          ∀ inputLen clock,
            visitedSpace machine inputLen (trace.take clock) ≤
              inputLen + 2*c*(bits.length+1)^2 + 1 :=
  ⟨21, unflagMachine, unflagEntry, unflagHalt, unflagCoefficient, by decide, actual⟩

end PaperProofs.Common.Native.PSTRWordBool.RawOutput.Unflag
