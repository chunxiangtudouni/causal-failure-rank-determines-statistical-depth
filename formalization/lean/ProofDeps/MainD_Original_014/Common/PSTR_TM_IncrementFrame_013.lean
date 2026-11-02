module
public import Common.PSTR_TM_Increment_009

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMIncrementFrame013
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMTrace002 PSTRTMIncrement009

/-- The real incrementer consumes one spare00 pair exactly on overflow. -/
def remainingPad : List Bool → List Bool
  | [] => []
  | false :: _ => [false, false]
  | true :: later => remainingPad later

/-- A fully explicit trace on a protected operand with arbitrary suffix.
No infinite blank-tail equality is assumed; the TWO own zero cells are real
input cells, and every suffix bit lies beyond them. -/
def frameTrace : Nat → List Bool → List Bool → List (MachineState 14)
  | n, [], suffix =>
    state 0 (zeroLeft n) (false :: false :: suffix) ::
    state 1 (false :: zeroLeft n) (false :: suffix) ::
    state 3 (zeroLeft n) (false :: false :: suffix) ::
    state 6 (zeroLeft n) (true :: false :: suffix) ::
    state 7 (true :: zeroLeft n) (false :: suffix) ::
    state 8 (true :: zeroLeft n) (true :: suffix) :: rewindTrace n (true :: true :: suffix)
  | n, false :: later, suffix =>
    state 0 (zeroLeft n) (false :: true :: (blocks later ++ false :: false :: suffix)) ::
    state 1 (false :: zeroLeft n) (true :: (blocks later ++ false :: false :: suffix)) ::
    state 4 (zeroLeft n) (false :: true :: (blocks later ++ false :: false :: suffix)) ::
      rewindTrace n (true :: true :: (blocks later ++ false :: false :: suffix))
  | n, true :: later, suffix =>
    state 0 (zeroLeft n) (true :: true :: (blocks later ++ false :: false :: suffix)) ::
    state 2 (true :: zeroLeft n) (true :: (blocks later ++ false :: false :: suffix)) ::
    state 5 (zeroLeft n) (true :: true :: (blocks later ++ false :: false :: suffix)) ::
    state 10 (zeroLeft n) (false :: true :: (blocks later ++ false :: false :: suffix)) ::
    state 11 (false :: zeroLeft n) (true :: (blocks later ++ false :: false :: suffix)) ::
      frameTrace (n + 1) later suffix

theorem frameTrace_head (n : Nat) (digits suffix : List Bool) :
    (frameTrace n digits suffix).head? =
      some (state 0 (zeroLeft n) (blocks digits ++ false :: false :: suffix)) := by
  cases digits with
  | nil => rfl
  | cons bit later => cases bit <;> rfl

theorem frameTrace_length_le (n : Nat) (digits suffix : List Bool) :
    (frameTrace n digits suffix).length ≤ 3 * n + 8 * digits.length + 9 := by
  induction digits generalizing n with
  | nil => simp only [frameTrace, List.length_cons, rewindTrace_length, List.length_nil]; omega
  | cons bit later ih =>
    cases bit with
    | false => simp only [frameTrace, List.length_cons, rewindTrace_length]; omega
    | true =>
      have h := ih (n + 1)
      simp only [frameTrace, List.length_cons] at h ⊢
      omega

theorem frameTrace_last (n : Nat) (digits suffix : List Bool) :
    (frameTrace n digits suffix).getLast? = some
      (state 14 [false] (restoreRight n (blocks (bumpDigits digits) ++ remainingPad digits ++ suffix))) := by
  induction digits generalizing n with
  | nil =>
    have hne : rewindTrace n (true :: true :: suffix) ≠ [] := by
      have hlen := rewindTrace_length n (true :: true :: suffix)
      intro h
      simp [h] at hlen
    simp only [frameTrace, List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne, rewindTrace_last]
    rfl
  | cons bit later ih =>
    cases bit with
    | false =>
      have hne : rewindTrace n (true :: true :: (blocks later ++ false :: false :: suffix)) ≠ [] := by
        have hlen := rewindTrace_length n (true :: true :: (blocks later ++ false :: false :: suffix))
        intro h
        simp [h] at hlen
      simp only [frameTrace, List.getLast?_cons_cons]
      rw [List.getLast?_cons_of_ne_nil hne, rewindTrace_last]
      simp [bumpDigits, remainingPad, blocks, List.append_assoc]
    | true =>
      have hne : frameTrace (n + 1) later suffix ≠ [] := by
        have hh := frameTrace_head (n + 1) later suffix
        intro h
        simp [h] at hh
      simp only [frameTrace, List.getLast?_cons_cons]
      rw [List.getLast?_cons_of_ne_nil hne, ih]
      rfl

private theorem prepend (before after : MachineState 14) (tail : List (MachineState 14))
    (hh : tail.head? = some after) (hs : Turing.TM0.step incrementMachine before = some after)
    (hc : tail.IsChain (fun a b => Turing.TM0.step incrementMachine a = some b)) :
    (before :: tail).IsChain (fun a b => Turing.TM0.step incrementMachine a = some b) := by
  apply List.isChain_cons.mpr
  constructor
  · intro next hn
    rw [hh] at hn
    have he := Option.mem_some_iff.mp hn
    subst next
    exact hs
  · exact hc

theorem frameTrace_chain (n : Nat) (digits suffix : List Bool) :
    (frameTrace n digits suffix).IsChain (fun before after =>
      Turing.TM0.step incrementMachine before = some after) := by
  induction digits generalizing n with
  | nil =>
    simp only [frameTrace, List.isChain_cons_cons]
    refine ⟨by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂],
      by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂],
      by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂],
      by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂],
      by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂], ?_⟩
    exact prepend _ _ _ (rewindTrace_head n _)
      (by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂]) (rewindTrace_chain n _)
  | cons bit later ih =>
    cases bit with
    | false =>
      simp only [frameTrace, List.isChain_cons_cons]
      refine ⟨by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂],
        by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂], ?_⟩
      exact prepend _ _ _ (rewindTrace_head n _)
        (by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂]) (rewindTrace_chain n _)
    | true =>
      simp only [frameTrace, List.isChain_cons_cons]
      refine ⟨by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂],
        by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂],
        by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂],
        by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂], ?_⟩
      exact prepend _ _ _ (frameTrace_head (n + 1) later suffix)
        (by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂, zeroLeft]) (ih (n + 1))

theorem increment_frame_runs (digits suffix : List Bool) :
    Runs incrementMachine (blocks digits ++ false :: false :: suffix) (frameTrace 0 digits suffix)
      (state 14 [false] (blocks (bumpDigits digits) ++ remainingPad digits ++ suffix)) := by
  apply runs_of_chain
  · simpa [Turing.TM0.init, Turing.Tape.mk₁, state, zeroLeft] using frameTrace_head 0 digits suffix
  · exact frameTrace_chain 0 digits suffix
  · simpa [restoreRight] using frameTrace_last 0 digits suffix
  · exact increment_halt _ _

theorem increment_frame_computes (digits suffix : List Bool) :
    computes incrementMachine (blocks digits ++ false :: false :: suffix)
      (blocks (bumpDigits digits) ++ remainingPad digits ++ suffix)
      (8 * digits.length + 9) (18 * digits.length + suffix.length + 21) := by
  refine ⟨frameTrace 0 digits suffix,
    state 14 [false] (blocks (bumpDigits digits) ++ remainingPad digits ++ suffix),
    increment_frame_runs digits suffix, ?_, ?_, ?_⟩
  · simp [state, Turing.Tape.mk₂]
  · simpa using frameTrace_length_le 0 digits suffix
  · have hs := visitedSpace_le incrementMachine (blocks digits ++ false :: false :: suffix).length
      (frameTrace 0 digits suffix)
    have ht := frameTrace_length_le 0 digits suffix
    simp only [List.length_append, List.length_cons, blocks_length] at hs ⊢
    omega

/-- The suffix begins at the SAME absolute tape offset after the call,
even when an all-one operand consumes both spare cells. -/
theorem suffix_boundary_preserved (digits : List Bool) :
    (blocks (bumpDigits digits) ++ remainingPad digits).length = (blocks digits).length + 2 := by
  simp only [List.length_append, blocks_length]
  induction digits with
  | nil => rfl
  | cons bit later ih =>
    cases bit with
    | false => simp only [bumpDigits, remainingPad, List.length_cons, List.length_nil]
    | true =>
      simp only [bumpDigits, remainingPad, List.length_cons]
      omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMIncrementFrame013

