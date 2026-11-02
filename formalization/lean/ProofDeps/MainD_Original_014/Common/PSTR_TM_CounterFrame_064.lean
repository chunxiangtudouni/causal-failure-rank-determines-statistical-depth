module
public import Common.PSTR_TM_Canonical_020

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCounterFrame064
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMIncrement009

/-- The B1 loop's binary counter is to the right of an ACTUAL false guard.
The archive past that guard contains its marker and retained A/B columns.
No left-blank assumption and no arbitrary right-suffix promise are used. -/
def counterLeft (count : Nat) (archive : List Bool) : List Bool := zeroLeft count ++ false :: archive

def rewindTrace (archive : List Bool) : Nat → List Bool → List (MachineState 14)
  | 0, tail => [state 9 (false :: archive) tail, state 12 archive (false :: tail), state 14 (false :: archive) tail]
  | count + 1, tail =>
    state 9 (counterLeft (count + 1) archive) tail ::
    state 12 (false :: counterLeft count archive) (true :: tail) ::
    state 13 (counterLeft count archive) (false :: true :: tail) ::
      rewindTrace archive count (false :: true :: tail)

theorem rewind_head (archive : List Bool) (count : Nat) (tail : List Bool) :
    (rewindTrace archive count tail).head? = some (state 9 (counterLeft count archive) tail) := by
  cases count <;> rfl

theorem rewind_length (archive : List Bool) (count : Nat) (tail : List Bool) :
    (rewindTrace archive count tail).length = 3 * count + 3 := by
  induction count generalizing tail with
  | zero => rfl
  | succ count ih => simp only [rewindTrace, List.length_cons, ih]; omega

theorem rewind_last (archive : List Bool) (count : Nat) (tail : List Bool) :
    (rewindTrace archive count tail).getLast? = some (state 14 (false :: archive) (restoreRight count tail)) := by
  induction count generalizing tail with
  | zero => rfl
  | succ count ih =>
    have hne : rewindTrace archive count (false :: true :: tail) ≠ [] := by
      intro h
      have hl := rewind_length archive count (false :: true :: tail)
      simp [h] at hl
    simp only [rewindTrace, List.getLast?_cons_cons]
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

theorem rewind_chain (archive : List Bool) (count : Nat) (tail : List Bool) :
    (rewindTrace archive count tail).IsChain (fun a b => Turing.TM0.step incrementMachine a = some b) := by
  induction count generalizing tail with
  | zero => simp [rewindTrace, List.isChain_cons_cons, Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂]
  | succ count ih =>
    simp only [rewindTrace, List.isChain_cons_cons]
    refine ⟨by simp [Turing.TM0.step, incrementMachine, state, counterLeft, zeroLeft, Turing.Tape.mk₂],
      by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂], ?_⟩
    exact prepend _ _ _ (rewind_head archive count (false :: true :: tail))
      (by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂]) (ih _)

def counterTrace (archive : List Bool) : Nat → List Bool → List (MachineState 14)
  | count, [] =>
    state 0 (counterLeft count archive) [] :: state 1 (false :: counterLeft count archive) [] ::
    state 3 (counterLeft count archive) [false] :: state 6 (counterLeft count archive) [true] ::
    state 7 (true :: counterLeft count archive) [] :: state 8 (true :: counterLeft count archive) [true] ::
      rewindTrace archive count [true,true]
  | count, false :: later =>
    state 0 (counterLeft count archive) (false :: true :: blocks later) ::
    state 1 (false :: counterLeft count archive) (true :: blocks later) ::
    state 4 (counterLeft count archive) (false :: true :: blocks later) ::
      rewindTrace archive count (true :: true :: blocks later)
  | count, true :: later =>
    state 0 (counterLeft count archive) (true :: true :: blocks later) ::
    state 2 (true :: counterLeft count archive) (true :: blocks later) ::
    state 5 (counterLeft count archive) (true :: true :: blocks later) ::
    state 10 (counterLeft count archive) (false :: true :: blocks later) ::
    state 11 (false :: counterLeft count archive) (true :: blocks later) ::
      counterTrace archive (count + 1) later

theorem counter_head (archive : List Bool) (count : Nat) (digits : List Bool) :
    (counterTrace archive count digits).head? = some (state 0 (counterLeft count archive) (blocks digits)) := by
  cases digits with
  | nil => rfl
  | cons bit later => cases bit <;> rfl

theorem counter_length_le (archive : List Bool) (count : Nat) (digits : List Bool) :
    (counterTrace archive count digits).length ≤ 3 * count + 8 * digits.length + 9 := by
  induction digits generalizing count with
  | nil => simp only [counterTrace, List.length_cons, rewind_length, List.length_nil]; omega
  | cons bit later ih =>
    cases bit with
    | false => simp only [counterTrace, List.length_cons, rewind_length]; omega
    | true =>
      have h := ih (count + 1)
      simp only [counterTrace, List.length_cons] at h ⊢
      omega

theorem counter_last (archive : List Bool) (count : Nat) (digits : List Bool) :
    (counterTrace archive count digits).getLast? = some
      (state 14 (false :: archive) (restoreRight count (blocks (bumpDigits digits)))) := by
  induction digits generalizing count with
  | nil =>
    have hne : rewindTrace archive count [true,true] ≠ [] := by
      intro h
      have hl := rewind_length archive count [true,true]
      simp [h] at hl
    simp only [counterTrace, List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne, rewind_last]
    rfl
  | cons bit later ih =>
    cases bit with
    | false =>
      have hne : rewindTrace archive count (true :: true :: blocks later) ≠ [] := by
        intro h
        have hl := rewind_length archive count (true :: true :: blocks later)
        simp [h] at hl
      simp only [counterTrace, List.getLast?_cons_cons]
      rw [List.getLast?_cons_of_ne_nil hne, rewind_last]
      rfl
    | true =>
      have hne : counterTrace archive (count + 1) later ≠ [] := by
        intro h
        have hh := counter_head archive (count + 1) later
        simp [h] at hh
      simp only [counterTrace, List.getLast?_cons_cons]
      rw [List.getLast?_cons_of_ne_nil hne, ih]
      rfl

theorem counter_chain (archive : List Bool) (count : Nat) (digits : List Bool) :
    (counterTrace archive count digits).IsChain (fun a b => Turing.TM0.step incrementMachine a = some b) := by
  induction digits generalizing count with
  | nil =>
    simp only [counterTrace, List.isChain_cons_cons]
    refine ⟨by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂],
      by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂],
      by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂],
      by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂],
      by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂], ?_⟩
    exact prepend _ _ _ (rewind_head archive count [true,true])
      (by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂]) (rewind_chain archive count [true,true])
  | cons bit later ih =>
    cases bit with
    | false =>
      simp only [counterTrace, List.isChain_cons_cons]
      refine ⟨by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂],
        by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂], ?_⟩
      exact prepend _ _ _ (rewind_head archive count (true :: true :: blocks later))
        (by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂]) (rewind_chain archive count _)
    | true =>
      simp only [counterTrace, List.isChain_cons_cons]
      refine ⟨by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂],
        by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂],
        by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂],
        by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂], ?_⟩
      exact prepend _ _ _ (counter_head archive (count + 1) later)
        (by simp [Turing.TM0.step, incrementMachine, state, counterLeft, zeroLeft, Turing.Tape.mk₂]) (ih (count + 1))

/-- A genuine retained-tape run of the EXISTING15-label incrementer.
The actual guard cell is visited; every archive cell past it is retained. -/
theorem counter_runsFrom (archive : List Bool) (digits : List Bool) :
    PSTRTMSeq005.RunsFrom incrementMachine (state 0 (false :: archive) (blocks digits))
      (counterTrace archive 0 digits) (state 14 (false :: archive) (blocks (bumpDigits digits))) := by
  refine ⟨?_, counter_chain archive 0 digits, ?_, increment_halt _ _⟩
  · simpa only [counterLeft, zeroLeft, List.nil_append] using counter_head archive 0 digits
  · simpa only [restoreRight] using counter_last archive 0 digits

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCounterFrame064
