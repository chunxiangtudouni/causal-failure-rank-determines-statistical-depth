module
public import PaperProofs.Common.PSTR_TM_Seq_005
public import Mathlib.Data.Nat.Bits

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMIncrement009
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMTrace002

/-- A concrete finite alphabet needed by unsigned arithmetic: blank 00,
zero digit 01, one digit 11. The true flag distinguishes numeric zero from
blank. This is an internal block representation, not the original raw input. -/
def blocks (digits : List Bool) : List Bool := digits.flatMap (fun bit => [bit, true])

def valueDigits : List Bool → Nat
  | [] => 0
  | digit :: later => Nat.bit digit (valueDigits later)

def bumpDigits : List Bool → List Bool
  | [] => [true]
  | false :: later => true :: later
  | true :: later => false :: bumpDigits later

theorem valueDigits_bumpDigits (digits : List Bool) :
    valueDigits (bumpDigits digits) = valueDigits digits + 1 := by
  induction digits with
  | nil => rfl
  | cons bit later ih =>
    cases bit with
    | false => simp [bumpDigits, valueDigits, Nat.bit]
    | true =>
      simp [bumpDigits, valueDigits, Nat.bit, ih]
      omega

/-- Fixed ordinary Bool TM implementing binary carry then rewind.
Its fifteen labels contain no input-dependent arithmetic or cost certificate.
State 13 writes its current bit to return to the rewind loop without moving. -/
def incrementMachine : Machine 14 := fun q symbol =>
  match q.val with
  | 0 => some (if symbol then 2 else 1, .move .right)
  | 1 => some (if symbol then 4 else 3, .move .left)
  | 2 => if symbol then some (5, .move .left) else none
  | 3 => some (6, .write true)
  | 4 => some (9, .write true)
  | 5 => some (10, .write false)
  | 6 => some (7, .move .right)
  | 7 => some (8, .write true)
  | 8 => some (9, .move .left)
  | 9 => some (12, .move .left)
  | 10 => some (11, .move .right)
  | 11 => some (0, .move .right)
  | 12 => some (if symbol then 13 else 14, if symbol then .move .left else .move .right)
  | 13 => some (9, .write symbol)
  | _ => none

def state (q : Fin 15) (left right : List Bool) : MachineState 14 :=
  ⟨q, Turing.Tape.mk₂ left right⟩

def zeroLeft : Nat → List Bool
  | 0 => []
  | n + 1 => true :: false :: zeroLeft n

def restoreRight : Nat → List Bool → List Bool
  | 0, tail => tail
  | n + 1, tail => restoreRight n (false :: true :: tail)

/-- The real rewind trace, including the final halt configuration. -/
def rewindTrace : Nat → List Bool → List (MachineState 14)
  | 0, tail => [state 9 [] tail, state 12 [] (false :: tail), state 14 [false] tail]
  | n + 1, tail =>
    state 9 (zeroLeft (n + 1)) tail ::
    state 12 (false :: zeroLeft n) (true :: tail) ::
    state 13 (zeroLeft n) (false :: true :: tail) ::
      rewindTrace n (false :: true :: tail)

theorem rewindTrace_head (n : Nat) (tail : List Bool) :
    (rewindTrace n tail).head? = some (state 9 (zeroLeft n) tail) := by
  cases n <;> rfl

theorem rewindTrace_length (n : Nat) (tail : List Bool) :
    (rewindTrace n tail).length = 3 * n + 3 := by
  induction n generalizing tail with
  | zero => rfl
  | succ n ih => simp only [rewindTrace, List.length_cons, ih]; omega

theorem rewindTrace_chain (n : Nat) (tail : List Bool) :
    (rewindTrace n tail).IsChain (fun before after =>
      Turing.TM0.step incrementMachine before = some after) := by
  induction n generalizing tail with
  | zero =>
    simp only [rewindTrace, List.isChain_cons_cons, List.isChain_singleton, and_true]
    constructor <;>
      simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂]
  | succ n ih =>
    simp only [rewindTrace, List.isChain_cons_cons]
    constructor
    · simp [Turing.TM0.step, incrementMachine, state, zeroLeft, Turing.Tape.mk₂]
    constructor
    · simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂]
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      simp only [rewindTrace_head, Option.mem_some_iff] at ha
      subst after
      simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂]
    · exact ih _

theorem restoreRight_eq (n : Nat) (tail : List Bool) :
    restoreRight n tail = blocks (List.replicate n false) ++ tail := by
  induction n generalizing tail with
  | zero => rfl
  | succ n ih =>
    rw [restoreRight, ih]
    simp [blocks, List.replicate_succ', List.flatMap_append, List.append_assoc]

theorem rewindTrace_last (n : Nat) (tail : List Bool) :
    (rewindTrace n tail).getLast? = some (state 14 [false] (restoreRight n tail)) := by
  induction n generalizing tail with
  | zero => rfl
  | succ n ih =>
    have hne : rewindTrace n (false :: true :: tail) ≠ [] := by
      have hlen := rewindTrace_length n (false :: true :: tail)
      intro h
      simp [h] at hlen
    simp only [rewindTrace, List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne, ih]
    rfl

theorem increment_halt (left right : List Bool) :
    Turing.TM0.step incrementMachine (state 14 left right) = none := by
  simp [Turing.TM0.step, incrementMachine, state]

/-- The complete real rewind phase of this concrete binary arithmetic
machine, preserving every remaining digit block and ending at the first
input cell. Carry and raw-codec expansion are separate obligations. -/
theorem rewind_runsFrom (n : Nat) (tail : List Bool) :
    PSTRTMSeq005.RunsFrom incrementMachine (state 9 (zeroLeft n) tail)
      (rewindTrace n tail) (state 14 [false] (blocks (List.replicate n false) ++ tail)) := by
  refine ⟨rewindTrace_head n tail, rewindTrace_chain n tail, ?_, increment_halt _ _⟩
  simpa [restoreRight_eq] using rewindTrace_last n tail

/-- Explicit complete trace for binary increment; every carried one costs
five real configurations before the recursive continuation. The full chain
and genuine final halt are proved below. -/
def computeTrace : Nat → List Bool → List (MachineState 14)
  | n, [] =>
    state 0 (zeroLeft n) [] ::
    state 1 (false :: zeroLeft n) [] ::
    state 3 (zeroLeft n) [false] ::
    state 6 (zeroLeft n) [true] ::
    state 7 (true :: zeroLeft n) [] ::
    state 8 (true :: zeroLeft n) [true] ::
      rewindTrace n [true, true]
  | n, false :: later =>
    state 0 (zeroLeft n) (false :: true :: blocks later) ::
    state 1 (false :: zeroLeft n) (true :: blocks later) ::
    state 4 (zeroLeft n) (false :: true :: blocks later) ::
      rewindTrace n (true :: true :: blocks later)
  | n, true :: later =>
    state 0 (zeroLeft n) (true :: true :: blocks later) ::
    state 2 (true :: zeroLeft n) (true :: blocks later) ::
    state 5 (zeroLeft n) (true :: true :: blocks later) ::
    state 10 (zeroLeft n) (false :: true :: blocks later) ::
    state 11 (false :: zeroLeft n) (true :: blocks later) ::
      computeTrace (n + 1) later

theorem computeTrace_head (n : Nat) (digits : List Bool) :
    (computeTrace n digits).head? = some (state 0 (zeroLeft n) (blocks digits)) := by
  cases digits with
  | nil => rfl
  | cons bit digits => cases bit <;> rfl

theorem computeTrace_length_le (n : Nat) (digits : List Bool) :
    (computeTrace n digits).length ≤ 3 * n + 8 * digits.length + 9 := by
  induction digits generalizing n with
  | nil => simp only [computeTrace, List.length_cons, rewindTrace_length, List.length_nil]; omega
  | cons bit digits ih =>
    cases bit with
    | false =>
      simp only [computeTrace, List.length_cons, rewindTrace_length]
      omega
    | true =>
      have h := ih (n + 1)
      simp only [computeTrace, List.length_cons] at h ⊢
      omega

theorem computeTrace_last (n : Nat) (digits : List Bool) :
    (computeTrace n digits).getLast? =
      some (state 14 [false] (restoreRight n (blocks (bumpDigits digits)))) := by
  induction digits generalizing n with
  | nil =>
    simp only [computeTrace, List.getLast?_cons_cons, bumpDigits, blocks, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    have hne : rewindTrace n [true, true] ≠ [] := by
      have hlen := rewindTrace_length n [true, true]
      intro h
      simp [h] at hlen
    exact (List.getLast?_cons_of_ne_nil hne).trans (rewindTrace_last n [true, true])
  | cons bit digits ih =>
    cases bit with
    | false =>
      simp only [computeTrace, List.getLast?_cons_cons, bumpDigits, blocks, List.flatMap_cons,
        List.cons_append, List.nil_append]
      have hne : rewindTrace n (true :: true :: blocks digits) ≠ [] := by
        have hlen := rewindTrace_length n (true :: true :: blocks digits)
        intro h
        simp [h] at hlen
      exact (List.getLast?_cons_of_ne_nil hne).trans (rewindTrace_last n _)
    | true =>
      have hne : computeTrace (n + 1) digits ≠ [] := by
        have hh := computeTrace_head (n + 1) digits
        intro h
        simp [h] at hh
      simp only [computeTrace, List.getLast?_cons_cons]
      rw [List.getLast?_cons_of_ne_nil hne, ih]
      rfl

private theorem chain_prepend (before after : MachineState 14) (tail : List (MachineState 14))
    (hh : tail.head? = some after)
    (hs : Turing.TM0.step incrementMachine before = some after)
    (hc : tail.IsChain (fun a b => Turing.TM0.step incrementMachine a = some b)) :
    (before :: tail).IsChain (fun a b => Turing.TM0.step incrementMachine a = some b) := by
  apply List.isChain_cons.mpr
  constructor
  · intro next hnext
    rw [hh] at hnext
    have he := Option.mem_some_iff.mp hnext
    subst next
    exact hs
  · exact hc

/-- Every consecutive configuration is a real transition of the fixed
fifteen-label Bool TM, including carry, extension, rewind, and final halt. -/
theorem computeTrace_chain (n : Nat) (digits : List Bool) :
    (computeTrace n digits).IsChain (fun before after =>
      Turing.TM0.step incrementMachine before = some after) := by
  induction digits generalizing n with
  | nil =>
    simp only [computeTrace, List.isChain_cons_cons]
    refine ⟨by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂],
      by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂],
      by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂],
      by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂],
      by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂], ?_⟩
    exact chain_prepend _ _ _ (rewindTrace_head n _)
      (by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂]) (rewindTrace_chain n _)
  | cons bit digits ih =>
    cases bit with
    | false =>
      simp only [computeTrace, List.isChain_cons_cons]
      refine ⟨by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂],
        by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂], ?_⟩
      exact chain_prepend _ _ _ (rewindTrace_head n _)
        (by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂]) (rewindTrace_chain n _)
    | true =>
      simp only [computeTrace, List.isChain_cons_cons]
      refine ⟨by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂],
        by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂],
        by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂],
        by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂], ?_⟩
      exact chain_prepend _ _ _ (computeTrace_head (n + 1) digits)
        (by simp [Turing.TM0.step, incrementMachine, state, Turing.Tape.mk₂, zeroLeft]) (ih (n + 1))

theorem increment_runs (digits : List Bool) :
    Runs incrementMachine (blocks digits) (computeTrace 0 digits)
      (state 14 [false] (blocks (bumpDigits digits))) := by
  apply runs_of_chain
  · simpa [Turing.TM0.init, Turing.Tape.mk₁, state, zeroLeft] using computeTrace_head 0 digits
  · exact computeTrace_chain 0 digits
  · simpa [restoreRight] using computeTrace_last 0 digits
  · exact increment_halt _ _

theorem blocks_length (digits : List Bool) : (blocks digits).length = 2 * digits.length := by
  induction digits with
  | nil => rfl
  | cons bit digits ih =>
    simp only [blocks, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil]
    change 2 + (blocks digits).length = 2 * (digits.length + 1)
    rw [ih]
    omega

/-- First concrete arithmetic primitive: a fixed ordinary Bool TM returns
unsigned binary value+1, with actual linear time and visited-bit space.
The block representation and its missing RAW-input transport are explicit. -/
theorem increment_computes (digits : List Bool) :
    computes incrementMachine (blocks digits) (blocks (bumpDigits digits))
      (8 * digits.length + 9) (18 * digits.length + 19) := by
  refine ⟨computeTrace 0 digits, state 14 [false] (blocks (bumpDigits digits)),
    increment_runs digits, ?_, ?_, ?_⟩
  · simp [state, Turing.Tape.mk₂]
  · simpa using computeTrace_length_le 0 digits
  · have hspace := visitedSpace_le incrementMachine (blocks digits).length (computeTrace 0 digits)
    have htime := computeTrace_length_le 0 digits
    rw [blocks_length] at hspace ⊢
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMIncrement009






