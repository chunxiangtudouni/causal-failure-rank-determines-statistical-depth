module

public import Common.PSTR_SYM_OriginalZeroRun_024

/-! A fixed11-label READ-ONLY test of the first original Natural. A second
TRUE unary-header bit means N>=2. Otherwise the one actual payload bit
distinguishes0/1. Every RIGHT/LEFT is real; both HALT ports return to the
same original N-tag with the entire tape unchanged. No host N-based choice. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicFront

open Turing PSTRTMSeq005

def firstNatTestMachine : Machine 10 := fun label symbol =>
  match label.val with
  | 0 => some (1, .move .right)
  | 1 => some (2, .move .right)
  | 2 => if symbol then some (4, .move .left) else some (3, .move .right)
  | 3 => if symbol then some (6, .move .left) else some (8, .move .left)
  | 4 => some (5, .move .left)
  | 5 => none
  | 6 => some (7, .move .left)
  | 7 => some (5, .move .left)
  | 8 => some (9, .move .left)
  | 9 => some (10, .move .left)
  | _ => none

def state (label : Fin 11) (left right : List Bool) : MachineState 10 := ⟨label, Tape.mk₂ left right⟩

def shortA (bit : Bool) : Fin 11 := if bit then 6 else 8
def shortB (bit : Bool) : Fin 11 := if bit then 7 else 9
def testPort (bit : Bool) : Fin 11 := if bit then 5 else 10

def shortTrace (left : List Bool) (bit : Bool) (suffix : List Bool) : List (MachineState 10) :=
  [state 0 left (false :: true :: false :: bit :: suffix),
    state 1 (false :: left) (true :: false :: bit :: suffix),
    state 2 (true :: false :: left) (false :: bit :: suffix),
    state 3 (false :: true :: false :: left) (bit :: suffix),
    state (shortA bit) (true :: false :: left) (false :: bit :: suffix),
    state (shortB bit) (false :: left) (true :: false :: bit :: suffix),
    state (testPort bit) left (false :: true :: false :: bit :: suffix)]

theorem short_runsFrom (left : List Bool) (bit : Bool) (suffix : List Bool) :
    RunsFrom firstNatTestMachine (state 0 left (false :: true :: false :: bit :: suffix))
      (shortTrace left bit suffix) (state (testPort bit) left (false :: true :: false :: bit :: suffix)) := by
  cases bit <;> refine ⟨rfl, ?_, rfl, ?_⟩ <;>
    simp [shortTrace, List.isChain_cons_cons, TM0.step, firstNatTestMachine,
      state, shortA, shortB, testPort, Tape.mk₂]

def longTrace (left suffix : List Bool) : List (MachineState 10) :=
  [state 0 left (false :: true :: true :: suffix),
    state 1 (false :: left) (true :: true :: suffix),
    state 2 (true :: false :: left) (true :: suffix),
    state 4 (false :: left) (true :: true :: suffix),
    state 5 left (false :: true :: true :: suffix)]

theorem long_runsFrom (left suffix : List Bool) :
    RunsFrom firstNatTestMachine (state 0 left (false :: true :: true :: suffix))
      (longTrace left suffix) (state 5 left (false :: true :: true :: suffix)) := by
  refine ⟨rfl, ?_, rfl, ?_⟩ <;>
    simp [longTrace, List.isChain_cons_cons, TM0.step, firstNatTestMachine, state, Tape.mk₂]

theorem natBits_ge_two (number : Nat) (large : 2 ≤ number) : 2 ≤ natBits number := by
  have nonzero : number ≠ 0 := by omega
  have log : 1 ≤ number.log2 := (Nat.le_log2 nonzero).2 (by simpa using large)
  unfold natBits
  omega

theorem encoded_large_prefix (number : Nat) (large : 2 ≤ number) :
    ∃ tail : List Bool, encodeNat number = true :: true :: tail := by
  have bits := natBits_ge_two number large
  have count : natBits number = 2 + (natBits number - 2) := by omega
  refine ⟨List.replicate (natBits number - 2) true ++ false :: PSTRTMNatValue017.rawPayload number, ?_⟩
  rw [PA17TMRatArithmeticParse002.encodeNat_rawField]
  simp only [PA17TMRatArithmeticParse002.rawField, PSTRSymbolicLocator.rawPayload_length]
  rw [count, List.replicate_add]
  simp [List.replicate_succ]

/-- Only the real original raw field is assumed. The SAME fixed code
returns zero-port10 or positive-port5 at exactly the same physical tape. -/
theorem firstNat_runsFrom (left : List Bool) (number : Nat) (suffix : List Bool) :
    ∃ trace : List (MachineState 10),
      RunsFrom firstNatTestMachine (state 0 left (encodeDatum (.natural number) ++ suffix)) trace
        (state (if number = 0 then 10 else 5) left (encodeDatum (.natural number) ++ suffix)) ∧
      trace.length ≤ 7 ∧
      ∀ inputLength, visitedSpace firstNatTestMachine inputLength trace ≤ inputLength + 15 := by
  by_cases zero : number = 0
  · subst number
    have bits : encodeDatum (.natural 0) = [false,true,false,false] := by decide
    refine ⟨shortTrace left false suffix, ?_, Nat.le_refl 7, ?_⟩
    · simpa [bits, testPort] using short_runsFrom left false suffix
    · intro inputLength
      have bound := PSTRTMTrace002.visitedSpace_le firstNatTestMachine inputLength (shortTrace left false suffix)
      simpa only [shortTrace, List.length_cons, List.length_nil] using bound
  · by_cases one : number = 1
    · subst number
      have bits : encodeDatum (.natural 1) = [false,true,false,true] := by decide
      refine ⟨shortTrace left true suffix, ?_, Nat.le_refl 7, ?_⟩
      · simpa [bits, testPort] using short_runsFrom left true suffix
      · intro inputLength
        have bound := PSTRTMTrace002.visitedSpace_le firstNatTestMachine inputLength (shortTrace left true suffix)
        simpa only [shortTrace, List.length_cons, List.length_nil] using bound
    · obtain ⟨tail, bits⟩ := encoded_large_prefix number (by omega)
      refine ⟨longTrace left (tail ++ suffix), ?_, (by decide : 5 ≤ 7), ?_⟩
      · simpa only [encodeDatum, bits, List.cons_append, zero, ite_false] using long_runsFrom left (tail ++ suffix)
      · intro inputLength
        have bound := PSTRTMTrace002.visitedSpace_le firstNatTestMachine inputLength (longTrace left (tail ++ suffix))
        have length : (longTrace left (tail ++ suffix)).length = 5 := rfl
        rw [length] at bound
        omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicFront
