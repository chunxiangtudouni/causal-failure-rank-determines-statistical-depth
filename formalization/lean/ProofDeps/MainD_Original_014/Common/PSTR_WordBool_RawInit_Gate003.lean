module

public import Common.PSTR_WordBool_RawInit_Header002

/-! One fixed25-control BoolTM0 reads the original outer count header,
returns to the unchanged whole initial tape, and exposes one of five
actual finite ports:0/1/2/3 or count>=4. No input-dependent code selection
or host count is used by the transition table. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticParse002

def rewindLabel (tag : Fin 5) (remaining : Fin 3) : Fin 25 :=
  ⟨5 + 3 * tag.val + remaining.val, by have ht := tag.isLt; have hr := remaining.isLt; omega⟩

def doneLabel (tag : Fin 5) : Fin 25 := ⟨20 + tag.val, by have ht := tag.isLt; omega⟩

def shortTag (bit : Bool) : Fin 5 := if bit then 1 else 0
def mediumTag (bit : Bool) : Fin 5 := if bit then 3 else 2

def countGateMachine : Machine 24 := fun q bit =>
  match q.val with
  | 0 => some (1, .move .right)
  | 1 => some ((if bit then 2 else 3), .move .right)
  | 2 => if bit then some (rewindLabel 4 1, .move .left) else some (4, .move .right)
  | 3 => some (rewindLabel (shortTag bit) 1, .move .left)
  | 4 => some (rewindLabel (mediumTag bit) 2, .move .left)
  | label =>
    if h : label < 20 then
      let tag : Fin 5 := ⟨(label - 5) / 3, by omega⟩
      let remaining := (label - 5) % 3
      have room : remaining < 3 := Nat.mod_lt _ (by decide)
      if zero : remaining = 0 then some (doneLabel tag, .write bit)
      else some (rewindLabel tag ⟨remaining - 1, by omega⟩, .move .left)
    else none

def gateState (q : Fin 25) (left right : List Bool) : MachineState 24 :=
  ⟨q, Tape.mk₂ left right⟩

def shortGateTrace (bit : Bool) (tail : List Bool) : List (MachineState 24) :=
  [gateState 0 [] (true :: false :: bit :: tail),
   gateState 1 [true] (false :: bit :: tail),
   gateState 3 [false,true] (bit :: tail),
   gateState (rewindLabel (shortTag bit) 1) [true] (false :: bit :: tail),
   gateState (rewindLabel (shortTag bit) 0) [] (true :: false :: bit :: tail),
   gateState (doneLabel (shortTag bit)) [] (true :: false :: bit :: tail)]

def mediumGateTrace (bit : Bool) (tail : List Bool) : List (MachineState 24) :=
  [gateState 0 [] (true :: true :: false :: bit :: tail),
   gateState 1 [true] (true :: false :: bit :: tail),
   gateState 2 [true,true] (false :: bit :: tail),
   gateState 4 [false,true,true] (bit :: tail),
   gateState (rewindLabel (mediumTag bit) 2) [true,true] (false :: bit :: tail),
   gateState (rewindLabel (mediumTag bit) 1) [true] (true :: false :: bit :: tail),
   gateState (rewindLabel (mediumTag bit) 0) [] (true :: true :: false :: bit :: tail),
   gateState (doneLabel (mediumTag bit)) [] (true :: true :: false :: bit :: tail)]

def largeGateTrace (tail : List Bool) : List (MachineState 24) :=
  [gateState 0 [] (true :: true :: true :: tail),
   gateState 1 [true] (true :: true :: tail),
   gateState 2 [true,true] (true :: tail),
   gateState (rewindLabel 4 1) [true] (true :: true :: tail),
   gateState (rewindLabel 4 0) [] (true :: true :: true :: tail),
   gateState (doneLabel 4) [] (true :: true :: true :: tail)]

theorem short_gate_runs (bit : Bool) (tail : List Bool) :
    Runs countGateMachine (true :: false :: bit :: tail) (shortGateTrace bit tail)
      (gateState (doneLabel (shortTag bit)) [] (true :: false :: bit :: tail)) := by
  apply PSTRTMTrace002.runs_of_chain
  · rfl
  · cases bit <;>
      simp [shortGateTrace, List.isChain_cons_cons, gateState, TM0.step,
        countGateMachine, shortTag, rewindLabel, doneLabel, Tape.mk₂]
  · rfl
  · cases bit <;> simp [countGateMachine, shortTag, doneLabel, gateState, TM0.step]

theorem medium_gate_runs (bit : Bool) (tail : List Bool) :
    Runs countGateMachine (true :: true :: false :: bit :: tail) (mediumGateTrace bit tail)
      (gateState (doneLabel (mediumTag bit)) [] (true :: true :: false :: bit :: tail)) := by
  apply PSTRTMTrace002.runs_of_chain
  · rfl
  · cases bit <;>
      simp [mediumGateTrace, List.isChain_cons_cons, gateState, TM0.step,
        countGateMachine, mediumTag, rewindLabel, doneLabel, Tape.mk₂]
  · rfl
  · cases bit <;> simp [countGateMachine, mediumTag, doneLabel, gateState, TM0.step]

theorem large_gate_runs (tail : List Bool) :
    Runs countGateMachine (true :: true :: true :: tail) (largeGateTrace tail)
      (gateState (doneLabel 4) [] (true :: true :: true :: tail)) := by
  apply PSTRTMTrace002.runs_of_chain
  · rfl
  · simp [largeGateTrace, List.isChain_cons_cons, gateState, TM0.step,
      countGateMachine, rewindLabel, doneLabel, Tape.mk₂]
  · rfl
  · simp [countGateMachine, doneLabel, gateState, TM0.step]

def countTag (count : Nat) : Fin 5 :=
  if small : count < 4 then ⟨count, by omega⟩ else 4

private theorem raw_tail_eq (data : List Datum) :
    encode data = encodeNat data.length ++ rawTail data := by
  simp only [encode, rawTail, List.append_assoc]

private theorem finish_gate (data : List Datum)
    (trace : List (MachineState 24)) (final : MachineState 24)
    (actual : Runs countGateMachine (encode data) trace final)
    (port : final.q = doneLabel (countTag data.length))
    (tape : final.Tape = Tape.mk₁ (encode data))
    (time : trace.length ≤ 8) :
    ∃ (trace : List (MachineState 24)) (final : MachineState 24),
      Runs countGateMachine (encode data) trace final ∧
      final.q = doneLabel (countTag data.length) ∧ final.Tape = Tape.mk₁ (encode data) ∧
      trace.length ≤ 8 ∧ ∀ clock,
        visitedSpace countGateMachine (encode data).length (trace.take clock) ≤ (encode data).length + 17 := by
  refine ⟨trace, final, actual, port, tape, time, ?_⟩
  intro clock
  have space := PSTRTMTrace002.visitedSpace_le countGateMachine (encode data).length (trace.take clock)
  have short : (trace.take clock).length ≤ trace.length := by
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  omega

theorem actual_count_gate (data : List Datum) :
    ∃ (trace : List (MachineState 24)) (final : MachineState 24),
      Runs countGateMachine (encode data) trace final ∧
      final.q = doneLabel (countTag data.length) ∧ final.Tape = Tape.mk₁ (encode data) ∧
      trace.length ≤ 8 ∧ ∀ clock,
        visitedSpace countGateMachine (encode data).length (trace.take clock) ≤ (encode data).length + 17 := by
  by_cases small : data.length < 4
  · have casesCount : data.length = 0 ∨ data.length = 1 ∨ data.length = 2 ∨ data.length = 3 := by omega
    rcases casesCount with count | count | count | count
    · have inputEq : encode data = true :: false :: false :: rawTail data := by
        rw [raw_tail_eq, count, show encodeNat 0 = [true,false,false] by decide]
        rfl
      apply finish_gate data (shortGateTrace false (rawTail data))
        (gateState (doneLabel 0) [] (true :: false :: false :: rawTail data))
      · rw [inputEq]
        exact short_gate_runs false _
      · simp only [gateState, count, countTag]
        rfl
      · rw [inputEq]
        rfl
      · simp only [shortGateTrace, List.length_cons, List.length_nil]
        omega
    · have inputEq : encode data = true :: false :: true :: rawTail data := by
        rw [raw_tail_eq, count, show encodeNat 1 = [true,false,true] by decide]
        rfl
      apply finish_gate data (shortGateTrace true (rawTail data))
        (gateState (doneLabel 1) [] (true :: false :: true :: rawTail data))
      · rw [inputEq]
        exact short_gate_runs true _
      · simp only [gateState, count, countTag]
        rfl
      · rw [inputEq]
        rfl
      · simp only [shortGateTrace, List.length_cons, List.length_nil]
        omega
    · have inputEq : encode data = true :: true :: false :: false :: true :: rawTail data := by
        rw [raw_tail_eq, count, show encodeNat 2 = [true,true,false,false,true] by decide]
        rfl
      apply finish_gate data (mediumGateTrace false (true :: rawTail data))
        (gateState (doneLabel 2) [] (true :: true :: false :: false :: true :: rawTail data))
      · rw [inputEq]
        exact medium_gate_runs false _
      · simp only [gateState, count, countTag]
        rfl
      · rw [inputEq]
        rfl
      · simp only [mediumGateTrace, List.length_cons, List.length_nil]
        omega
    · have inputEq : encode data = true :: true :: false :: true :: true :: rawTail data := by
        rw [raw_tail_eq, count, show encodeNat 3 = [true,true,false,true,true] by decide]
        rfl
      apply finish_gate data (mediumGateTrace true (true :: rawTail data))
        (gateState (doneLabel 3) [] (true :: true :: false :: true :: true :: rawTail data))
      · rw [inputEq]
        exact medium_gate_runs true _
      · simp only [gateState, count, countTag]
        rfl
      · rw [inputEq]
        rfl
      · simp only [mediumGateTrace, List.length_cons, List.length_nil]
        omega
  · have room : 4 ≤ data.length := by omega
    have width : 3 ≤ natBits data.length := by
      have monotone : natBits 4 ≤ natBits data.length := by
        simp only [natBits, Nat.log2_eq_log_two]
        exact Nat.add_le_add_right (Nat.log_mono_right room) 1
      simpa only [show natBits 4 = 3 by decide] using monotone
    have rawLength : (PSTRTMNatValue017.rawPayload data.length).length = natBits data.length := by
      simp only [PSTRTMNatValue017.rawPayload, List.length_ofFn]
    have firstThree : List.replicate (natBits data.length) true =
        true :: true :: true :: List.replicate (natBits data.length - 3) true := by
      have widthEq : natBits data.length = 3 + (natBits data.length - 3) := by omega
      conv_lhs => rw [widthEq]
      rw [List.replicate_add]
      rfl
    let tail := List.replicate (natBits data.length - 3) true ++
      false :: (PSTRTMNatValue017.rawPayload data.length ++ rawTail data)
    have inputEq : encode data = true :: true :: true :: tail := by
      rw [raw_tail_eq, encodeNat_rawField]
      simp only [rawField, rawLength, firstThree, List.cons_append, List.append_assoc, tail]
    apply finish_gate data (largeGateTrace tail)
      (gateState (doneLabel 4) [] (true :: true :: true :: tail))
    · rw [inputEq]
      exact large_gate_runs tail
    · simp only [gateState, countTag, dite_eq_right small]
    · rw [inputEq]
      rfl
    · simp only [largeGateTrace, List.length_cons, List.length_nil]
      omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit
