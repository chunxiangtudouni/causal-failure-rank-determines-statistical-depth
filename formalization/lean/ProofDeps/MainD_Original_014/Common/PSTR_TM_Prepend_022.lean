module
public import Common.PSTR_TM_NativeIncrement_021

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPrepend022
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMTrace002 PSTRTMSeq005

/-- A literal bit belongs to fixed finite program code. Each call really
moves one cell left, writes that bit, then halts. -/
def bitMachine (bit : Bool) : Machine 2 := fun q _ =>
  match q.val with
  | 0 => some (1, .move .left)
  | 1 => some (2, .write bit)
  | _ => none

def bitState (q : Fin 3) (right : List Bool) : MachineState 2 :=
  ⟨q, Turing.Tape.mk₂ [] right⟩

def bitTrace (bit : Bool) (input : List Bool) : List (MachineState 2) :=
  [bitState 0 input, bitState 1 (false :: input), bitState 2 (bit :: input)]

theorem bit_runs (bit : Bool) (input : List Bool) :
    Runs (bitMachine bit) input (bitTrace bit input) (bitState 2 (bit :: input)) := by
  apply runs_of_chain
  · rfl
  · simp [bitTrace, List.isChain_cons_cons, bitState, Turing.TM0.step, bitMachine, Turing.Tape.mk₂]
  · rfl
  · simp [bitState, Turing.TM0.step, bitMachine]

def prefixStates : List Bool → Nat
  | [] => 0
  | _ :: later => prefixStates later + 3

/-- Compile a FIXED literal fragment by reusing the real sequence compiler.
The original input is arbitrary Bool data and is never used as code. -/
def prefixMachine : (fragment : List Bool) → Machine (prefixStates fragment)
  | [] => fun _ _ => none
  | bit :: later => seqMachine (prefixMachine later) (bitMachine bit)

def prefixTrace : (fragment : List Bool) → List Bool → List (MachineState (prefixStates fragment))
  | [], input => [⟨0, Turing.Tape.mk₁ input⟩]
  | bit :: later, input =>
    (prefixTrace later input).map (leftCfg (b := 2)) ++
      (bitTrace bit (later ++ input)).map (rightCfg (a := prefixStates later))

def prefixFinal : (fragment : List Bool) → List Bool → MachineState (prefixStates fragment)
  | [], input => ⟨0, Turing.Tape.mk₁ input⟩
  | bit :: later, input => rightCfg (a := prefixStates later) (bitState 2 (bit :: (later ++ input)))

theorem prefixStates_length (fragment : List Bool) : prefixStates fragment = 3 * fragment.length := by
  induction fragment with
  | nil => rfl
  | cons bit later ih => simp only [prefixStates, ih, List.length_cons]; omega

theorem prefix_final_tape (fragment input : List Bool) :
    (prefixFinal fragment input).Tape = Turing.Tape.mk₁ (fragment ++ input) := by
  cases fragment with
  | nil => rfl
  | cons bit later => rfl

theorem prefix_length (fragment input : List Bool) :
    (prefixTrace fragment input).length = 3 * fragment.length + 1 := by
  induction fragment with
  | nil => rfl
  | cons bit later ih =>
    change ((prefixTrace later input).map (leftCfg (b := 2)) ++
      (bitTrace bit (later ++ input)).map (rightCfg (a := prefixStates later))).length =
        3 * (bit :: later).length + 1
    rw [List.length_append, List.length_map, List.length_map, ih]
    simp only [bitTrace, List.length_cons, List.length_nil]
    omega

theorem prefix_runs (fragment input : List Bool) :
    Runs (prefixMachine fragment) input (prefixTrace fragment input) (prefixFinal fragment input) := by
  induction fragment with
  | nil =>
    apply runs_of_chain
    · rfl
    · exact .singleton _
    · rfl
    · rfl
  | cons bit later ih =>
    apply seq_runs (prefixMachine later) (bitMachine bit) input
      (prefixFinal later input) (bitState 2 (bit :: (later ++ input)))
      (prefixTrace later input) (bitTrace bit (later ++ input))
    · exact ih
    · have h := bit_runs bit (later ++ input)
      refine ⟨?_, h.2.1, h.2.2.1, h.2.2.2.1⟩
      rw [prefix_final_tape]
      exact h.1

/-- Neutral, directly consumable Bool codec fragment. The trace length is
exact; space is ORIGINAL visitedSpace from its actual finite moves. -/
theorem prefix_computes (fragment input : List Bool) :
    computes (prefixMachine fragment) input (fragment ++ input)
      (3 * fragment.length + 1) (input.length + 6 * fragment.length + 3) := by
  refine ⟨prefixTrace fragment input, prefixFinal fragment input, prefix_runs fragment input, ?_, ?_, ?_⟩
  · rw [prefix_final_tape]
    simp [Turing.Tape.mk₁, Turing.Tape.mk₂]
  · exact (prefix_length fragment input).le
  · have hs := visitedSpace_le (prefixMachine fragment) input.length (prefixTrace fragment input)
    rw [prefix_length] at hs
    omega

/-- The actual original natural Datum tag, one fixed4-label Bool machine. -/
def naturalTagMachine : Machine 3 := prefixMachine [false]

theorem naturalTag_computes (value : Nat) :
    computes naturalTagMachine (encodeNat value) (encodeDatum (.natural value))
      4 ((encodeNat value).length + 9) := by
  simpa [naturalTagMachine, encodeDatum, prefixStates, Nat.add_assoc] using
    prefix_computes [false] (encodeNat value)

/-- ONE fixed4-label machine. The original public sign bit is DATA on the
input tape, not an externally computed sign or a machine-selection oracle. -/
def rationalTagMachine : Machine 3 := prefixMachine [true]

theorem rationalTag_computes (value : Rat) :
    computes rationalTagMachine
      (decide (value < 0) :: (encodeNat value.num.natAbs ++ encodeNat value.den))
      (encodeDatum (.rational value)) 4
      ((decide (value < 0) :: (encodeNat value.num.natAbs ++ encodeNat value.den)).length + 9) := by
  simpa [rationalTagMachine, encodeDatum, prefixStates, Nat.add_assoc] using
    prefix_computes [true] (decide (value < 0) :: (encodeNat value.num.natAbs ++ encodeNat value.den))

/-- A STATIC list arity is compiled before numeric operands. This supports
fixed-arity output formats; it is not a uniform dynamic-length list encoder. -/
def listFrameMachine (count : Nat) : Machine (prefixStates (encodeNat count)) :=
  prefixMachine (encodeNat count)

theorem listFrame_computes (count : Nat) (data : List Datum) (arity : data.length = count) :
    computes (listFrameMachine count) (data.flatMap encodeDatum ++ [true]) (encode data)
      (3 * (encodeNat count).length + 1)
      ((data.flatMap encodeDatum ++ [true]).length + 6 * (encodeNat count).length + 3) := by
  simpa only [listFrameMachine, encode, arity, List.append_assoc] using
    prefix_computes (encodeNat count) (data.flatMap encodeDatum ++ [true])

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPrepend022
