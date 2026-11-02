module
public import PaperProofs.Common.PSTR_TM_DoubleCode_061

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMDoubleTrace062
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMDoubleCode061

def prependTrace (input : List Bool) : List (MachineState 13) :=
  [state 6 [] (false :: input), state 7 [] (true :: input),
    state 9 [] (false :: true :: input), state 10 [] (false :: true :: input)]

def zeroTrace : List (MachineState 13) :=
  [state 0 [] [false,true], state 1 [false] [true], state 2 [true,false] [],
    state 4 [false,true,false] [], state 11 [true,false] [false],
    state 12 [false] [true,false], state 13 [] [false,true,false],
    state 10 [] [false,true,false]]

def doubleTrace : List Bool → List (MachineState 13)
  | [] => []
  | [false] => zeroTrace
  | true :: later => [state 0 [] (PSTRTMIncrement009.blocks (true :: later))] ++ prependTrace (PSTRTMIncrement009.blocks (true :: later))
  | false :: true :: later =>
    [state 0 [] (PSTRTMIncrement009.blocks (false :: true :: later)), state 1 [false] (true :: PSTRTMIncrement009.blocks (true :: later)),
      state 2 [true,false] (PSTRTMIncrement009.blocks (true :: later)), state 3 [false] (true :: PSTRTMIncrement009.blocks (true :: later)),
      state 5 [] (PSTRTMIncrement009.blocks (false :: true :: later))] ++ prependTrace (PSTRTMIncrement009.blocks (false :: true :: later))
  | false :: false :: later =>
    [state 0 [] (PSTRTMIncrement009.blocks (false :: false :: later)), state 1 [false] (true :: PSTRTMIncrement009.blocks (false :: later)),
      state 2 [true,false] (PSTRTMIncrement009.blocks (false :: later)), state 4 [false,true,false] (true :: PSTRTMIncrement009.blocks later),
      state 8 [true,false] (PSTRTMIncrement009.blocks (false :: later)), state 3 [false] (true :: PSTRTMIncrement009.blocks (false :: later)),
      state 5 [] (PSTRTMIncrement009.blocks (false :: false :: later))] ++ prependTrace (PSTRTMIncrement009.blocks (false :: false :: later))

theorem double_head (digits : List Bool) (hn : digits ≠ []) :
    (doubleTrace digits).head? = some (state 0 [] (PSTRTMIncrement009.blocks digits)) := by
  cases digits with
  | nil => contradiction
  | cons bit later =>
    cases bit <;> cases later with
    | nil => rfl
    | cons next rest => cases next <;> rfl

theorem double_last (digits : List Bool) (hn : digits ≠ []) :
    (doubleTrace digits).getLast? = some (state 10 [] (PSTRTMIncrement009.blocks (doubleDigits digits))) := by
  cases digits with
  | nil => contradiction
  | cons bit later =>
    cases bit with
    | false =>
      cases later with
      | nil =>
        change some (state 10 [] [false,true,false]) = some (state 10 [] [false,true])
        have hb : Turing.ListBlank.mk [false,true,false] = Turing.ListBlank.mk [false,true] :=
          PSTRTMRawNat010.blank_append_false [false,true]
        simp only [state, Turing.Tape.mk₂]
        rw [hb]
      | cons next rest => cases next <;> simp [doubleTrace, prependTrace, doubleDigits, PSTRTMIncrement009.blocks]
    | true => simp [doubleTrace, prependTrace, doubleDigits, PSTRTMIncrement009.blocks]

theorem double_length_le (digits : List Bool) : (doubleTrace digits).length ≤ 11 := by
  cases digits with
  | nil => decide
  | cons bit later =>
    cases bit <;> cases later with
    | nil => decide
    | cons next rest => cases next <;> simp [doubleTrace, prependTrace]

theorem double_chain (digits : List Bool) :
    (doubleTrace digits).IsChain (fun before after => Turing.TM0.step doubleMachine before = some after) := by
  cases digits with
  | nil => exact .nil
  | cons bit later =>
    cases bit <;> cases later with
    | nil => simp [doubleTrace, zeroTrace, prependTrace, List.isChain_cons_cons, Turing.TM0.step,
        doubleMachine, state, PSTRTMIncrement009.blocks, Turing.Tape.mk₂]
    | cons next rest => cases next <;> simp [doubleTrace, prependTrace, List.isChain_cons_cons,
        Turing.TM0.step, doubleMachine, state, PSTRTMIncrement009.blocks, Turing.Tape.mk₂]

/-- Actual zero detection and physical low-digit allocation, including
the rewinds. No branch takes an externally supplied zero/positive test. -/
theorem double_runs (digits : List Bool) (hn : digits ≠ []) :
    Runs doubleMachine (PSTRTMIncrement009.blocks digits) (doubleTrace digits) (state 10 [] (PSTRTMIncrement009.blocks (doubleDigits digits))) := by
  apply PSTRTMTrace002.runs_of_chain
  · simpa [Turing.TM0.init, state, Turing.Tape.mk₁] using double_head digits hn
  · exact double_chain digits
  · exact double_last digits hn
  · exact double_halt _ _

theorem double_final_tape (digits : List Bool) :
    (state 10 [] (PSTRTMIncrement009.blocks (doubleDigits digits))).Tape = Turing.Tape.mk₁ (PSTRTMIncrement009.blocks (doubleDigits digits)) := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMDoubleTrace062
