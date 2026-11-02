module
public import Common.PSTR_TM_Trace_002

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMTrace002

variable {a b : Nat}

def leftLabel (q : Fin (a + 1)) : Fin ((a + b + 1) + 1) := ⟨q.val, by omega⟩
def rightLabel (q : Fin (b + 1)) : Fin ((a + b + 1) + 1) := ⟨a + 1 + q.val, by omega⟩
def leftCfg (state : MachineState a) : MachineState (a + b + 1) :=
  ⟨leftLabel state.q, state.Tape⟩
def rightCfg (state : MachineState b) : MachineState (a + b + 1) :=
  ⟨rightLabel state.q, state.Tape⟩

/-- Actual finite-control sequencing. First-machine HALT performs one
head-preserving write and transfers to the second machine's initial label. -/
def seqMachine (first : Machine a) (second : Machine b) : Machine (a + b + 1) :=
  fun q symbol =>
    if h : q.val < a + 1 then
      match first ⟨q.val, h⟩ symbol with
      | none => some (rightLabel (a := a) (0 : Fin (b + 1)), .write symbol)
      | some (q', statement) => some (leftLabel (b := b) q', statement)
    else
      (second ⟨q.val - (a + 1), by omega⟩ symbol).map
        (fun (q', statement) => (rightLabel (a := a) q', statement))

theorem seq_step_left (first : Machine a) (second : Machine b) (state : MachineState a) :
    Turing.TM0.step (seqMachine first second) (leftCfg (b := b) state) =
      match Turing.TM0.step first state with
      | none => some (rightCfg (a := a) ⟨0, state.Tape⟩)
      | some result => some (leftCfg (b := b) result) := by
  cases state with
  | mk q tape =>
    unfold Turing.TM0.step seqMachine leftCfg leftLabel
    simp only [dite_eq_left q.isLt, Fin.eta]
    cases h : first q tape.head with
    | none => simp [rightCfg, Turing.Tape.write_self]
    | some value =>
      obtain ⟨q', statement⟩ := value
      cases statement <;> simp

theorem seq_step_right (first : Machine a) (second : Machine b) (state : MachineState b) :
    Turing.TM0.step (seqMachine first second) (rightCfg (a := a) state) =
      (Turing.TM0.step second state).map (rightCfg (a := a)) := by
  cases state with
  | mk q tape =>
    unfold Turing.TM0.step seqMachine rightCfg rightLabel
    simp only [show ¬a + 1 + q.val < a + 1 by omega, ↓reduceDIte,
      Nat.add_sub_cancel_left, Fin.eta]
    cases h : second q tape.head with
    | none => simp
    | some value =>
      obtain ⟨q', statement⟩ := value
      cases statement <;> simp

/-- A genuine segment may start on a tape retained by a preceding program.
No answer or performance fields are inserted into the machine code. -/
def RunsFrom {states : Nat} (machine : Machine states) (initial : MachineState states)
    (trace : List (MachineState states)) (final : MachineState states) : Prop :=
  trace.head? = some initial ∧
    trace.IsChain (fun before after => Turing.TM0.step machine before = some after) ∧
    trace.getLast? = some final ∧ Turing.TM0.step machine final = none

/-- Concrete trace concatenation charges the first machine's final transfer
step and preserves the entire tape, with no reset or payload reloading. -/
theorem seq_runsFrom (first : Machine a) (second : Machine b)
    (initial finalFirst : MachineState a) (finalSecond : MachineState b)
    (traceFirst : List (MachineState a)) (traceSecond : List (MachineState b))
    (hfirst : RunsFrom first initial traceFirst finalFirst)
    (hsecond : RunsFrom second ⟨0, finalFirst.Tape⟩ traceSecond finalSecond) :
    RunsFrom (seqMachine first second) (leftCfg (b := b) initial)
      (traceFirst.map (leftCfg (b := b)) ++ traceSecond.map (rightCfg (a := a)))
      (rightCfg (a := a) finalSecond) := by
  obtain ⟨hfhead, hfchain, hflast, hfhalt⟩ := hfirst
  obtain ⟨hshead, hschain, hslast, hshalt⟩ := hsecond
  constructor
  · simp [List.head?_append, hfhead, List.head?_map]
  constructor
  · apply List.IsChain.append
    · apply (List.isChain_map _).mpr
      apply hfchain.imp
      intro before after h
      simp [seq_step_left, h]
    · apply (List.isChain_map _).mpr
      apply hschain.imp
      intro before after h
      simp [seq_step_right, h]
    · intro x hx y hy
      simp only [List.getLast?_map, hflast, Option.map_some, Option.mem_some_iff] at hx
      simp only [List.head?_map, hshead, Option.map_some, Option.mem_some_iff] at hy
      subst x
      subst y
      simp [seq_step_left, hfhalt]
  constructor
  · simp [List.getLast?_append, List.getLast?_map, hslast]
  · simp [seq_step_right, hshalt]

theorem seq_trace_length (traceFirst : List (MachineState a)) (traceSecond : List (MachineState b)) :
    (traceFirst.map (leftCfg (b := b)) ++ traceSecond.map (rightCfg (a := a))).length =
      traceFirst.length + traceSecond.length := by simp

/-- Actual sequential runs are in the ORIGINAL B23 trace format. -/
theorem seq_runs (first : Machine a) (second : Machine b) (input : List Bool)
    (finalFirst : MachineState a) (finalSecond : MachineState b)
    (traceFirst : List (MachineState a)) (traceSecond : List (MachineState b))
    (hfirst : Runs first input traceFirst finalFirst)
    (hsecond : RunsFrom second ⟨0, finalFirst.Tape⟩ traceSecond finalSecond) :
    Runs (seqMachine first second) input
      (traceFirst.map (leftCfg (b := b)) ++ traceSecond.map (rightCfg (a := a)))
      (rightCfg (a := a) finalSecond) := by
  have hc := seq_runsFrom first second (Turing.TM0.init input) finalFirst finalSecond
    traceFirst traceSecond ⟨hfirst.1, hfirst.2.1, hfirst.2.2.1, hfirst.2.2.2.1⟩ hsecond
  apply runs_of_chain
  · simpa [leftCfg, leftLabel, Turing.TM0.init] using hc.1
  · exact hc.2.1
  · exact hc.2.2.1
  · exact hc.2.2.2

/-- The composed machine's peak space is bounded by the actual summed
trace lengths, with both input cells and the transfer transition charged. -/
theorem seq_visitedSpace_le (first : Machine a) (second : Machine b) (inputLength : Nat)
    (traceFirst : List (MachineState a)) (traceSecond : List (MachineState b)) :
    visitedSpace (seqMachine first second) inputLength
      (traceFirst.map (leftCfg (b := b)) ++ traceSecond.map (rightCfg (a := a))) ≤
      inputLength + 2 * (traceFirst.length + traceSecond.length) + 1 := by
  simpa [seq_trace_length] using visitedSpace_le (seqMachine first second) inputLength
    (traceFirst.map (leftCfg (b := b)) ++ traceSecond.map (rightCfg (a := a)))

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005


