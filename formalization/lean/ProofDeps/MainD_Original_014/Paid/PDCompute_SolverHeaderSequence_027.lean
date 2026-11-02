module

public import Paid.PDCompute_SolverHeaderCommand_026

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute linearExecute_append)
open PDMenu.ComputeFrame

def headerCode (commands : List HeaderCommand) : List Instruction := commands.flatMap HeaderCommand.code

def headerEval : List HeaderCommand → (ℕ → Cell) → Option (ℕ → Cell)
  | [],values => some values
  | command::commands,values => (command.eval values).bind (headerEval commands)

theorem headerCode_straight (commands : List HeaderCommand) : StraightCode (headerCode commands) := by
  intro instruction member
  obtain ⟨command,_,hin⟩ := List.mem_flatMap.mp member
  exact command.code_straight instruction hin

theorem headerCode_length_le (commands : List HeaderCommand) : (headerCode commands).length ≤ 10*commands.length := by
  induction commands with
  | nil => exact le_refl _
  | cons command commands ih =>
    have hc := command.code_length_le
    simp only [headerCode,List.flatMap_cons,List.length_append,List.length_cons] at ih ⊢
    omega

/-- The symbolic cell-map execution is discharged by actual ORIGINAL-ISA
execution. No cell-map operation is called by the runtime machine. -/
theorem headerCode_realize (commands : List HeaderCommand) (input : List Cell) (before : State)
    (base n k : ℕ) (values next : ℕ → Cell)
    (valid : ∀ command ∈ commands, command.Valid)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (heval : headerEval commands values=some next) :
    ∃ after : State, linearExecute input (headerCode commands) before=some after ∧ Header after base next ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+(headerCode commands).length ∧
      Frame before after base n k ∧ after.output=before.output := by
  induction commands generalizing before values with
  | nil =>
    have he : values=next := Option.some.inj heval
    subst next
    refine ⟨before,rfl,header,hbase,rfl,?_,rfl⟩
    exact ⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩
  | cons command commands ih =>
    obtain ⟨middleValues,hfirst,hlater⟩ := Option.bind_eq_some_iff.mp heval
    obtain ⟨middle,hrun,hh,hb,hpc,hframe,hout⟩ :=
      command.realize input before base n k values middleValues (valid command (by simp)) header hbase hfirst
    obtain ⟨after,hrunAfter,hhAfter,hbAfter,hpcAfter,hframeAfter,houtAfter⟩ :=
      ih middle middleValues (fun c hm => valid c (by simp only [List.mem_cons]; exact Or.inr hm)) hh hb hlater
    refine ⟨after,?_,hhAfter,hbAfter,?_,hframe.trans hframeAfter,houtAfter.trans hout⟩
    · simp only [headerCode,List.flatMap_cons,linearExecute_append,hrun,Option.bind_some]
      exact hrunAfter
    · simp only [headerCode,List.flatMap_cons,List.length_append]
      rw [hpcAfter,hpc]
      exact Nat.add_assoc _ _ _

private theorem sequenceTime (commands : ℕ) : 15*(10*commands+1) ≤ 165*(commands+1) := by omega

theorem headerCode_trace (commands : List HeaderCommand) (program : Program) (input : List Cell) (before : State)
    (base n k : ℕ) (values next : ℕ → Cell)
    (valid : ∀ command ∈ commands, command.Valid)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (heval : headerEval commands values=some next)
    (hfetch : FetchesCode program before.pc (headerCode commands)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 165*(commands.length+1) ∧
      Header after base next ∧ after.register .fresh=.natural base ∧
      after.pc=before.pc+(headerCode commands).length ∧ Frame before after base n k ∧
      after.output=before.output ∧
      ∀ state ∈ trace.dropLast, ∃ count < (headerCode commands).length,
        linearExecute input ((headerCode commands).take count) before=some state := by
  obtain ⟨after,hrun,hh,hb,hpc,hframe,hout⟩ :=
    headerCode_realize commands input before base n k values next valid header hbase heval
  obtain ⟨trace,htHead,htLast,htChain,htTime,htPrefixes⟩ :=
    linearExecute_trace_time program input (headerCode commands) (headerCode_straight commands)
      before after hfetch hrun
  refine ⟨trace,after,htHead,htLast,htChain,?_,hh,hb,hpc,hframe,hout,htPrefixes⟩
  exact htTime.trans ((Nat.mul_le_mul_left 15 (Nat.add_le_add_right (headerCode_length_le commands) 1)).trans
    (sequenceTime commands.length))

end PDCompute.Solver
