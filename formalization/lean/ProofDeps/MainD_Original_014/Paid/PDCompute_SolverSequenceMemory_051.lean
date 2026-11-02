module

public import Paid.PDCompute_SolverCommandMemory_050

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute linearExecute_append)
open PDMenu.ComputeFrame

/-- Every successful literal prefix of a valid scalar command sequence
has this exact header48-only footprint. The result includes the terminal
prefix as well as every intermediate instruction, and keeps live/output
exactly equal to the caller's original state. -/
theorem headerCode_prefix_memory (commands : List HeaderCommand) (input : List Cell) (before after : State)
    (base : ℕ) (values next : ℕ → Cell)
    (valid : ∀ command ∈ commands, command.Valid)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (heval : headerEval commands values=some next) (count : ℕ) (hcount : count ≤ (headerCode commands).length)
    (hexec : linearExecute input ((headerCode commands).take count) before=some after) :
    HeaderMemory before after base := by
  induction commands generalizing before values count with
  | nil =>
    have eq : before=after := by
      simpa only [headerCode,List.flatMap_nil,List.take_nil,linearExecute,Option.some.injEq] using hexec
    subst after
    exact HeaderMemory.refl before base
  | cons command commands ih =>
    obtain ⟨middleValues,hfirst,hlater⟩ := Option.bind_eq_some_iff.mp heval
    have firstValid : command.Valid := valid command (by simp)
    by_cases short : count ≤ command.code.length
    · have takeEq : (headerCode (command::commands)).take count=command.code.take count := by
        exact List.take_append_of_le_length short
      rw [takeEq] at hexec
      exact command.prefix_memory input before after base values middleValues firstValid header hbase hfirst count short hexec
    · have firstLe : command.code.length ≤ count := by omega
      obtain ⟨middle,firstRun,middleHeader,middleBase,_,_,_⟩ :=
        command.realize input before base 0 0 values middleValues firstValid header hbase hfirst
      have takeEq : (headerCode (command::commands)).take count=
          command.code++(headerCode commands).take (count-command.code.length) := by
        change (command.code++headerCode commands).take count=_
        rw [List.take_append,List.take_of_length_le firstLe]
      rw [takeEq,linearExecute_append,firstRun,Option.bind_some] at hexec
      have tailBound : count-command.code.length ≤ (headerCode commands).length := by
        change count ≤ (command.code++headerCode commands).length at hcount
        rw [List.length_append] at hcount
        omega
      have firstMemory := command.prefix_memory input before middle base values middleValues firstValid header hbase
        hfirst command.code.length (le_refl _) (by simpa only [List.take_length] using firstRun)
      have laterMemory := ih middle middleValues
        (fun c member => valid c (by simp only [List.mem_cons]; exact Or.inr member))
        middleHeader middleBase hlater (count-command.code.length) tailBound hexec
      exact firstMemory.trans laterMemory

theorem headerCode_memory (commands : List HeaderCommand) (input : List Cell) (before after : State)
    (base : ℕ) (values next : ℕ → Cell)
    (valid : ∀ command ∈ commands, command.Valid)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (heval : headerEval commands values=some next)
    (hexec : linearExecute input (headerCode commands) before=some after) :
    HeaderMemory before after base :=
  headerCode_prefix_memory commands input before after base values next valid header hbase heval
    (headerCode commands).length (le_refl _) (by simpa only [List.take_length] using hexec)

theorem headerCode_trace_memory (commands : List HeaderCommand) (program : Program) (input : List Cell) (before : State)
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
      after.output=before.output ∧ ∀ state ∈ trace, HeaderMemory before state base := by
  obtain ⟨after,run,afterHeader,afterBase,afterPC,afterFrame,afterOutput⟩ :=
    headerCode_realize commands input before base n k values next valid header hbase heval
  obtain ⟨trace,hh,hl,hchain,ht,prefixes⟩ :=
    linearExecute_trace_time program input (headerCode commands) (headerCode_straight commands) before after hfetch run
  have timeBound : time program trace ≤ 165*(commands.length+1) := by
    have lengthBound := headerCode_length_le commands
    omega
  have lastEq : ∀ state ∈ trace, state ∈ trace.dropLast ∨ state=after := by
    intro state member
    have split := List.dropLast_append_getLast? after (by rw [hl]; simp)
    rw [← split] at member
    simpa only [List.mem_append,List.mem_singleton] using member
  refine ⟨trace,after,hh,hl,hchain,timeBound,afterHeader,afterBase,afterPC,afterFrame,afterOutput,?_⟩
  intro state member
  rcases lastEq state member with proper|last
  · obtain ⟨count,bound,execute⟩ := prefixes state proper
    exact headerCode_prefix_memory commands input before state base values next valid header hbase heval count (Nat.le_of_lt bound) execute
  · subst state
    exact headerCode_memory commands input before after base values next valid header hbase heval run

end PDCompute.Solver
