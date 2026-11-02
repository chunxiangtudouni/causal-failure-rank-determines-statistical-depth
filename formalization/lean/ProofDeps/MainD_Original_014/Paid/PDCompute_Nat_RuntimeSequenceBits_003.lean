module
public import Paid.PDCompute_Nat_RuntimeCommandBits_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
@[expose] public section
namespace PDCompute.NatControl
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute linearExecute_append)
open PDROC.CalibrationRow.Operand

theorem runtimeCommand_straight (command : RuntimeCommand) : StraightCode command.code := by
  cases command with
  | scalar command => exact command.code_straight
  | natural operation left right target => exact natBinarySlots_straight operation left right target

theorem runtimeCode_straight (commands : List RuntimeCommand) : StraightCode (runtimeCode commands) := by
  intro instruction member
  obtain ⟨command,_,member⟩:=List.mem_flatMap.mp member
  exact runtimeCommand_straight command instruction member

theorem runtimeCode_realize (commands : List RuntimeCommand) (input : List Cell) (before : State)
    (base n k : ℕ) (values next : ℕ → Cell)
    (valid : ∀ command ∈ commands, command.Valid)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (heval : runtimeEval commands values=some next) :
    ∃ after : State, linearExecute input (runtimeCode commands) before=some after ∧ Header after base next ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+(runtimeCode commands).length ∧
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
      runtimeCommand_realize command input before base n k values middleValues (valid command (by simp)) header hbase hfirst
    obtain ⟨after,hrunAfter,hhAfter,hbAfter,hpcAfter,hframeAfter,houtAfter⟩ :=
      ih middle middleValues (fun c hm => valid c (by simp only [List.mem_cons]; exact Or.inr hm)) hh hb hlater
    refine ⟨after,?_,hhAfter,hbAfter,?_,hframe.trans hframeAfter,houtAfter.trans hout⟩
    · simp only [runtimeCode,List.flatMap_cons,linearExecute_append,hrun,Option.bind_some]
      exact hrunAfter
    · simp only [runtimeCode,List.flatMap_cons,List.length_append]
      rw [hpcAfter,hpc]
      exact Nat.add_assoc _ _ _

theorem runtimeCode_prefix_memory (commands : List RuntimeCommand) (input : List Cell) (before after : State)
    (base : ℕ) (values next : ℕ → Cell)
    (valid : ∀ command ∈ commands, command.Valid)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (heval : runtimeEval commands values=some next) (count : ℕ) (hcount : count ≤ (runtimeCode commands).length)
    (hexec : linearExecute input ((runtimeCode commands).take count) before=some after) :
    HeaderMemory before after base := by
  induction commands generalizing before values count with
  | nil =>
    have eq : before=after := by
      simpa only [runtimeCode,List.flatMap_nil,List.take_nil,linearExecute,Option.some.injEq] using hexec
    subst after
    exact HeaderMemory.refl before base
  | cons command commands ih =>
    obtain ⟨middleValues,hfirst,hlater⟩ := Option.bind_eq_some_iff.mp heval
    have firstValid : command.Valid := valid command (by simp)
    by_cases short : count ≤ command.code.length
    · have takeEq : (runtimeCode (command::commands)).take count=command.code.take count := by
        exact List.take_append_of_le_length short
      rw [takeEq] at hexec
      exact runtimeCommand_prefix_memory command input before after base values middleValues firstValid header hbase hfirst count short hexec
    · have firstLe : command.code.length ≤ count := by omega
      obtain ⟨middle,firstRun,middleHeader,middleBase,_,_,_⟩ :=
        runtimeCommand_realize command input before base 0 0 values middleValues firstValid header hbase hfirst
      have takeEq : (runtimeCode (command::commands)).take count=
          command.code++(runtimeCode commands).take (count-command.code.length) := by
        change (command.code++runtimeCode commands).take count=_
        rw [List.take_append,List.take_of_length_le firstLe]
      rw [takeEq,linearExecute_append,firstRun,Option.bind_some] at hexec
      have tailBound : count-command.code.length ≤ (runtimeCode commands).length := by
        change count ≤ (command.code++runtimeCode commands).length at hcount
        rw [List.length_append] at hcount
        omega
      have firstMemory := runtimeCommand_prefix_memory command input before middle base values middleValues firstValid header hbase
        hfirst command.code.length (le_refl _) (by simpa only [List.take_length] using firstRun)
      have laterMemory := ih middle middleValues
        (fun c member => valid c (by simp only [List.mem_cons]; exact Or.inr member))
        middleHeader middleBase hlater (count-command.code.length) tailBound hexec
      exact firstMemory.trans laterMemory


def RuntimeEvaluatedBits (budget : ℕ) : List RuntimeCommand → (ℕ → Cell) → Prop
  | [],_ => True
  | command::rest,values => ∃ next,command.eval values=some next ∧ HeaderValueBits next budget ∧ RuntimeEvaluatedBits budget rest next

theorem runtimeCode_prefix_safe (commands : List RuntimeCommand) (input : List Cell) (before : State)
    (base budget : ℕ) (values : ℕ → Cell) (valid : ∀ command∈commands,command.Valid)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (safe : RootD27.Bits.SafeBits before budget) (bounded : RuntimeEvaluatedBits budget commands values)
    (addressBits : 1+natBits (base+headerWords)≤budget) (pcBits : natBits (before.pc+(runtimeCode commands).length)≤budget) :
    PrefixSafe input (runtimeCode commands) before budget := by
  induction commands generalizing before values with
  | nil => exact PrefixSafe.nil input before budget safe
  | cons command rest ih =>
    obtain ⟨next,evaluated,nextBits,tailBounds⟩:=bounded
    have commandValid : command.Valid := valid command (by simp)
    obtain ⟨middle,run,middleHeader,middleFresh,middlePC,_,_⟩:=runtimeCommand_realize command input before base 0 0 values next commandValid header fresh evaluated
    have firstPC : natBits (before.pc+command.code.length)≤budget :=
      (natBits_mono (by change before.pc+command.code.length≤before.pc+(command.code++runtimeCode rest).length; rw [List.length_append]; omega)).trans pcBits
    have firstSafe:=runtimeCommand_prefix_safe command input before base budget values next commandValid header fresh evaluated safe nextBits addressBits firstPC
    have laterPC : natBits (middle.pc+(runtimeCode rest).length)≤budget := by
      rw [middlePC]
      simpa only [runtimeCode,List.flatMap_cons,List.length_append,Nat.add_assoc] using pcBits
    have laterSafe:=ih middle next (fun command member=>valid command (by simp only [List.mem_cons]; exact Or.inr member))
      middleHeader middleFresh (firstSafe.final run) tailBounds laterPC
    exact PrefixSafe.append input command.code (runtimeCode rest) before middle budget run firstSafe laterSafe

/-- Canonical real scalar-block trace with memory and operand bits on
the SAME witness. The concrete block supplies evaluated-value bounds,
not a machine run or postulated final resource guarantee. -/
theorem runtimeCode_trace_bits (commands : List RuntimeCommand) (program : Program) (input : List Cell) (before : State)
    (base n k budget : ℕ) (values next : ℕ → Cell) (valid : ∀ command∈commands,command.Valid)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (evaluated : runtimeEval commands values=some next) (safe : RootD27.Bits.SafeBits before budget)
    (bounded : RuntimeEvaluatedBits budget commands values) (addressBits : 1+natBits (base+headerWords)≤budget)
    (pcBits : natBits (before.pc+(runtimeCode commands).length)≤budget)
    (fetch : FetchesCode program before.pc (runtimeCode commands)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤165*(commands.length+1) ∧
      Header after base next ∧ after.register .fresh=.natural base ∧ after.pc=before.pc+(runtimeCode commands).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  obtain ⟨after,run,afterHeader,afterFresh,afterPC,frame,output⟩:=runtimeCode_realize commands input before base n k values next valid header fresh evaluated
  have prefixSafe:=runtimeCode_prefix_safe commands input before base budget values valid header fresh safe bounded addressBits pcBits
  obtain ⟨trace,head,last,chain,cost,invariant⟩:=PDCompute.Pack.linearExecute_trace_invariant program input (runtimeCode commands)
    (runtimeCode_straight commands) before after fetch run (fun state=>HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget) (by
      intro count bound state executed
      exact ⟨runtimeCode_prefix_memory commands input before state base values next valid header fresh evaluated count bound executed,prefixSafe count state executed⟩)
  refine ⟨trace,after,head,last,chain,?_,afterHeader,afterFresh,afterPC,frame,output,invariant⟩
  have codeBound:=runtimeCode_length_le commands
  omega


end PDCompute.NatControl
