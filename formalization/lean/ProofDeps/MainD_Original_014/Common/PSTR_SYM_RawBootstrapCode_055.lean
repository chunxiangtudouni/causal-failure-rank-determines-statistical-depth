module

public import Common.PSTR_SYM_CursorArchive_054

/-! SOURCEONLY until its own later strict batch. A fixed original-header
bootstrap with seven genuinely called finite blocks. The physical proof
must still produce their exact adjoining tapes; no count/width is code. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawBootstrap

open Turing PSTRTMSeq005 PSTRSymbolicCounter PSTRSymbolicPairedArchive
open PSTRSymbolicZeroTail PA17TMRatArithmeticParse002 PSTRSymbolicCursorCode PSTRSymbolicCursorStages

def pairMachine : Machine 219 := seqMachine datumCompactMachine datumCompactMachine

inductive BootLabel where
  | entry : Fin 24 → BootLabel
  | first : Fin 17 → BootLabel
  | one : Fin 20 → BootLabel
  | rewind : Fin 6 → BootLabel
  | second : Fin 17 → BootLabel
  | two : Fin 20 → BootLabel
  | pair : Fin 220 → BootLabel
  | halt : BootLabel
  deriving DecidableEq, Fintype

instance : Inhabited BootLabel := ⟨.entry 0⟩

def bootstrapCode : TM0.Machine Bool BootLabel
  | .entry q, bit => calledCode counterEntryMachine BootLabel.entry (fun _ => .first 0) q bit
  | .first q, bit => calledCode counterRoundMachine BootLabel.first (fun _ => .one 18) q bit
  | .one q, bit => calledCode right19Machine BootLabel.one (fun _ => .rewind 0) q bit
  | .rewind q, bit => calledCode fieldBackMachine BootLabel.rewind (fun _ => .second 0) q bit
  | .second q, bit => calledCode counterRoundMachine BootLabel.second (fun _ => .two 18) q bit
  | .two q, bit => calledCode right19Machine BootLabel.two (fun _ => .pair 0) q bit
  | .pair q, bit => calledCode pairMachine BootLabel.pair (fun _ => .halt) q bit
  | .halt, _ => none

/-- A segment records actual adjacent configurations of ONE whole table.
Its joining operation requires the real edge between the two endpoints. -/
structure RunPart {Target : Type} [Inhabited Target] (whole : TM0.Machine Bool Target)
    (first last : TM0.Cfg Bool Target) where
  trace : List (TM0.Cfg Bool Target)
  head : trace.head? = some first
  chain : trace.IsChain (fun before after => TM0.step whole before = some after)
  last : trace.getLast? = some last

def RunPart.append {Target : Type} [Inhabited Target] {whole : TM0.Machine Bool Target}
    {first middle next last : TM0.Cfg Bool Target}
    (left : RunPart whole first middle) (right : RunPart whole next last)
    (edge : TM0.step whole middle = some next) : RunPart whole first last where
  trace := left.trace ++ right.trace
  head := by simp only [List.head?_append,left.head,Option.some_or]
  chain := by
    apply List.IsChain.append left.chain right.chain
    intro before beforeLast after afterHead
    simp only [left.last,Option.mem_some_iff] at beforeLast
    simp only [right.head,Option.mem_some_iff] at afterHead
    subst before
    subst after
    exact edge
  last := by simp only [List.getLast?_append,right.last,Option.some_or]

theorem RunPart.append_length {Target : Type} [Inhabited Target] {whole : TM0.Machine Bool Target}
    {first middle next last : TM0.Cfg Bool Target}
    (left : RunPart whole first middle) (right : RunPart whole next last)
    (edge : TM0.step whole middle = some next) :
    (left.append right edge).trace.length = left.trace.length + right.trace.length :=
  List.length_append

def nativePart {states : Nat} {Target : Type} [Inhabited Target]
    (whole : TM0.Machine Bool Target) (callee : Machine states)
    (tag finish : Fin (states + 1) → Target)
    (code : ∀ q bit, whole (tag q) bit = calledCode callee tag finish q bit)
    (entry final : MachineState states) (trace : List (MachineState states))
    (actual : RunsFrom callee entry trace final) :
    RunPart whole (tagCfg tag entry) (tagCfg tag final) where
  trace := trace.map (tagCfg tag)
  head := (called_endpoints whole callee tag finish code entry final trace actual).1
  chain := (called_endpoints whole callee tag finish code entry final trace actual).2.1
  last := (called_endpoints whole callee tag finish code entry final trace actual).2.2.1

theorem nativePart_length {states : Nat} {Target : Type} [Inhabited Target]
    (whole : TM0.Machine Bool Target) (callee : Machine states)
    (tag finish : Fin (states + 1) → Target)
    (code : ∀ q bit, whole (tag q) bit = calledCode callee tag finish q bit)
    (entry final : MachineState states) (trace : List (MachineState states))
    (actual : RunsFrom callee entry trace final) :
    (nativePart whole callee tag finish code entry final trace actual).trace.length = trace.length :=
  List.length_map _

theorem nativePart_return {states : Nat} {Target : Type} [Inhabited Target]
    (whole : TM0.Machine Bool Target) (callee : Machine states)
    (tag finish : Fin (states + 1) → Target)
    (code : ∀ q bit, whole (tag q) bit = calledCode callee tag finish q bit)
    (entry final : MachineState states) (trace : List (MachineState states))
    (actual : RunsFrom callee entry trace final) :
    TM0.step whole (tagCfg tag final) = some ⟨finish final.q,final.Tape⟩ :=
  (called_endpoints whole callee tag finish code entry final trace actual).2.2.2.1

theorem bootstrap_halt (tape : Tape Bool) : TM0.step bootstrapCode ⟨.halt,tape⟩ = none := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawBootstrap
