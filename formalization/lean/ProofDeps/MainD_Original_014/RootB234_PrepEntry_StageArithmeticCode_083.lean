module

public import RootB234_PrepEntry_NatPacketPublic_081
public import RootB234_StageStash_Public008
public import RootB234_PrepExponent_GlobalRun040

/-! The stage archives are genuinely stashed before a concrete binary
call, then restored around the actual new result15. The fixed store is
exactly the existing global exponent store, including all actual flags. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.StageArithmetic
open Turing PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootB234.PrepExponent

abbrev Store (C : Type*) := Global.Store C
abbrev Core (C : Type*) := RootL01.SymbolicSource.PacketUnary.Store (Arithmetic.Aux×C)
abbrev Stack := RatInput.Stack
abbrev Bank := Stack → List Bool

inductive Label where
  | stash : StageStash.Label → Label
  | binary : RatBinary.Label → Label
  | restore : StageStash.Label → Label
  | done
  deriving DecidableEq,Fintype
instance : Inhabited Label := ⟨.stash (.start 0)⟩
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)
variable {C : Type*}

def result (multiply : Bool) (x y : Rat) : Rat := if multiply then x*y else x-y
def binary (multiply : Bool) : RatBinary.Label → TM2.Stmt RatInput.Alphabet RatBinary.Label (Store C) :=
  fun point => StoreIso.statement (QLoop.arithmeticIso C)
    (if multiply then Arithmetic.mulProgram point else Arithmetic.subProgram point)

def stashLabel (point : StageStash.Label) : Label :=
  if point=.saved then .binary default else .stash point
def binaryLabel (point : RatBinary.Label) : Label :=
  if point=.done then .restore (.clear 7) else .binary point
def restoreLabel (point : StageStash.Label) : Label :=
  if point=.restored then .done else .restore point

def program (multiply : Bool) (caller : Statement C) : Label → Statement C
  | .stash point => LabelMap.statement stashLabel (StageStash.source point)
  | .binary point => LabelMap.statement binaryLabel (binary multiply point)
  | .restore point => LabelMap.statement restoreLabel (StageStash.source point)
  | .done => caller

def state (point : Label) (memory : Store C) (before : Bank) : State C := ⟨some point,memory,before⟩
def output (before : Bank) (cells : List Bool) : Bank := Function.update before 15 cells

theorem same_store : StageStash.Store (Core C)=Store C := rfl

theorem stash_bank (before : Bank) (x y : Rat) (tail : List Bool)
    (source : before 15=RatPair.input x y tail) (temporary : before 4=[]) :
    Global.bank (StageStash.stashBank before 8) (before 7) (before 11)
      (RatPair.input x y tail) [] [] []=StageStash.stashBank before 8 := by
  funext slot
  fin_cases slot <;> simp_all [Global.bank,StageStash.stashBank,StageStash.index]

theorem result_bank (before : Bank) (value : Rat) (tail : List Bool) (temporary : before 4=[]) :
    Global.bank (StageStash.stashBank before 8) (before 7) (before 11)
      (RatInput.Encoder.packet value tail) [] [] []=
      output (StageStash.stashBank before 8) (RatInput.Encoder.packet value tail) := by
  funext slot
  fin_cases slot <;> simp_all [Global.bank,output,StageStash.stashBank,StageStash.index]

theorem restored_bank (before : Bank) (cells : List Bool) :
    StageStash.restoreBank before (output (StageStash.stashBank before 8) cells) 0=output before cells := by
  funext slot
  fin_cases slot <;> simp [StageStash.restoreBank,StageStash.spool,StageStash.index,StageStash.stashBank,output]

structure Segment (multiply : Bool) (caller : Statement C) (before final : State C) where
  trace : List (State C)
  first : trace.head?=some before
  chain : trace.IsChain (fun a b => TM2.step (program multiply caller) a=some b)
  last : trace.getLast?=some final

def Segment.append {multiply : Bool} {caller : Statement C} {before middle final : State C}
    (front : Segment multiply caller before middle) (back : Segment multiply caller middle final) :
    Segment multiply caller before final := by
  have shape : middle::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp back.first
    rw [same];rfl
  exact ⟨front.trace++back.trace.tail,by rw [List.head?_append,front.first];rfl,
    NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain),
    (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)⟩

theorem Segment.append_length {multiply : Bool} {caller : Statement C} {before middle final : State C}
    (front : Segment multiply caller before middle) (back : Segment multiply caller middle final) :
    (front.append back).trace.length≤front.trace.length+back.trace.length := by
  change (front.trace++back.trace.tail).length≤_
  simp only [List.length_append,List.length_tail];omega

theorem label_path {Λ : Type*} (mapping : Λ → Label)
    (old : Λ → TM2.Stmt RatInput.Alphabet Λ (Store C)) (multiply : Bool) (caller : Statement C)
    (port : Λ) (atPort : old port=.halt) (trace : List (TM2.Cfg RatInput.Alphabet Λ (Store C)))
    (before final : TM2.Cfg RatInput.Alphabet Λ (Store C))
    (first : trace.head?=some before) (chain : trace.IsChain (fun a b => TM2.step old a=some b))
    (last : trace.getLast?=some final) (active : final.l=some port)
    (same : ∀ point,point≠port→program multiply caller (mapping point)=LabelMap.statement mapping (old point)) :
    (trace.map (LabelMap.configuration mapping)).head?=some (LabelMap.configuration mapping before) ∧
    (trace.map (LabelMap.configuration mapping)).IsChain (fun a b => TM2.step (program multiply caller) a=some b) ∧
    (trace.map (LabelMap.configuration mapping)).getLast?=some (LabelMap.configuration mapping final) := by
  have proper:=NativeMulLink.no_early_halt_port old port atPort trace final chain last active
  have linked:=LabelMap.actual_path_on mapping old (program multiply caller) trace before final first chain last
    (by intro current member point selected;exact same point (by intro equal;subst point;exact proper current member selected))
  exact ⟨linked.1,linked.2.1,linked.2.2.1⟩

private theorem supports_stmt (body : Statement C) : TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro _;exact Finset.mem_univ _
  | halt => trivial

theorem supports (multiply : Bool) (caller : Statement C) :
    TM2.Supports (program multiply caller) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun point _ => supports_stmt (program multiply caller point)⟩

theorem finite_store [Finite C] : Finite (Store C) := Global.finite_store

end RootB234.PrepEntry.StageArithmetic
