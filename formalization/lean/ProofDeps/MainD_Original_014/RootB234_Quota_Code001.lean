module

public import RootB234_PrepEntry_StageArithmeticPublic_088
public import RootB234_PrepEntry_ScalarPacketPublic_102
public import RootB234_PrepExponent_NatToRatPublic008

/-! A fixed first-success quota search. Every number is read from its
physical packet. The outer archive is a renamed, paid StageStash; in
particular the original raw cursor is the untouched tail of that archive.
The store is exactly the existing global store, with arbitrary entry flags. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.Quota
open Turing PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM B23_4_RatWordPrep
open RootB234.PrepExponent RootB234.PrepEntry

abbrev Store (C : Type*) := Global.Store C
abbrev Core (C : Type*) := StageArithmetic.Core C
abbrev Stack := RatInput.Stack
abbrev Bank := Stack → List Bool
abbrev PC := Fin 50

inductive NatSource where
  | exponent | prior | channels | counter
  deriving DecidableEq
instance : Fintype NatSource where
  elems := {.exponent,.prior,.channels,.counter}
  complete := by intro point;cases point <;> simp
def natSlot : NatSource → Stack
  | .exponent => 5 | .prior => 13 | .channels => 14 | .counter => 11

inductive Literal where
  | negativeOne | two | eight | zeroCounter
  deriving DecidableEq
instance : Fintype Literal where
  elems := {.negativeOne,.two,.eight,.zeroCounter}
  complete := by intro point;cases point <;> simp
def literalBits : Literal → List Bool
  | .negativeOne => RatInput.Encoder.packet (-1) []
  | .two => RatInput.Encoder.packet 2 []
  | .eight => RatInput.Encoder.packet 8 []
  | .zeroCounter => NatField.packet 0 []
def literalSlot : Literal → Stack
  | .zeroCounter => 11 | _ => 15

inductive Instruction where
  | natural (source : NatSource) (next : PC)
  | transport (copy : Bool) (source target : Stack) (next : PC)
  | arithmetic (multiply : Bool) (next : PC)
  | drop (slot : Stack) (next : PC)
  | literal (value : Literal) (next : PC)
  | probe (negative nonnegative : PC)
  | increment (next : PC)
  | finish
  deriving DecidableEq,Fintype

/-- All instruction addresses and all literal packets precede all data. -/
def instruction (point : PC) : Instruction :=
  match point.val with
  | 0 => .natural .exponent 1
  | 1 => .transport false 15 2 2
  | 2 => .natural .prior 3
  | 3 => .literal .negativeOne 4
  | 4 => .arithmetic true 5
  | 5 => .transport true 2 15 6
  | 6 => .arithmetic false 7
  | 7 => .literal .two 8
  | 8 => .arithmetic true 9
  | 9 => .transport false 15 3 10
  | 10 => .natural .channels 11
  | 11 => .transport true 15 7 12
  | 12 => .transport true 7 15 13
  | 13 => .arithmetic true 14
  | 14 => .literal .eight 15
  | 15 => .arithmetic true 16
  | 16 => .transport true 2 15 17
  | 17 => .arithmetic true 18
  | 18 => .transport false 15 6 19
  | 19 => .drop 7 20
  | 20 => .drop 2 21
  | 21 => .transport true 12 15 22
  | 22 => .transport true 12 15 23
  | 23 => .arithmetic true 24
  | 24 => .transport false 15 7 25
  | 25 => .literal .zeroCounter 26
  | 26 => .natural .counter 27
  | 27 => .transport false 15 2 28
  | 28 => .transport true 3 15 29
  | 29 => .transport true 2 15 30
  | 30 => .transport true 12 15 31
  | 31 => .arithmetic true 32
  | 32 => .arithmetic false 33
  | 33 => .probe 47 34
  | 34 => .drop 15 35
  | 35 => .transport true 6 15 36
  | 36 => .transport true 2 15 37
  | 37 => .transport true 7 15 38
  | 38 => .arithmetic true 39
  | 39 => .arithmetic false 40
  | 40 => .probe 47 41
  | 41 => .drop 15 42
  | 42 => .drop 2 43
  | 43 => .drop 3 44
  | 44 => .drop 6 45
  | 45 => .drop 7 46
  | 46 => .finish
  | 47 => .drop 15 48
  | 48 => .drop 2 49
  | _ => .increment 26

inductive Label where
  | control : PC → Label
  | natural : NatSource → PC → NatToRat.Label → Label
  | transport : Bool → Stack → Stack → PC → RatPacketTransport.Label → Label
  | arithmetic : Bool → PC → StageArithmetic.Label → Label
  | drop : Stack → PC → ScalarPacket.Label → Label
  | probe : PC → PC → ScalarPacket.Label → Label
  | decision : PC → PC → Label
  | increment : PC → NatIncrement.Label → Label
  | stash : StageStash.Label → Label
  | restore : StageStash.Label → Label
  | done
  deriving DecidableEq,Fintype
instance : Inhabited Label := ⟨.stash (.start 0)⟩
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)
variable {C : Type*}

/-- Image of the StageStash slots. Its eight saved slots are exactly
2,3,6,7,15,4,10,8. Thus original input5/12/13/14 and result11 survive it. -/
def archiveIndex (slot : Stack) : Stack :=
  match slot.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 6
  | 6 => 7 | 7 => 9 | 8 => 11 | 9 => 12 | 10 => 15 | 11 => 13
  | 12 => 4 | 13 => 10 | 14 => 8 | _ => 14
noncomputable def archiveRoles : Stack ≃ Stack := Equiv.ofBijective archiveIndex (by decide)

def naturalRoles (source : NatSource) : Stack ≃ Stack :=
  ((Equiv.swap 3 4).trans (Equiv.swap 3 10)).trans (Equiv.swap 8 (natSlot source))
def transportRoles (source target : Stack) : Stack ≃ Stack :=
  let first := Equiv.swap (15 : Stack) source
  first.trans (Equiv.swap (first 2) target)
def incrementRoles : Stack ≃ Stack := Equiv.swap 3 4

def stashLabel (point : StageStash.Label) : Label :=
  if point=.saved then .control 0 else .stash point
def restoreLabel (point : StageStash.Label) : Label :=
  if point=.restored then .done else .restore point
def naturalLabel (source : NatSource) (next : PC) (point : NatToRat.Label) : Label :=
  if point=.done then .control next else .natural source next point
def transportLabel (copy : Bool) (source target : Stack) (next : PC) (point : RatPacketTransport.Label) : Label :=
  if point=4 then .control next else .transport copy source target next point
def arithmeticLabel (multiply : Bool) (next : PC) (point : StageArithmetic.Label) : Label :=
  if point=.done then .control next else .arithmetic multiply next point
def dropLabel (slot : Stack) (next : PC) (point : ScalarPacket.Label) : Label :=
  if point=.done then .control next else .drop slot next point
def probeLabel (negative nonnegative : PC) (point : ScalarPacket.Label) : Label :=
  if point=.done then .decision negative nonnegative else .probe negative nonnegative point
def incrementLabel (next : PC) (point : NatIncrement.Label) : Label :=
  if point=4 then .control next else .increment next point

def literalPush (slot : Stack) (bits : List Bool) (next : Label) : Statement C :=
  bits.reverse.foldr (fun bit tail => .push slot (fun _ => bit) tail) (.goto (fun _ => next))
def control (op : Instruction) : Statement C :=
  match op with
  | .natural source next => .goto (fun _ => .natural source next .prepare)
  | .transport copy source target next => .goto (fun _ => .transport copy source target next 0)
  | .arithmetic multiply next => .goto (fun _ => .arithmetic multiply next default)
  | .drop slot next => .goto (fun _ => .drop slot next .rational)
  | .literal value next => literalPush (literalSlot value) (literalBits value) (.control next)
  | .probe negative nonnegative => .goto (fun _ => .probe negative nonnegative .sign)
  | .increment next => .goto (fun _ => .increment next 0)
  | .finish => .goto (fun _ => .restore (.clear 7))

noncomputable def program (caller : Statement C) : Label → Statement C
  | .control point => control (instruction point)
  | .natural source next point => LabelMap.statement (naturalLabel source next)
      (StackIso.statement (naturalRoles source) (NatToRat.program .halt point))
  | .transport copy source target next point => LabelMap.statement (transportLabel copy source target next)
      (RatPacketTransport.atProgram (transportRoles source target) copy point)
  | .arithmetic multiply next point => LabelMap.statement (arithmeticLabel multiply next)
      (StageArithmetic.program multiply .halt point)
  | .drop slot next point => LabelMap.statement (dropLabel slot next)
      (StackIso.statement (Equiv.swap 15 slot) (ScalarPacket.program .halt point))
  | .probe negative nonnegative point => LabelMap.statement (probeLabel negative nonnegative)
      (ScalarPacket.program .halt point)
  | .decision negative nonnegative => .branch (fun memory => memory.2.2)
      (.goto (fun _ => .control negative)) (.goto (fun _ => .control nonnegative))
  | .increment next point => LabelMap.statement (incrementLabel next)
      (StackIso.statement incrementRoles (NatIncrement.program .halt point))
  | .stash point => LabelMap.statement stashLabel (StackIso.statement archiveRoles (StageStash.source point))
  | .restore point => LabelMap.statement restoreLabel (StackIso.statement archiveRoles (StageStash.source point))
  | .done => caller

def state (point : Label) (memory : Store C) (before : Bank) : State C := ⟨some point,memory,before⟩
def output (before : Bank) (quota : Nat) : Bank := Function.update before 11 (NatField.packet quota [])
def inputScale (before : Bank) (e b m quota : Nat) : Nat := RatInput.occupied before+e+b+m+quota+1
def target (e b m : Nat) (d : Rat) : Rat :=
  max (2*((e : Rat)+b)/d) (8*(m : Rat)^2*e/d^2)
def quota (e b m : Nat) (d : Rat) : Nat := ⌈target e b m d⌉₊

private theorem supports_stmt (body : Statement C) : TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto _ => intro _;exact Finset.mem_univ _
  | halt => trivial
theorem supports (caller : Statement C) : TM2.Supports (program caller) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun point _ => supports_stmt (program caller point)⟩
theorem finite_store [Finite C] : Finite (Store C) := Global.finite_store

end RootB234.Quota
