module

public import Common.PSTR_SYM_CursorPorts_047
public import Common.PSTR_SYM_FiniteRelabel_007
public import Mathlib.Tactic.DeriveFintype

/-! One finite global cursor/counter code table. Every callee return is an
actual WRITE-current-symbol edge whose target is computed from the current
finite label. The original raw-entry/bootstrap and this table's complete
same-run correctness are the next obligations; no Full claim is asserted. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicCursorCode

open Turing PSTRTMSeq005 PSTRSymbolicPairedCursor PSTRSymbolicCarry
open PSTRSymbolicLaneScan PSTRSymbolicCounter PSTRSymbolicZeroTail
open PA17TMRatArithmeticParse002

inductive Label where
  | mark : Fin 80 → Label
  | scanLeft : Fin 56 → Label
  | six : Fin 160 → Label
  | rewind : Fin 48 → Label
  | borrow : Fin 136 → Label
  | one : Bool → Fin 160 → Label
  | scanRight : Bool → Fin 56 → Label
  | restore : Bool → Fin 128 → Label
  | halt : Bool → Label
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.mark 0⟩

def calledCode {states : Nat} {Target : Type}
    (machine : Machine states) (tag finish : Fin (states + 1) → Target)
    (label : Fin (states + 1)) (symbol : Bool) : Option (Target × TM0.Stmt Bool) :=
  match machine label symbol with
  | some (next, op) => some (tag next, op)
  | none => some (finish label, .write symbol)

def machine : TM0.Machine Bool Label := fun label symbol =>
  match label with
  | .mark q => calledCode markerSetupMachine .mark
      (fun current => .scanLeft (carryLabel (0 : Fin 7) (savedLabel (states := 9) current))) q symbol
  | .scanLeft q => calledCode (carryMachine (flagWalkMachine false)) .scanLeft
      (fun current => .six (carryLabel (13 : Fin 20) (savedLabel (states := 6) current))) q symbol
  | .six q => calledCode (carryMachine right19Machine) .six
      (fun current => .rewind (carryLabel (0 : Fin 6) (savedLabel (states := 19) current))) q symbol
  | .rewind q => calledCode (carryMachine fieldBackMachine) .rewind
      (fun current => .borrow (carryLabel (0 : Fin 17) (savedLabel (states := 5) current))) q symbol
  | .borrow q => calledCode (carryMachine counterRoundMachine) .borrow
      (fun current => .one (decide ((originalLabel (states := 16) current).val = 15))
        (carryLabel (18 : Fin 20) (savedLabel (states := 16) current))) q symbol
  | .one zero q => calledCode (carryMachine right19Machine) (.one zero)
      (fun current => .scanRight zero (carryLabel (0 : Fin 7) (savedLabel (states := 19) current))) q symbol
  | .scanRight zero q => calledCode (carryMachine (flagWalkMachine true)) (.scanRight zero)
      (fun current => .restore zero
        (restoreLabel 0 (savedTag current.val) (savedFirst current.val) (savedSecond current.val))) q symbol
  | .restore zero q => calledCode markerRestoreMachine (.restore zero) (fun _ => .halt zero) q symbol
  | .halt _ => none

def tagCfg {states : Nat} {Target : Type} (tag : Fin (states + 1) → Target)
    (cfg : MachineState states) : TM0.Cfg Bool Target := ⟨tag cfg.q,cfg.Tape⟩

def stepTape (op : TM0.Stmt Bool) (tape : Tape Bool) : Tape Bool :=
  match op with
  | .move direction => tape.move direction
  | .write bit => tape.write bit

theorem called_edge {states : Nat} {Target : Type} [Inhabited Target]
    (whole : TM0.Machine Bool Target) (callee : Machine states)
    (tag finish : Fin (states + 1) → Target)
    (code : ∀ q bit, whole (tag q) bit = calledCode callee tag finish q bit)
    (q next : Fin (states + 1)) (op : TM0.Stmt Bool) (tape : Tape Bool)
    (actual : callee q tape.head = some (next,op)) :
    TM0.step whole ⟨tag q,tape⟩ = some ⟨tag next,stepTape op tape⟩ := by
  cases op <;> simp only [TM0.step, code, calledCode, actual, Option.map_some, stepTape]

theorem called_return {states : Nat} {Target : Type} [Inhabited Target]
    (whole : TM0.Machine Bool Target) (callee : Machine states)
    (tag finish : Fin (states + 1) → Target)
    (code : ∀ q bit, whole (tag q) bit = calledCode callee tag finish q bit)
    (q : Fin (states + 1)) (tape : Tape Bool) (actual : callee q tape.head = none) :
    TM0.step whole ⟨tag q,tape⟩ = some ⟨finish q,tape⟩ := by
  simp [TM0.step, code, calledCode, actual]

theorem called_step_some {states : Nat} {Target : Type} [Inhabited Target]
    (whole : TM0.Machine Bool Target) (callee : Machine states)
    (tag finish : Fin (states + 1) → Target)
    (code : ∀ q bit, whole (tag q) bit = calledCode callee tag finish q bit)
    (before after : MachineState states) (actual : TM0.step callee before = some after) :
    TM0.step whole (tagCfg tag before) = some (tagCfg tag after) := by
  cases before with
  | mk q tape =>
    cases action : callee q tape.head with
    | none => simp [TM0.step, action] at actual
    | some pair =>
      obtain ⟨next,op⟩ := pair
      have endpoint : after = ⟨next,stepTape op tape⟩ := by
        cases op <;>
          simpa only [TM0.step, action, Option.map_some, Option.some.injEq, stepTape] using actual.symm
      subst after
      exact called_edge whole callee tag finish code q next op tape action

theorem called_step_none {states : Nat} {Target : Type} [Inhabited Target]
    (whole : TM0.Machine Bool Target) (callee : Machine states)
    (tag finish : Fin (states + 1) → Target)
    (code : ∀ q bit, whole (tag q) bit = calledCode callee tag finish q bit)
    (cfg : MachineState states) (actual : TM0.step callee cfg = none) :
    TM0.step whole (tagCfg tag cfg) = some ⟨finish cfg.q,cfg.Tape⟩ := by
  cases cfg with
  | mk q tape =>
    cases action : callee q tape.head with
    | none => exact called_return whole callee tag finish code q tape action
    | some pair => simp [TM0.step, action] at actual

theorem terminal (zero : Bool) (tape : Tape Bool) : TM0.step machine ⟨.halt zero,tape⟩ = none := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicCursorCode
