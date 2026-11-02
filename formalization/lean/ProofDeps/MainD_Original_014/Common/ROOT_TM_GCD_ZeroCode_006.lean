module
public import Common.ROOT_TM_GCD_MapTrace_005
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDZero006
open PaperProofs.Common.Native.RationalControllerComputation

def control (a b : Bool) : Fin 4 :=
  ⟨2*a.toNat+b.toNat, by cases a <;> cases b <;> decide⟩
def seenA (r : Fin 4) : Bool := decide (2 ≤ r.val)
def seenB (r : Fin 4) : Bool := decide (r.val%2=1)
def update (r : Fin 4) (a b : Bool) : Fin 4 := control (seenA r || a) (seenB r || b)
def aState (r : Fin 4) : Fin 28 := ⟨r.val,by omega⟩
def flagA (r : Fin 4) (a : Bool) : Fin 28 :=
  ⟨4+2*r.val+a.toNat,by have h:=r.isLt; have ha:=Bool.toNat_le a; omega⟩
def readB (r : Fin 4) (a : Bool) : Fin 28 :=
  ⟨12+2*r.val+a.toNat,by have h:=r.isLt; have ha:=Bool.toNat_le a; omega⟩
def flagB (r : Fin 4) : Fin 28 := ⟨20+r.val,by omega⟩
def haltLabel (r : Fin 4) : Fin 28 := ⟨24+r.val,by omega⟩

/-- Fixed finite-control scan computes both nonzero bits from the actual
resident columns. It changes no tape cell and preserves arbitrary frames.
No zero certificate, operand value, width, fuel or output is an input. -/
def zeroMachine : Machine 27 := fun q symbol =>
  if h0 : q.val<4 then some (flagA ⟨q.val,h0⟩ symbol,.move .right)
  else if _h1 : q.val<12 then
    let r : Fin 4 := ⟨(q.val-4)/2,by omega⟩
    let a := decide (q.val%2=1)
    if symbol then some (readB r a,.move .right) else some (haltLabel r,.move .left)
  else if _h2 : q.val<20 then
    let r : Fin 4 := ⟨(q.val-12)/2,by omega⟩
    let a := decide (q.val%2=1)
    some (flagB (update r a symbol),.move .right)
  else if _h3 : q.val<24 then
    if symbol then some (aState ⟨q.val-20,by omega⟩,.move .right) else none
  else none

def state (q : Fin 28) (left right : List Bool) : MachineState 27 := ⟨q,Turing.Tape.mk₂ left right⟩
abbrev leftColumns := PSTRTMCompareCode054.leftColumns
def resultControl (r : Fin 4) (pairs : List (Bool × Bool)) : Fin 4 :=
  pairs.foldl (fun old pair => update old pair.1 pair.2) r
theorem resultControl_nil (r : Fin 4) : resultControl r []=r := rfl
theorem resultControl_cons (r : Fin 4) (a b : Bool) (later : List (Bool × Bool)) :
    resultControl r ((a,b)::later)=resultControl (update r a b) later := rfl
theorem zero_halt (r : Fin 4) (left right : List Bool) :
    Turing.TM0.step zeroMachine (state (haltLabel r) left right)=none := by
  have hr:=r.isLt
  simp [Turing.TM0.step,zeroMachine,state,haltLabel,
    show ¬24+r.val<4 by omega,show ¬24+r.val<12 by omega,
    show ¬24+r.val<20 by omega,show ¬24+r.val<24 by omega]
end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDZero006
