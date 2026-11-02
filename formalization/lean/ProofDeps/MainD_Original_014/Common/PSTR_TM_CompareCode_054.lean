module
public import Common.PSTR_TM_AddRun_026

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCompareCode054
open PaperProofs.Common.Native.RationalControllerComputation

/-- Fixed finite control:0 equal,1 less,2 greater. Each new higher binary
digit overrides earlier lower digits only when the actual digit pair differs. -/
def update (relation : Fin 3) (a b : Bool) : Fin 3 :=
  if a = b then relation else if a then 2 else 1

def aState (relation : Fin 3) : Fin 21 := ⟨relation.val, by omega⟩
def flagA (relation : Fin 3) (a : Bool) : Fin 21 :=
  ⟨3 + 2 * relation.val + a.toNat, by have hr := relation.isLt; have ha := Bool.toNat_le a; omega⟩
def readB (relation : Fin 3) (a : Bool) : Fin 21 :=
  ⟨9 + 2 * relation.val + a.toNat, by have hr := relation.isLt; have ha := Bool.toNat_le a; omega⟩
def flagB (relation : Fin 3) : Fin 21 := ⟨15 + relation.val, by omega⟩
def haltLabel (relation : Fin 3) : Fin 21 := ⟨18 + relation.val, by omega⟩

/-- Actual21-label NONDESTRUCTIVE comparison kernel. The initial label0
means equal. Only four real read/move steps per column; actual owned00 ends
the scan. Result is computed in finite HALT control, not supplied as input. -/
def compareMachine : Machine 20 := fun q symbol =>
  if h0 : q.val < 3 then
    some (flagA ⟨q.val, h0⟩ symbol, .move .right)
  else if h1 : q.val < 9 then
    let relation : Fin 3 := ⟨(q.val - 3) / 2, by omega⟩
    let a := decide (q.val % 2 = 0)
    if symbol then some (readB relation a, .move .right) else some (haltLabel relation, .move .left)
  else if h2 : q.val < 15 then
    let relation : Fin 3 := ⟨(q.val - 9) / 2, by omega⟩
    let a := decide (q.val % 2 = 0)
    some (flagB (update relation a symbol), .move .right)
  else if h3 : q.val < 18 then
    if symbol then some (aState ⟨q.val - 15, by omega⟩, .move .right) else none
  else none

def state (q : Fin 21) (left right : List Bool) : MachineState 20 := ⟨q, Turing.Tape.mk₂ left right⟩
def leftColumns (previous : List (Bool × Bool)) : List Bool :=
  previous.flatMap (fun pair => [true,pair.2,true,pair.1])

def resultRelation (relation : Fin 3) (pairs : List (Bool × Bool)) : Fin 3 :=
  pairs.foldl (fun old pair => update old pair.1 pair.2) relation

theorem resultRelation_nil (relation : Fin 3) : resultRelation relation [] = relation := rfl
theorem resultRelation_cons (relation : Fin 3) (a b : Bool) (later : List (Bool × Bool)) :
    resultRelation relation ((a,b) :: later) = resultRelation (update relation a b) later := rfl

theorem compare_halt (relation : Fin 3) (left right : List Bool) :
    Turing.TM0.step compareMachine (state (haltLabel relation) left right) = none := by
  have hr := relation.isLt
  simp [Turing.TM0.step, compareMachine, state, haltLabel, show ¬18 + relation.val < 3 by omega,
    show ¬18 + relation.val < 9 by omega, show ¬18 + relation.val < 15 by omega,
    show ¬18 + relation.val < 18 by omega]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCompareCode054
