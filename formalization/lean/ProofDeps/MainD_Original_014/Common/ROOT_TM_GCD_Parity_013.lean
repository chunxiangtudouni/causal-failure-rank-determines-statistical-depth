module
public import Common.ROOT_TM_GCD_CounterTrace_012

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDParity013
open PaperProofs.Common.Native.RationalControllerComputation
local notation "cols" => PSTRTMBinaryAdd024.operandColumns

def control (a b : Bool) : Fin 4 := ⟨2*a.toNat+b.toNat,by cases a <;> cases b <;> decide⟩
def flagA (a : Bool) : Fin 13 := ⟨1+a.toNat,by have h:=Bool.toNat_le a; omega⟩
def readB (a : Bool) : Fin 13 := ⟨3+a.toNat,by have h:=Bool.toNat_le a; omega⟩
def backward (r : Fin 4) : Fin 13 := ⟨5+r.val,by omega⟩
def haltLabel (r : Fin 4) : Fin 13 := ⟨9+r.val,by omega⟩
def parityMachine : Machine 12 := fun q bit =>
  if q.val=0 then some (flagA bit,.move .right)
  else if q.val<3 then
    if bit then some (readB (decide (q.val=2)),.move .right) else some (9,.move .left)
  else if q.val<5 then some (backward (control (decide (q.val=4)) bit),.move .left)
  else if _h : q.val<9 then some (haltLabel ⟨q.val-5,by omega⟩,.move .left)
  else none
def state (q : Fin 13) (left right : List Bool) : MachineState 12 := ⟨q,Turing.Tape.mk₂ left right⟩

def pairTrace (a b : Bool) (left right : List Bool) : List (MachineState 12) :=
  [state 0 left (a::true::b::true::right),
    state (flagA a) (a::left) (true::b::true::right),
    state (readB a) (true::a::left) (b::true::right),
    state (backward (control a b)) (a::left) (true::b::true::right),
    state (haltLabel (control a b)) left (a::true::b::true::right)]
theorem pair_chain (a b : Bool) (left right : List Bool) :
    (pairTrace a b left right).IsChain (fun x y => Turing.TM0.step parityMachine x=some y) := by
  cases a <;> cases b <;> simp [pairTrace,List.isChain_cons_cons,Turing.TM0.step,
    parityMachine,state,flagA,readB,backward,haltLabel,control,Turing.Tape.mk₂]
theorem parity_halt (r : Fin 4) (left right : List Bool) :
    Turing.TM0.step parityMachine (state (haltLabel r) left right)=none := by
  have hr:=r.isLt
  simp [Turing.TM0.step,parityMachine,state,haltLabel,
    show ¬9+r.val<3 by omega,show ¬9+r.val<5 by omega,show ¬9+r.val<9 by omega]
theorem pair_runsFrom (a b : Bool) (left right : List Bool) :
    PSTRTMSeq005.RunsFrom parityMachine (state 0 left (a::true::b::true::right))
      (pairTrace a b left right) (state (haltLabel (control a b)) left (a::true::b::true::right)) :=
  ⟨rfl,pair_chain a b left right,rfl,parity_halt _ _ _⟩

theorem actual_parity (a b : Bool) (later : List (Bool × Bool)) :
    a=(PSTRTMBinaryAdd024.firstValue ((a,b)::later)).testBit 0 ∧
    b=(PSTRTMBinaryAdd024.secondValue ((a,b)::later)).testBit 0 := by
  change a=(Nat.bit a (PSTRTMBinaryAdd024.firstValue later)).testBit 0 ∧
    b=(Nat.bit b (PSTRTMBinaryAdd024.secondValue later)).testBit 0
  cases a <;> cases b <;> simp [Nat.testBit_zero,Nat.bit]

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDParity013
