module
public import Common.PSTR_TM_MulPassTrace_081

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulHalfCode082
open PaperProofs.Common.Native.RationalControllerComputation

def control (higher seen : Bool) : Fin 4 :=
  ⟨2*higher.toNat+seen.toNat,by cases higher <;> cases seen <;> decide⟩
def higher (r : Fin 4) : Bool := decide (2 ≤ r.val)
def seen (r : Fin 4) : Bool := decide (r.val%2=1)
def nextControl (r : Fin 4) (oldBit : Bool) : Fin 4 := control oldBit (seen r || higher r)

def readB (r : Fin 4) : Fin 34 := ⟨2+r.val,by have h := r.isLt; omega⟩
def backward (phase : Fin 6) (r : Fin 4) : Fin 34 :=
  ⟨6+4*phase.val+r.val,by have hp := phase.isLt; have hr := r.isLt; omega⟩
def haltLabel (r : Fin 4) : Fin 34 := ⟨30+r.val,by have h := r.isLt; omega⟩

/-- ONE fixed34-label real multiplier-halving pass. Starting at real EOF,
it visits B from high to low, writes the carried higher B bit, preserves
every C/A/flag, and physically returns to the actual left false guard/start.
HALT control contains original B's LOW BIT and whether the NEW B is nonzero.
Those computed bits drive binary multiplication, not a supplied answer. -/
def halfMachine : Machine 33 := fun q symbol =>
  if h0 : q.val=0 then some (backward 5 (control false false),.move .left)
  else if h1 : q.val=1 then
    if symbol then some (readB (control false false),.move .left)
      else some (haltLabel (control false false),.move .right)
  else if h2 : q.val<6 then
    let r : Fin 4 := ⟨q.val-2,by omega⟩
    some (backward 0 (nextControl r symbol),.write (higher r))
  else if h3 : q.val<30 then
    let r : Fin 4 := ⟨(q.val-6)%4,Nat.mod_lt _ (by decide)⟩
    if q.val<26 then some (⟨q.val+4,by omega⟩,.move .left)
    else if symbol then some (readB r,.move .left) else some (haltLabel r,.move .right)
  else none

def state (q : Fin 34) (left right : List Bool) : MachineState 33 := ⟨q,Turing.Tape.mk₂ left right⟩

def resultReverse : Fin 4 → List PSTRTMMulPassCode079.Triple → List PSTRTMMulPassCode079.Triple
  | _,[] => []
  | r,(c,a,b)::earlier => (c,a,higher r)::resultReverse (nextControl r b) earlier
def finalControl : Fin 4 → List PSTRTMMulPassCode079.Triple → Fin 4
  | r,[] => r
  | r,(_,_,b)::earlier => finalControl (nextControl r b) earlier
def halfTriples (triples : List PSTRTMMulPassCode079.Triple) : List PSTRTMMulPassCode079.Triple :=
  (resultReverse (control false false) triples.reverse).reverse

theorem half_halt (r : Fin 4) (left right : List Bool) :
    Turing.TM0.step halfMachine (state (haltLabel r) left right)=none := by
  have hr := r.isLt
  simp [Turing.TM0.step,halfMachine,state,haltLabel,
    show 30+r.val≠1 by omega,
    show ¬30+r.val<6 by omega,show ¬30+r.val<30 by omega]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulHalfCode082
