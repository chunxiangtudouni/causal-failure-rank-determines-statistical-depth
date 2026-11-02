module
public import Common.PSTR_TM_BinaryAdd_024

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulPassCode079
open PaperProofs.Common.Native.RationalControllerComputation

abbrev Triple := Bool × Bool × Bool

/-- Actual resident schoolbook-multiplication cells: accumulator C,
shifted multiplicand A, remaining multiplier B, each with its TRUE flag. -/
def columns (triples : List Triple) : List Bool := triples.flatMap (fun (c,a,b) => [c,true,a,true,b,true])
def leftColumns (triples : List Triple) : List Bool := triples.flatMap (fun (c,a,b) => [true,b,true,a,true,c])
def cValue (triples : List Triple) : Nat := PSTRTMIncrement009.valueDigits (triples.map (fun (c,_,_) => c))
def aValue (triples : List Triple) : Nat := PSTRTMIncrement009.valueDigits (triples.map (fun (_,a,_) => a))
def bValue (triples : List Triple) : Nat := PSTRTMIncrement009.valueDigits (triples.map (fun (_,_,b) => b))

/-- All registers are finite control bits. In the multiplication caller,
mode comes from reading B's ACTUAL low digit, not an answer/input promise. -/
def control (mode carryA carryC : Bool) : Fin 8 :=
  ⟨4*mode.toNat+2*carryA.toNat+carryC.toNat, by cases mode <;> cases carryA <;> cases carryC <;> decide⟩
def mode (r : Fin 8) : Bool := decide (4 ≤ r.val)
def aCarry (r : Fin 8) : Bool := decide (2 ≤ r.val%4)
def cCarry (r : Fin 8) : Bool := decide (r.val%2=1)
def hold (mode nextA nextC oldA : Bool) : Fin 16 :=
  ⟨8*mode.toNat+4*nextA.toNat+2*nextC.toNat+oldA.toNat,
    by cases mode <;> cases nextA <;> cases nextC <;> cases oldA <;> decide⟩

def sumOutput (r : Fin 8) (c a : Bool) : Bool := PSTRTMBinaryAdd024.sumBit (cCarry r) c (a && mode r)
def nextControl (r : Fin 8) (c a : Bool) : Fin 8 :=
  control (mode r) a (PSTRTMBinaryAdd024.carryBit (cCarry r) c (a && mode r))
def nextHold (r : Fin 8) (c a : Bool) : Fin 16 :=
  hold (mode r) a (PSTRTMBinaryAdd024.carryBit (cCarry r) c (a && mode r)) (aCarry r)

def cState (r : Fin 8) : Fin 192 := ⟨r.val, by have h := r.isLt; omega⟩
def flagC (r : Fin 8) (c : Bool) : Fin 192 :=
  ⟨8+2*r.val+c.toNat, by have h := r.isLt; have hc := Bool.toNat_le c; omega⟩
def readA (r : Fin 8) (c : Bool) : Fin 192 :=
  ⟨24+2*r.val+c.toNat, by have h := r.isLt; have hc := Bool.toNat_le c; omega⟩
def backFlag (r : Fin 8) (c a : Bool) : Fin 192 :=
  ⟨40+4*r.val+2*c.toNat+a.toNat, by have h := r.isLt; have hc := Bool.toNat_le c; have ha := Bool.toNat_le a; omega⟩
def writeC (r : Fin 8) (c a : Bool) : Fin 192 :=
  ⟨72+4*r.val+2*c.toNat+a.toNat, by have h := r.isLt; have hc := Bool.toNat_le c; have ha := Bool.toNat_le a; omega⟩
def towardA (phase : Fin 3) (saved : Fin 16) : Fin 192 :=
  ⟨104+16*phase.val+saved.val, by have hp := phase.isLt; have hs := saved.isLt; omega⟩
def advance (phase : Fin 4) (r : Fin 8) : Fin 192 :=
  ⟨152+8*phase.val+r.val, by have hp := phase.isLt; have hr := r.isLt; omega⟩
def haltLabel (r : Fin 8) : Fin 192 := ⟨184+r.val, by have h := r.isLt; omega⟩

/-- ONE fixed192-label Bool pass used by binary multiplication. It really
reads C/A, writes C+mode*A with carry, writes the shifted A digit, preserves
all B bits/flags, and reaches real OWN00. BOTH overflow bits remain computed
in finite HALT control; no truncation/absence of overflow is assumed. -/
def passMachine : Machine 191 := fun q symbol =>
  if h0 : q.val < 8 then some (flagC ⟨q.val,h0⟩ symbol,.move .right)
  else if h1 : q.val < 24 then
    let r : Fin 8 := ⟨(q.val-8)/2,by omega⟩
    let c := decide (q.val%2=1)
    if symbol then some (readA r c,.move .right) else some (haltLabel r,.move .left)
  else if h2 : q.val < 40 then
    let r : Fin 8 := ⟨(q.val-24)/2,by omega⟩
    let c := decide (q.val%2=1)
    some (backFlag r c symbol,.move .left)
  else if h3 : q.val < 72 then some (⟨q.val+32,by omega⟩,.move .left)
  else if h4 : q.val < 104 then
    let r : Fin 8 := ⟨(q.val-72)/4,by omega⟩
    let c := decide (2 ≤ (q.val-72)%4)
    let a := decide (q.val%2=1)
    some (towardA 0 (nextHold r c a),.write (sumOutput r c a))
  else if h5 : q.val < 120 then some (⟨q.val+16,by omega⟩,.move .right)
  else if h6 : q.val < 136 then some (⟨q.val+16,by omega⟩,.move .right)
  else if h7 : q.val < 152 then
    let r : Fin 8 := ⟨(q.val-136)/2,by omega⟩
    some (advance 0 r,.write (decide (q.val%2=1)))
  else if h8 : q.val < 184 then
    let r : Fin 8 := ⟨(q.val-152)%8,Nat.mod_lt _ (by decide)⟩
    if q.val < 176 then some (⟨q.val+8,by omega⟩,.move .right) else some (cState r,.move .right)
  else none

def state (q : Fin 192) (left right : List Bool) : MachineState 191 := ⟨q,Turing.Tape.mk₂ left right⟩

def resultTriples : Fin 8 → List Triple → List Triple
  | _,[] => []
  | r,(c,a,b)::later => (sumOutput r c a,aCarry r,b)::resultTriples (nextControl r c a) later
def finalControl : Fin 8 → List Triple → Fin 8
  | r,[] => r
  | r,(c,a,_)::later => finalControl (nextControl r c a) later

theorem pass_halt (r : Fin 8) (left right : List Bool) :
    Turing.TM0.step passMachine (state (haltLabel r) left right) = none := by
  have hr := r.isLt
  simp [Turing.TM0.step,passMachine,state,haltLabel,
    show ¬184+r.val<8 by omega,show ¬184+r.val<24 by omega,show ¬184+r.val<40 by omega,
    show ¬184+r.val<72 by omega,show ¬184+r.val<104 by omega,show ¬184+r.val<120 by omega,
    show ¬184+r.val<136 by omega,show ¬184+r.val<152 by omega,show ¬184+r.val<184 by omega]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulPassCode079
