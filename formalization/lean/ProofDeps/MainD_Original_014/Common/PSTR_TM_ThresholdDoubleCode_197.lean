module
public import Common.PSTR_TM_PairRewind_105
public import Common.PSTR_TM_Canonical_020

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDoubleCode197
open PaperProofs.Common.Native.RationalControllerComputation

/-- The actual finite shift used twice to form4*(B+1). One carried
bit lives in finite control; the operand itself stays on the Bool tape.
The right side must really be blank. No runtime length or fuel is read.
The old061 double allocates on the left; here both left guard cells
protect the archived B, so this concrete consumer grows on the right. -/
def scanMachine : Machine 19 := fun q symbol =>
  match q.val with
  | 0 => some (if symbol then 3 else 2,.move .right)
  | 1 => some (if symbol then 5 else 4,.move .right)
  | 2 => some (if symbol then 6 else 14,.move .left)
  | 3 => some (if symbol then 7 else 14,.move .left)
  | 4 => some (if symbol then 8 else 15,.move .left)
  | 5 => some (if symbol then 9 else 15,.move .left)
  | 6 => some (10,.write false)
  | 7 => some (11,.write false)
  | 8 => some (10,.write true)
  | 9 => some (11,.write true)
  | 10 => some (12,.move .right)
  | 11 => some (13,.move .right)
  | 12 => some (0,.move .right)
  | 13 => some (1,.move .right)
  | 14 => some (16,.write false)
  | 15 => some (16,.write true)
  | 16 => some (17,.move .right)
  | 17 => some (18,.write true)
  | 18 => some (19,.move .right)
  | _ => none

def state (q : Fin 20) (left right : List Bool) : MachineState 19 :=
  ⟨q,Turing.Tape.mk₂ left right⟩

def readLabel (carry : Bool) : Fin 20 := if carry then 1 else 0
def flagLabel (carry bit : Bool) : Fin 20 :=
  if carry then (if bit then 5 else 4) else (if bit then 3 else 2)
def writeLabel (carry bit : Bool) : Fin 20 :=
  if carry then (if bit then 9 else 8) else (if bit then 7 else 6)
def firstMove (bit : Bool) : Fin 20 := if bit then 11 else 10
def secondMove (bit : Bool) : Fin 20 := if bit then 13 else 12
def endWrite (carry : Bool) : Fin 20 := if carry then 15 else 14

def unitTrace (carry bit : Bool) (left right : List Bool) : List (MachineState 19) :=
  [state (readLabel carry) left (bit::true::right),
   state (flagLabel carry bit) (bit::left) (true::right),
   state (writeLabel carry bit) left (bit::true::right),
   state (firstMove bit) left (carry::true::right),
   state (secondMove bit) (carry::left) (true::right)]

theorem unit_head (carry bit : Bool) (left right : List Bool) :
    (unitTrace carry bit left right).head? =
      some (state (readLabel carry) left (bit::true::right)) := rfl

theorem unit_last (carry bit : Bool) (left right : List Bool) :
    (unitTrace carry bit left right).getLast? =
      some (state (secondMove bit) (carry::left) (true::right)) := rfl

theorem unit_chain (carry bit : Bool) (left right : List Bool) :
    (unitTrace carry bit left right).IsChain (fun a b => Turing.TM0.step scanMachine a = some b) := by
  cases carry <;> cases bit <;>
    simp [unitTrace,List.isChain_cons_cons,Turing.TM0.step,scanMachine,state,
      readLabel,flagLabel,writeLabel,firstMove,secondMove,Turing.Tape.mk₂]

theorem unit_advance (carry bit : Bool) (left right : List Bool) :
    Turing.TM0.step scanMachine (state (secondMove bit) (carry::left) (true::right)) =
      some (state (readLabel bit) (true::carry::left) right) := by
  cases bit <;> simp [Turing.TM0.step,scanMachine,state,secondMove,readLabel,Turing.Tape.mk₂]

def endTrace (carry : Bool) (left : List Bool) : List (MachineState 19) :=
  [state (readLabel carry) left [false,false],
   state (flagLabel carry false) (false::left) [false],
   state (endWrite carry) left [false,false],
   state 16 left [carry,false],
   state 17 (carry::left) [false],
   state 18 (carry::left) [true],
   state 19 (true::carry::left) []]

theorem end_head (carry : Bool) (left : List Bool) :
    (endTrace carry left).head? = some (state (readLabel carry) left [false,false]) := rfl

theorem end_last (carry : Bool) (left : List Bool) :
    (endTrace carry left).getLast? = some (state 19 (true::carry::left) []) := rfl

theorem end_chain (carry : Bool) (left : List Bool) :
    (endTrace carry left).IsChain (fun a b => Turing.TM0.step scanMachine a = some b) := by
  cases carry <;> simp [endTrace,List.isChain_cons_cons,Turing.TM0.step,
    scanMachine,state,readLabel,flagLabel,endWrite,Turing.Tape.mk₂]

theorem scan_halt (left right : List Bool) :
    Turing.TM0.step scanMachine (state 19 left right) = none := by
  simp [Turing.TM0.step,scanMachine,state]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDoubleCode197
