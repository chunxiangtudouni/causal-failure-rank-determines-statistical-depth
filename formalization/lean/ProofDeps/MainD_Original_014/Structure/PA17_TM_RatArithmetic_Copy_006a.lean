module
public import Structure.PA17_TM_RatArithmetic_Unblock_004c

/-! A physical copy from the nearest parsed flagged field into actual blank
workspace to the right of the original footer. The source flags and footer
are temporarily marked and are all restored. No width is supplied to code. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCopy006

/-- Fixed43-label Bool TM0. 00 workspace terminators are physically written
initially and after each copied bit, not supplied as a caller answer. -/
def copyMachine : Machine 42 := fun q symbol =>
  match q.val with
  | 0 => some (1,.move .right)
  | 1 => some (2,.write false)
  | 2 => some (3,.move .right)
  | 3 => some (4,.write false)
  | 4 => some (5,.move .left)
  | 5 => some (6,.move .left)
  | 6 => some (7,.write false)
  | 7 => some (8,.move .left)
  | 8 => some (9,.move .left)
  | 9 => some (if symbol then 10 else 11,if symbol then .move .left else .move .right)
  | 10 => some (9,.move .left)
  | 11 => some (if symbol then 13 else 12,.move .right)
  | 12 => some (if symbol then 14 else 42,if symbol then .write false else .write true)
  | 13 => some (if symbol then 15 else 42,if symbol then .write false else .write true)
  | 14 => some (16,.move .right)
  | 15 => some (17,.move .right)
  | 16 => some (18,.move .right)
  | 17 => some (19,.move .right)
  | 18 => some (if symbol then 16 else 20,.move .right)
  | 19 => some (if symbol then 17 else 21,.move .right)
  | 20 => some (22,.move .right)
  | 21 => some (23,.move .right)
  | 22 => some (if symbol then 20 else 24,if symbol then .move .right else .move .left)
  | 23 => some (if symbol then 21 else 25,if symbol then .move .right else .move .left)
  | 24 => some (26,.write false)
  | 25 => some (26,.write true)
  | 26 => some (27,.move .right)
  | 27 => some (28,.write true)
  | 28 => some (29,.move .right)
  | 29 => some (30,.write false)
  | 30 => some (31,.move .right)
  | 31 => some (32,.write false)
  | 32 => some (33,.move .left)
  | 33 => some (34,.move .left)
  | 34 => some (35,.move .left)
  | 35 => some (36,.move .left)
  | 36 => some (if symbol then 37 else 38,.move .left)
  | 37 => some (36,.move .left)
  | 38 => some (39,.move .left)
  | 39 => some (if symbol then 40 else 41,if symbol then .move .left else .write true)
  | 40 => some (39,.move .left)
  | 41 => some (11,.move .right)
  | _ => none

def state (q : Fin 43) (left right : List Bool) : MachineState 42 :=
  ⟨q,Turing.Tape.mk₂ left right⟩

def outData (bit : Bool) : Fin 43 := if bit then 17 else 16
def outFlag (bit : Bool) : Fin 43 := if bit then 19 else 18
def workData (bit : Bool) : Fin 43 := if bit then 21 else 20
def workFlag (bit : Bool) : Fin 43 := if bit then 23 else 22
def writeData (bit : Bool) : Fin 43 := if bit then 25 else 24
def saveFlag (bit : Bool) : Fin 43 := if bit then 13 else 12
def leaveFlag (bit : Bool) : Fin 43 := if bit then 15 else 14

theorem chain_append (xs ys : List (MachineState 42)) (last first : MachineState 42)
    (hx : xs.IsChain (fun a b => Turing.TM0.step copyMachine a = some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step copyMachine a = some b))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (hs : Turing.TM0.step copyMachine last = some first) :
    (xs ++ ys).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

theorem copy_halt (left right : List Bool) :
    Turing.TM0.step copyMachine (state 42 left right) = none := by
  simp [Turing.TM0.step,copyMachine,state]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCopy006
