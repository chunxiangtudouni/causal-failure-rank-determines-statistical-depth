module
public import Common.PSTR_TM_RawNat_010

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPadInsert034
open PaperProofs.Common.Native.RationalControllerComputation

def embedRaw (q : Fin 17) : Fin 41 := ⟨q.val, by omega⟩
def liftRaw (old : MachineState 16) : MachineState 40 := ⟨embedRaw old.q, old.Tape⟩

/-- Restore actual00 padding after an A-empty alignment step. Rewind the
already-produced finite flagged prefix, copy it TWO cells left, then clear
the two old source cells immediately before the retained10 marker. The
whole prefix shifts left, so its relative left tape remains unchanged when
the actual head returns at the new00. No prefix length is supplied. -/
def padMachine : Machine 40 := fun q symbol =>
  if q.val = 0 then some (12, .move .left)
  else if q.val = 16 then some (17, .write symbol)
  else if h : q.val < 17 then
    (PSTRTMRawNat010.rawNatMachine ⟨q.val, h⟩ symbol).map
      (fun (next, statement) => (embedRaw next, statement))
  else
    match q.val with
    | 17 => some (if symbol then 19 else 18, .move .right)
    | 18 => if symbol then some (20, .move .left) else none
    | 19 => some (if symbol then 21 else 36, .move .left)
    | 20 => some (22, .move .left)
    | 21 => some (23, .move .left)
    | 22 => some (24, .move .left)
    | 23 => some (25, .move .left)
    | 24 => some (26, .write false)
    | 25 => some (27, .write true)
    | 26 => some (28, .move .right)
    | 27 => some (28, .move .right)
    | 28 => some (29, .write true)
    | 29 => some (30, .move .right)
    | 30 => some (31, .move .right)
    | 31 => some (17, .move .right)
    | 36 => some (37, .move .left)
    | 37 => some (38, .write false)
    | 38 => some (39, .move .left)
    | 39 => some (40, .write false)
    | _ => none

def state (q : Fin 41) (left right : List Bool) : MachineState 40 := ⟨q, Turing.Tape.mk₂ left right⟩

def flagMode (bit : Bool) : Fin 41 := if bit then 19 else 18
def backOne (bit : Bool) : Fin 41 := if bit then 21 else 20
def backTwo (bit : Bool) : Fin 41 := if bit then 23 else 22
def writeMode (bit : Bool) : Fin 41 := if bit then 25 else 24
def afterWrite (bit : Bool) : Fin 41 := if bit then 27 else 26

theorem pad_halt (left right : List Bool) :
    Turing.TM0.step padMachine (state 40 left right) = none := by
  simp [Turing.TM0.step, padMachine, state]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPadInsert034
