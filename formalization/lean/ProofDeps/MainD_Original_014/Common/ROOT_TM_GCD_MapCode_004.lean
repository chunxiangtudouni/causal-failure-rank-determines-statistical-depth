module
public import Common.ROOT_TM_GCD_HalfTrace_003

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDMap004
open PaperProofs.Common.Native.RationalControllerComputation

abbrev Pair := Bool × Bool
def flagA (a : Bool) : Fin 31 := ⟨1 + a.toNat, by have h := Bool.toNat_le a; omega⟩
def readB (a : Bool) : Fin 31 := ⟨3 + a.toNat, by have h := Bool.toNat_le a; omega⟩
def pairLabel (phase : Fin 6) (a b : Bool) : Fin 31 :=
  ⟨5 + 4 * phase.val + 2 * a.toNat + b.toNat, by
    have hp := phase.isLt; have ha := Bool.toNat_le a; have hb := Bool.toNat_le b; omega⟩

/-- A genuine finite truth-table transducer. The map is chosen with the
machine, before any operand; later GCD instantiations use only swap and
OR/clear. It reads each A/B, really writes both mapped data bits, and retains
every flag and all archive/tail cells. No host map is an executed operation. -/
def mapScanMachine (f : Pair → Pair) : Machine 30 := fun q symbol =>
  if _h0 : q.val = 0 then some (flagA symbol, .move .right)
  else if _h1 : q.val < 3 then
    let a := decide (q.val = 2)
    if symbol then some (readB a, .move .right) else some (30, .move .left)
  else if _h2 : q.val < 5 then
    some (pairLabel 0 (decide (q.val = 4)) symbol, .move .left)
  else if _h3 : q.val < 29 then
    let offset := (q.val - 5) % 4
    let a := decide (2 ≤ offset)
    let b := decide (offset % 2 = 1)
    match (q.val - 5) / 4 with
    | 0 => some (pairLabel 1 a b, .move .left)
    | 1 => some (pairLabel 2 a b, .write (f (a,b)).1)
    | 2 => some (pairLabel 3 a b, .move .right)
    | 3 => some (pairLabel 4 a b, .move .right)
    | 4 => some (pairLabel 5 a b, .write (f (a,b)).2)
    | _ => some (29, .move .right)
  else if q.val = 29 then some (0, .move .right)
  else none

def mapState (q : Fin 31) (left right : List Bool) : MachineState 30 :=
  ⟨q, Turing.Tape.mk₂ left right⟩

theorem map_halt (f : Pair → Pair) (left right : List Bool) :
    Turing.TM0.step (mapScanMachine f) (mapState 30 left right) = none := by
  simp [Turing.TM0.step, mapScanMachine, mapState]

def swapPair (p : Pair) : Pair := (p.2,p.1)
def outputPair (p : Pair) : Pair := (p.1 || p.2,false)

theorem firstValue_swap (pairs : List Pair) :
    PSTRTMBinaryAdd024.firstValue (pairs.map swapPair) = PSTRTMBinaryAdd024.secondValue pairs := by
  simp only [PSTRTMBinaryAdd024.firstValue, PSTRTMBinaryAdd024.secondValue, List.map_map]
  rfl

theorem secondValue_swap (pairs : List Pair) :
    PSTRTMBinaryAdd024.secondValue (pairs.map swapPair) = PSTRTMBinaryAdd024.firstValue pairs := by
  simp only [PSTRTMBinaryAdd024.firstValue, PSTRTMBinaryAdd024.secondValue, List.map_map]
  rfl

theorem secondValue_output (pairs : List Pair) :
    PSTRTMBinaryAdd024.secondValue (pairs.map outputPair) = 0 := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
    obtain ⟨a,b⟩ := pair
    change Nat.bit false (PSTRTMBinaryAdd024.secondValue (pairs.map outputPair)) = 0
    rw [ih]
    rfl

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDMap004
