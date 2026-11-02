module
public import Common.PSTR_TM_TwoRawOperands_029

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMAlignCode030
open PaperProofs.Common.Native.RationalControllerComputation

def hole (phase : Fin 3) (bit : Bool) : Fin 135 :=
  ⟨10 + 2 * phase.val + bit.toNat, by have h := phase.isLt; have hb := Bool.toNat_le bit; omega⟩
def previousFlag (phase : Fin 3) (bit : Bool) : Fin 135 :=
  ⟨16 + 2 * phase.val + bit.toNat, by have h := phase.isLt; have hb := Bool.toNat_le bit; omega⟩
def readPrevious (phase : Fin 3) (bit flag : Bool) : Fin 135 :=
  ⟨24 + 4 * phase.val + 2 * bit.toNat + flag.toNat, by
    have h := phase.isLt; have hb := Bool.toNat_le bit; have hf := Bool.toNat_le flag; omega⟩
def moveToHole (phase : Fin 3) (bit flag data : Bool) : Fin 135 :=
  ⟨36 + 8 * phase.val + 4 * bit.toNat + 2 * flag.toNat + data.toNat, by
    have h := phase.isLt; have hb := Bool.toNat_le bit; have hf := Bool.toNat_le flag
    have hd := Bool.toNat_le data; omega⟩
def writePrevious (phase : Fin 3) (bit flag data : Bool) : Fin 135 :=
  ⟨60 + 8 * phase.val + 4 * bit.toNat + 2 * flag.toNat + data.toNat, by
    have h := phase.isLt; have hb := Bool.toNat_le bit; have hf := Bool.toNat_le flag
    have hd := Bool.toNat_le data; omega⟩
def moveToFlag (phase : Fin 3) (bit flag : Bool) : Fin 135 :=
  ⟨84 + 4 * phase.val + 2 * bit.toNat + flag.toNat, by
    have h := phase.isLt; have hb := Bool.toNat_le bit; have hf := Bool.toNat_le flag; omega⟩
def writePreviousFlag (phase : Fin 3) (bit flag : Bool) : Fin 135 :=
  ⟨96 + 4 * phase.val + 2 * bit.toNat + flag.toNat, by
    have h := phase.isLt; have hb := Bool.toNat_le bit; have hf := Bool.toNat_le flag; omega⟩
def backFirst (phase : Fin 3) (bit : Bool) : Fin 135 :=
  ⟨108 + 2 * phase.val + bit.toNat, by have h := phase.isLt; have hb := Bool.toNat_le bit; omega⟩
def backSecond (phase : Fin 3) (bit : Bool) : Fin 135 :=
  ⟨114 + 2 * phase.val + bit.toNat, by have h := phase.isLt; have hb := Bool.toNat_le bit; omega⟩
def backThird (phase : Fin 3) (bit : Bool) : Fin 135 :=
  ⟨120 + 2 * phase.val + bit.toNat, by have h := phase.isLt; have hb := Bool.toNat_le bit; omega⟩
def nextPhase (phase : Fin 3) : Fin 3 := ⟨phase.val - 1, by have h := phase.isLt; omega⟩
def checkB (bit : Bool) : Fin 135 := ⟨8 + bit.toNat, by cases bit <;> decide⟩
def restoreAFlag (bit : Bool) : Fin 135 := ⟨22 + bit.toNat, by cases bit <;> decide⟩
def fillB (bit : Bool) : Fin 135 := ⟨126 + bit.toNat, by cases bit <;> decide⟩
def moveBFlag (bit : Bool) : Fin 135 := ⟨128 + bit.toNat, by cases bit <;> decide⟩
def fillBFlag (bit : Bool) : Fin 135 := ⟨130 + bit.toNat, by cases bit <;> decide⟩
def finishColumn (bit : Bool) : Fin 135 := ⟨132 + bit.toNat, by cases bit <;> decide⟩

/-- Actual alignment of ONE pair of operand digits. The real A flag is
marked on tape; B's actual digit is held in one finite Boolean control bit.
The phase counter is a FIXED three-state control for the two separator pairs,
not a runtime width/value/cost input. Every earlier A pair is shifted right
into the hole until the actual marked A flag is read. -/
def alignMachine : Machine 134 := fun q symbol =>
  if q.val < 8 then
    match q.val with
    | 0 => some (1, .move .right)
    | 1 => some (2, .write false)
    | 2 => some (3, .move .right)
    | 3 => some (4, .move .right)
    | 4 => some (if symbol then 3 else 5, .move .right)
    | 5 => some (6, .move .right)
    | 6 => some (7, .move .right)
    | _ => some (⟨8 + symbol.toNat, by cases symbol <;> decide⟩, .move .right)
  else if q.val < 10 then
    if symbol then some (⟨14 + q.val % 2, by omega⟩, .move .left) else none
  else if h2 : q.val < 16 then
    some (⟨q.val + 6, by omega⟩, .move .left)
  else if h3 : q.val < 22 then
    if q.val < 18 ∧ symbol = false then
      some (⟨22 + q.val % 2, by omega⟩, .write true)
    else some (⟨24 + 4 * ((q.val - 16) / 2) + 2 * (q.val % 2) + symbol.toNat, by
      have hs := Bool.toNat_le symbol; omega⟩, .move .left)
  else if h4 : q.val < 24 then
    some (⟨q.val + 104, by omega⟩, .move .right)
  else if h5 : q.val < 36 then
    some (⟨36 + 2 * (q.val - 24) + symbol.toNat, by have hs := Bool.toNat_le symbol; omega⟩, .move .right)
  else if h6 : q.val < 60 then
    some (⟨q.val + 24, by omega⟩, .move .right)
  else if q.val < 84 then
    some (⟨84 + (q.val - 60) / 2, by omega⟩, .write (decide (q.val % 2 = 1)))
  else if h8 : q.val < 96 then
    some (⟨q.val + 12, by omega⟩, .move .right)
  else if q.val < 108 then
    some (⟨108 + ((q.val - 96) / 2) % 2 + 2 * ((q.val - 96) / 4 - 1), by omega⟩,
      .write (decide (q.val % 2 = 1)))
  else if h10 : q.val < 114 then
    some (⟨q.val + 6, by omega⟩, .move .left)
  else if h11 : q.val < 120 then
    some (⟨q.val + 6, by omega⟩, .move .left)
  else if q.val < 126 then
    some (⟨q.val - 110, by omega⟩, .move .left)
  else if h13 : q.val < 128 then
    some (⟨q.val + 2, by omega⟩, .write (decide (q.val % 2 = 1)))
  else if h14 : q.val < 130 then
    some (⟨q.val + 2, by omega⟩, .move .right)
  else if h15 : q.val < 132 then
    some (⟨q.val + 2, by omega⟩, .write true)
  else if q.val < 134 then
    some (134, .move .right)
  else none

def state (q : Fin 135) (left right : List Bool) : MachineState 134 := ⟨q, Turing.Tape.mk₂ left right⟩

theorem align_halt (left right : List Bool) :
    Turing.TM0.step alignMachine (state 134 left right) = none := by
  simp [Turing.TM0.step, alignMachine, state]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMAlignCode030
