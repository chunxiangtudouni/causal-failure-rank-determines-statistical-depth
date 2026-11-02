module

public import Paid.PDROC_BitVM_Common_IO_Output_Decode_002
public import Paid.PDROC_BitVM_Common_IO_Wide_Runtime_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Output

open Turing

def pairBits (pairs : List (Bool × Bool)) : List Bool :=
  pairs.flatMap (fun pair => [pair.1, pair.2])

def pairFound (pairs : List (Bool × Bool)) : Bool := pairs.any Prod.fst

def seenStore (saved : Store) (seen : Bool) : Store := { saved with seen := saved.seen || seen }

/-- Proof-only whole-tape summary of the actual two RIGHT moves per
presence/value pair. It is not an operation of the finite program. -/
def presenceTape : List (Bool × Bool) → Bool → List Bool → List Bool → Tape Bool
  | [], current, left, suffix => Tape.mk₂ left (current :: suffix)
  | pair :: rest, current, left, suffix =>
      presenceTape rest pair.2 (pair.1 :: current :: left) suffix

theorem pairBits_length (pairs : List (Bool × Bool)) : (pairBits pairs).length = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih => simp [pairBits] at ih ⊢; omega

/-- Every actual read is paid by the literal presenceCode; all values,
caller flags and the ENTIRE tape are retained. No host projection acts as
a machine transition. Final code instantiates the compile-time32 pairs. -/
theorem presenceCode_correct (pairs : List (Bool × Bool)) (current : Bool)
    (left suffix : List Bool) (saved : Store) (next : Statement) :
    TM1.stepAux (presenceCode pairs.length next) saved
      (Tape.mk₂ left (current :: (pairBits pairs ++ suffix))) =
      TM1.stepAux next (seenStore saved (pairFound pairs)) (presenceTape pairs current left suffix) := by
  induction pairs generalizing current left saved with
  | nil => simp [presenceCode, pairBits, pairFound, seenStore, presenceTape]
  | cons pair rest ih =>
    rcases pair with ⟨present, value⟩
    simpa [presenceCode, pairBits, pairFound, presenceTape, seenStore,
      TM1.stepAux, Tape.mk₂, Bool.or_assoc] using
      ih value (present :: current :: left) (seenStore saved present)

theorem presenceTape_right (pairs : List (Bool × Bool)) (current : Bool) (left suffix : List Bool) :
    (presenceTape pairs current left suffix).move .right =
      Tape.mk₂ ((current :: pairBits pairs).reverse ++ left) suffix := by
  induction pairs generalizing current left with
  | nil => simp [presenceTape, pairBits, Tape.mk₂]
  | cons pair rest ih =>
    rcases pair with ⟨present, value⟩
    simpa [presenceTape, pairBits, List.reverse_cons, List.append_assoc] using
      ih value (present :: current :: left)

/-- Exactly one full physical65-bit row, observing all32 presences.
The successor head is at the next row's col0; every old bit is retained. -/
theorem presence_row_goto (pairs : List (Bool × Bool)) (width : pairs.length = 32)
    (current : Bool) (left suffix : List Bool) (saved : Store) (target : Label) :
    TM1.stepAux (presenceCode 32 (.move .right (.goto (fun _ _ => target)))) saved
      (Tape.mk₂ left (current :: (pairBits pairs ++ suffix))) =
      cfg target (seenStore saved (pairFound pairs))
        (Tape.mk₂ ((current :: pairBits pairs).reverse ++ left) suffix) := by
  rw [← width, presenceCode_correct]
  simp only [TM1.stepAux, presenceTape_right]
  rfl

/-- Finite source-row read/mark prefix with an arbitrary fixed caller
continuation. The old col0 is observed BEFORE it is really overwritten. -/
theorem mark_prefix (saved : Store) (bottom present bit : Bool) (left suffix : List Bool)
    (next : Statement) :
    TM1.stepAux
      (.load (fun symbol saved => { saved with bottom := symbol })
        (.write (fun _ _ => true)
          (Wide.moveCode .right 2
            (.load (fun symbol saved => { saved with bit := symbol }) (Wide.moveCode .left 2 next)))))
      saved (Tape.mk₂ left (bottom :: present :: bit :: suffix)) =
      TM1.stepAux next { saved with bottom := bottom, bit := bit }
        (Tape.mk₂ left (true :: present :: bit :: suffix)) := by
  simp [Wide.moveCode, TM1.stepAux, Tape.mk₂]

theorem markCurrent_effect (target : Label) (saved : Store) (bottom present bit : Bool)
    (left suffix : List Bool) :
    TM1.stepAux (markCurrent target) saved (Tape.mk₂ left (bottom :: present :: bit :: suffix)) =
      cfg target { saved with bottom := bottom, bit := bit }
        ((fun old : Tape Bool => old.move .right)^[65]
          (Tape.mk₂ left (true :: present :: bit :: suffix))) := by
  unfold markCurrent
  rw [mark_prefix, Wide.moveCode_semantics]
  rfl

end PDROC.BitVM.Common.IO.Output
