module
public import PaperProofs.Common.PSTR_TM_NatValue_017

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMUnblock018
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMHeader003

/-- Fixed20-label inverse codec for an isolated flagged operand. The initial
pass finds the genuine end on the tape; each later rotation restores one
original raw bit and one unary header cell. No numeric width is supplied. -/
def unblockMachine : Machine 19 := fun q symbol =>
  match q.val with
  | 0 => some (1, .move .right)
  | 1 => some (if symbol then 0 else 2, if symbol then .move .right else .move .left)
  | 2 => some (3, .move .left)
  | 3 => some (if symbol then 4 else 19, if symbol then .move .left else .move .right)
  | 4 => some (if symbol then 6 else 5, .write false)
  | 5 => some (7, .move .right)
  | 6 => some (8, .move .right)
  | 7 => some (if symbol then 7 else 9, if symbol then .move .right else .write false)
  | 8 => some (if symbol then 8 else 9, if symbol then .move .right else .write true)
  | 9 => some (10, .move .left)
  | 10 => some (11, .write false)
  | 11 => some (12, .move .left)
  | 12 => some (if symbol then 12 else 2, if symbol then .move .left else .write true)
  | _ => none

def state (q : Fin 20) (left right : List Bool) : MachineState 19 :=
  ⟨q, Turing.Tape.mk₂ left right⟩

def rightMode (saved : Bool) : Fin 20 := if saved then 8 else 7
def savedMode (saved : Bool) : Fin 20 := if saved then 6 else 5

def scanRight (saved : Bool) : Nat → List Bool → List Bool → List (MachineState 19)
  | 0, left, tail => [state (rightMode saved) left (false :: tail)]
  | n + 1, left, tail =>
    state (rightMode saved) left (true :: (List.replicate n true ++ false :: tail)) ::
      scanRight saved n (true :: left) tail

theorem scanRight_head (saved : Bool) (n : Nat) (left tail : List Bool) :
    (scanRight saved n left tail).head? = some
      (state (rightMode saved) left (List.replicate n true ++ false :: tail)) := by
  cases n <;> rfl

theorem scanRight_length (saved : Bool) (n : Nat) (left tail : List Bool) :
    (scanRight saved n left tail).length = n + 1 := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih => simp only [scanRight, List.length_cons, ih]

theorem scanRight_last (saved : Bool) (n : Nat) (left tail : List Bool) :
    (scanRight saved n left tail).getLast? = some
      (state (rightMode saved) (List.replicate n true ++ left) (false :: tail)) := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
    have hne : scanRight saved n (true :: left) tail ≠ [] := by
      have hh := scanRight_head saved n (true :: left) tail
      intro h
      simp [h] at hh
    rw [scanRight, List.getLast?_cons_of_ne_nil hne, ih]
    rw [replicate_push]

theorem scanRight_chain (saved : Bool) (n : Nat) (left tail : List Bool) :
    (scanRight saved n left tail).IsChain (fun before after =>
      Turing.TM0.step unblockMachine before = some after) := by
  induction n generalizing left with
  | zero => exact .singleton _
  | succ n ih =>
    rw [scanRight]
    apply List.isChain_cons.mpr
    constructor
    · intro next hn
      rw [scanRight_head] at hn
      have he := Option.mem_some_iff.mp hn
      subst next
      cases saved <;> simp [Turing.TM0.step, unblockMachine, state, rightMode, Turing.Tape.mk₂]
    · exact ih _

def scanLeft : Nat → List Bool → List Bool → List (MachineState 19)
  | 0, left, tail => [state 12 left (false :: tail)]
  | n + 1, left, tail =>
    state 12 (List.replicate n true ++ false :: left) (true :: tail) ::
      scanLeft n left (true :: tail)

def leftInitial : Nat → List Bool → List Bool → MachineState 19
  | 0, left, tail => state 12 left (false :: tail)
  | n + 1, left, tail => state 12 (List.replicate n true ++ false :: left) (true :: tail)

theorem scanLeft_head (n : Nat) (left tail : List Bool) :
    (scanLeft n left tail).head? = some (leftInitial n left tail) := by
  cases n <;> rfl

theorem scanLeft_length (n : Nat) (left tail : List Bool) :
    (scanLeft n left tail).length = n + 1 := by
  induction n generalizing tail with
  | zero => rfl
  | succ n ih => simp only [scanLeft, List.length_cons, ih]

theorem scanLeft_last (n : Nat) (left tail : List Bool) :
    (scanLeft n left tail).getLast? = some
      (state 12 left (false :: (List.replicate n true ++ tail))) := by
  induction n generalizing tail with
  | zero => rfl
  | succ n ih =>
    have hne : scanLeft n left (true :: tail) ≠ [] := by
      have hh := scanLeft_head n left (true :: tail)
      intro h
      simp [h] at hh
    rw [scanLeft, List.getLast?_cons_of_ne_nil hne, ih]
    rw [replicate_push]

theorem scanLeft_chain (n : Nat) (left tail : List Bool) :
    (scanLeft n left tail).IsChain (fun before after =>
      Turing.TM0.step unblockMachine before = some after) := by
  induction n generalizing tail with
  | zero => exact .singleton _
  | succ n ih =>
    rw [scanLeft]
    apply List.isChain_cons.mpr
    constructor
    · intro next hn
      rw [scanLeft_head] at hn
      have he := Option.mem_some_iff.mp hn
      subst next
      cases n <;> simp [leftInitial, Turing.TM0.step, unblockMachine, state, Turing.Tape.mk₂,
        List.replicate_succ]
    · exact ih _

private theorem append_link (xs ys : List (MachineState 19)) (last first : MachineState 19)
    (hx : xs.IsChain (fun a b => Turing.TM0.step unblockMachine a = some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step unblockMachine a = some b))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (hs : Turing.TM0.step unblockMachine last = some first) :
    (xs ++ ys).IsChain (fun a b => Turing.TM0.step unblockMachine a = some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

def inverseUnit (bit : Bool) (previous tail : List Bool) : List (MachineState 19) :=
  let k := tail.length
  let left := PSTRTMRawNat010.leftBlocks previous
  [state 2 (true :: bit :: left) (List.replicate k true ++ false :: tail),
    state 3 (bit :: left) (true :: (List.replicate k true ++ false :: tail)),
    state 4 left (bit :: true :: (List.replicate k true ++ false :: tail)),
    state (savedMode bit) left (false :: true :: (List.replicate k true ++ false :: tail))] ++
      scanRight bit (k + 1) (false :: left) tail ++
      [state 9 (List.replicate (k + 1) true ++ false :: left) (bit :: tail),
        state 10 (List.replicate k true ++ false :: left) (true :: bit :: tail),
        state 11 (List.replicate k true ++ false :: left) (false :: bit :: tail)] ++
      scanLeft k left (false :: bit :: tail)

theorem inverseUnit_head (bit : Bool) (previous tail : List Bool) :
    (inverseUnit bit previous tail).head? = some
      (state 2 (PSTRTMRawNat010.leftBlocks (bit :: previous))
        (List.replicate tail.length true ++ false :: tail)) := rfl

theorem inverseUnit_last (bit : Bool) (previous tail : List Bool) :
    (inverseUnit bit previous tail).getLast? = some
      (state 12 (PSTRTMRawNat010.leftBlocks previous)
        (false :: (List.replicate tail.length true ++ false :: bit :: tail))) := by
  unfold inverseUnit
  rw [List.getLast?_append, scanLeft_last]
  rfl

theorem inverseUnit_length (bit : Bool) (previous tail : List Bool) :
    (inverseUnit bit previous tail).length = 2 * tail.length + 10 := by
  simp only [inverseUnit, List.length_append, List.length_cons, List.length_nil,
    scanRight_length, scanLeft_length]
  omega

theorem inverseUnit_chain (bit : Bool) (previous tail : List Bool) :
    (inverseUnit bit previous tail).IsChain (fun before after =>
      Turing.TM0.step unblockMachine before = some after) := by
  let k := tail.length
  let left := PSTRTMRawNat010.leftBlocks previous
  let firstPart := [state 2 (true :: bit :: left) (List.replicate k true ++ false :: tail),
    state 3 (bit :: left) (true :: (List.replicate k true ++ false :: tail)),
    state 4 left (bit :: true :: (List.replicate k true ++ false :: tail)),
    state (savedMode bit) left (false :: true :: (List.replicate k true ++ false :: tail))]
  let middle := [state 9 (List.replicate (k + 1) true ++ false :: left) (bit :: tail),
    state 10 (List.replicate k true ++ false :: left) (true :: bit :: tail),
    state 11 (List.replicate k true ++ false :: left) (false :: bit :: tail)]
  have hp : firstPart.IsChain (fun a b => Turing.TM0.step unblockMachine a = some b) := by
    cases bit <;> simp [firstPart, List.isChain_cons_cons, Turing.TM0.step, unblockMachine,
      state, savedMode, Turing.Tape.mk₂]
  have hm : middle.IsChain (fun a b => Turing.TM0.step unblockMachine a = some b) := by
    simp [middle, List.isChain_cons_cons, Turing.TM0.step, unblockMachine, state, Turing.Tape.mk₂,
      List.replicate_succ]
  have hml := append_link middle (scanLeft k left (false :: bit :: tail)) _ _ hm
    (scanLeft_chain _ _ _) (by rfl) (scanLeft_head _ _ _) (by
      cases k <;> simp [leftInitial, Turing.TM0.step, unblockMachine, state, Turing.Tape.mk₂,
        List.replicate_succ])
  have hmh : (middle ++ scanLeft k left (false :: bit :: tail)).head? = some
      (state 9 (List.replicate (k + 1) true ++ false :: left) (bit :: tail)) := by
    simp [middle]
  have hr := append_link (scanRight bit (k + 1) (false :: left) tail)
    (middle ++ scanLeft k left (false :: bit :: tail)) _ _ (scanRight_chain _ _ _ _) hml
    (scanRight_last _ _ _ _) hmh (by
      cases bit <;> simp [rightMode, Turing.TM0.step, unblockMachine, state, Turing.Tape.mk₂])
  have hrh : (scanRight bit (k + 1) (false :: left) tail ++
      middle ++ scanLeft k left (false :: bit :: tail)).head? = some
      (state (rightMode bit) (false :: left) (List.replicate (k + 1) true ++ false :: tail)) := by
    simp [List.head?_append, scanRight_head]
  have hall := append_link firstPart
    (scanRight bit (k + 1) (false :: left) tail ++ (middle ++ scanLeft k left (false :: bit :: tail))) _ _
    hp (by simpa only [List.append_assoc] using hr) (by rfl)
    (by simpa only [List.append_assoc] using hrh) (by
      cases bit <;> simp [savedMode, rightMode, Turing.TM0.step, unblockMachine, state,
        Turing.Tape.mk₂, List.replicate_succ])
  simpa only [inverseUnit, k, left, firstPart, middle, List.append_assoc] using hall

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMUnblock018
