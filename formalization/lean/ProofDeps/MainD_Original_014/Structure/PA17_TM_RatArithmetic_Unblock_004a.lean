module
public import Common.PSTR_TM_UnblockTrace_019

/-! Framed inverse codec: unchanged parent20-label code, actual rotations.
The unit below has arbitrary left/right data, not an isolated blank tape. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticUnblock004
open PSTRTMUnblock018 PSTRTMHeader003
open PSTRTMUnblockTrace019 (rawWord)

theorem append_link (xs ys : List (MachineState 19)) (last first : MachineState 19)
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

def inverseUnit (bit : Bool) (k : Nat) (left tail : List Bool) : List (MachineState 19) :=
  [state 2 (true :: bit :: left) (List.replicate k true ++ false :: tail),
    state 3 (bit :: left) (true :: (List.replicate k true ++ false :: tail)),
    state 4 left (bit :: true :: (List.replicate k true ++ false :: tail)),
    state (savedMode bit) left (false :: true :: (List.replicate k true ++ false :: tail))] ++
      scanRight bit (k + 1) (false :: left) tail ++
      [state 9 (List.replicate (k + 1) true ++ false :: left) (bit :: tail),
        state 10 (List.replicate k true ++ false :: left) (true :: bit :: tail),
        state 11 (List.replicate k true ++ false :: left) (false :: bit :: tail)] ++
      scanLeft k left (false :: bit :: tail)

theorem inverseUnit_head (bit : Bool) (k : Nat) (left tail : List Bool) :
    (inverseUnit bit k left tail).head? = some
      (state 2 ((true :: bit :: left))
        (List.replicate k true ++ false :: tail)) := rfl

theorem inverseUnit_last (bit : Bool) (k : Nat) (left tail : List Bool) :
    (inverseUnit bit k left tail).getLast? = some
      (state 12 (left)
        (false :: (List.replicate k true ++ false :: bit :: tail))) := by
  unfold inverseUnit
  rw [List.getLast?_append, scanLeft_last]
  rfl

theorem inverseUnit_length (bit : Bool) (k : Nat) (left tail : List Bool) :
    (inverseUnit bit k left tail).length = 2 * k + 10 := by
  simp only [inverseUnit, List.length_append, List.length_cons, List.length_nil,
    scanRight_length, scanLeft_length]
  omega

theorem inverseUnit_chain (bit : Bool) (k : Nat) (left tail : List Bool) :
    (inverseUnit bit k left tail).IsChain (fun before after =>
      Turing.TM0.step unblockMachine before = some after) := by
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
  simpa only [inverseUnit, firstPart, middle, List.append_assoc] using hall


end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticUnblock004

