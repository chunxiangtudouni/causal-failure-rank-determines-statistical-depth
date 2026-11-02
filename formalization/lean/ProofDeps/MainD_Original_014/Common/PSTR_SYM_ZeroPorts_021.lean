module

public import Common.PSTR_SYM_OriginalZeroErase_020
public import Common.PSTR_SYM_PrependFrame_015
public import Structure.PA17_TM_RatArithmetic_Allocate_013d
public import Structure.PA17_TM_RatArithmetic_Unblock_004c

/-! Actual N0 cursor ports. Clear the genuine old EOF, reuse the frozen
LEFT seek on its physically established zero strip, then perform NINETEEN
real RIGHT transitions. These fixed finite controls are not an allocator,
an input-dependent machine family, a known-distance jump or a cursor reset. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicZeroTail

open Turing PSTRTMSeq005 PA17TMRatArithmeticAllocate013

theorem tape_false_suffix (left right : List Bool) (count : Nat) :
    Tape.mk₂ left (right ++ List.replicate count false) = Tape.mk₂ left right := by
  unfold Tape.mk₂
  rw [PSTRTMPackFinish039.blank_false_suffix]

theorem tape_false_left (left right : List Bool) (count : Nat) :
    Tape.mk₂ (left ++ List.replicate count false) right = Tape.mk₂ left right := by
  unfold Tape.mk₂
  rw [PSTRTMPackFinish039.blank_false_suffix]

def clearEOFMachine : Machine 1 := fun label _ =>
  if label.val = 0 then some (1, .write false) else none

def clearEOFTrace (left : List Bool) : List (MachineState 1) :=
  [⟨0, Tape.mk₂ left [true]⟩, ⟨1, Tape.mk₂ left []⟩]

theorem clearEOF_runsFrom (left : List Bool) :
    RunsFrom clearEOFMachine ⟨0, Tape.mk₂ left [true]⟩
      (clearEOFTrace left) ⟨1, Tape.mk₂ left []⟩ := by
  refine ⟨rfl, ?_, rfl, ?_⟩
  · simp [clearEOFTrace, List.isChain_cons_cons, TM0.step, clearEOFMachine, Tape.mk₂]
    have blank : ListBlank.mk ([false] : List Bool) = ListBlank.mk [] := by
      simpa using PSTRTMPackFinish039.blank_false_suffix [] 1
    exact congrArg (Tape.mk' (ListBlank.mk left)) blank
  · simp [TM0.step, clearEOFMachine]

theorem clearEOF_length (left : List Bool) : (clearEOFTrace left).length = 2 := rfl

/-- Same frozen direction-LEFT code, with its genuine FALSE current cell.
The suffix is carried by every real move, not changed from TRUE for free. -/
def seekFalseTrace (count : Nat) (archive suffix : List Bool) : List (MachineState 1) :=
  seekState 0 (List.replicate count false ++ true :: archive) (false :: suffix) ::
    seekLeftTrace count archive (false :: suffix)

theorem seekFalse_runsFrom (count : Nat) (archive suffix : List Bool) :
    RunsFrom (gapSeekMachine .left)
      (seekState 0 (List.replicate count false ++ true :: archive) (false :: suffix))
      (seekFalseTrace count archive suffix)
      (seekState 1 archive (true :: (List.replicate count false ++ false :: suffix))) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · apply List.IsChain.cons (seekLeft_chain count archive (false :: suffix))
    intro after first
    rw [seekLeft_head] at first
    have equal := Option.mem_some_iff.mp first
    subst after
    simp [TM0.step, gapSeekMachine, seekState]
  · change ([seekState 0 (List.replicate count false ++ true :: archive) (false :: suffix)] ++
      seekLeftTrace count archive (false :: suffix)).getLast? = _
    rw [List.getLast?_append, seekLeft_last]
    rfl
  · simp [TM0.step, gapSeekMachine, seekState, Tape.mk₂]

theorem seekFalse_length (count : Nat) (archive suffix : List Bool) :
    (seekFalseTrace count archive suffix).length = count + 2 := by
  simp [seekFalseTrace, seekLeft_length]

/-- Exactly twenty labels: nineteen RIGHT operations followed by HALT.
The bound19 is fixed code before every original input. -/
def right19Machine : Machine 19 := fun label _ =>
  if live : label.val < 19 then some (⟨label.val + 1, by omega⟩, .move .right) else none

def rightState (label : Nat) (room : label ≤ 19) (tape : Tape Bool) : MachineState 19 :=
  ⟨⟨label, by omega⟩, tape⟩

def rightTrace (done remaining : Nat) (count : done + remaining = 19)
    (tape : Tape Bool) : List (MachineState 19) :=
  match remaining with
  | 0 => [rightState done (by omega) tape]
  | later + 1 => rightState done (by omega) tape ::
      rightTrace (done + 1) later (by omega) (tape.move .right)
termination_by remaining

theorem rightTrace_head (done remaining : Nat) (count : done + remaining = 19) (tape : Tape Bool) :
    (rightTrace done remaining count tape).head? = some (rightState done (by omega) tape) := by
  cases remaining <;> simp [rightTrace]

theorem rightTrace_last (done remaining : Nat) (count : done + remaining = 19) (tape : Tape Bool) :
    (rightTrace done remaining count tape).getLast? =
      some (rightState 19 (by omega) ((Tape.move .right)^[remaining] tape)) := by
  induction remaining generalizing done tape with
  | zero =>
    have last : done = 19 := by omega
    subst done
    simp [rightTrace]
  | succ remaining ih =>
    have nonempty : rightTrace (done + 1) remaining (by omega) (tape.move .right) ≠ [] := by
      intro empty
      have head := rightTrace_head (done + 1) remaining (by omega) (tape.move .right)
      simp [empty] at head
    rw [rightTrace, List.getLast?_cons_of_ne_nil nonempty, ih]
    simp only [Function.iterate_succ_apply]

theorem rightTrace_chain (done remaining : Nat) (count : done + remaining = 19) (tape : Tape Bool) :
    (rightTrace done remaining count tape).IsChain
      (fun before after => TM0.step right19Machine before = some after) := by
  induction remaining generalizing done tape with
  | zero => simp [rightTrace]
  | succ remaining ih =>
    rw [rightTrace]
    apply List.IsChain.cons (ih (done + 1) (by omega) (tape.move .right))
    intro after first
    rw [rightTrace_head] at first
    have equal := Option.mem_some_iff.mp first
    subst after
    have live : done < 19 := by omega
    simp [TM0.step, right19Machine, rightState, live]

theorem rightTrace_length (done remaining : Nat) (count : done + remaining = 19) (tape : Tape Bool) :
    (rightTrace done remaining count tape).length = remaining + 1 := by
  induction remaining generalizing done tape with
  | zero => simp [rightTrace]
  | succ remaining ih =>
    rw [rightTrace, List.length_cons, ih]

theorem right19_runsFrom (tape : Tape Bool) :
    RunsFrom right19Machine ⟨0, tape⟩ (rightTrace 0 19 (by omega) tape)
      (rightState 19 (by omega) ((Tape.move .right)^[19] tape)) := by
  refine ⟨?_, rightTrace_chain 0 19 (by omega) tape, rightTrace_last 0 19 (by omega) tape, ?_⟩
  · simpa only [rightState, Fin.mk_zero] using rightTrace_head 0 19 (by omega) tape
  · simp [TM0.step, right19Machine, rightState]

theorem right_blank (count : Nat) (left : List Bool) :
    (Tape.move .right)^[count] (Tape.mk₂ left []) =
      Tape.mk₂ (List.replicate count false ++ left) [] := by
  induction count generalizing left with
  | zero => rfl
  | succ count ih =>
    rw [Function.iterate_succ_apply]
    have move : (Tape.mk₂ left ([] : List Bool)).move .right = Tape.mk₂ (false :: left) [] := by
      simp [Tape.mk₂]
    rw [move, ih]
    have zeros : List.replicate count false ++ false :: left = List.replicate (count + 1) false ++ left := by
      rw [List.replicate_succ']
      simp only [List.append_assoc, List.singleton_append]
    rw [zeros]

theorem right19_from_flag (archive : List Bool) :
    (Tape.move .right)^[19] (Tape.mk₂ archive [true]) =
      Tape.mk₂ (List.replicate 18 false ++ true :: archive) [] := by
  have move : (Tape.mk₂ archive [true]).move .right = Tape.mk₂ (true :: archive) [] := by
    simp [Tape.mk₂]
  rw [show 19 = 18 + 1 by decide, Function.iterate_succ_apply, move, right_blank]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicZeroTail
