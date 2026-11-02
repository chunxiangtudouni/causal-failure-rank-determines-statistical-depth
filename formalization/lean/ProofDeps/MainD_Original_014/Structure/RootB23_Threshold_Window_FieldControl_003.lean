module

public import Structure.RootB23_Threshold_Window_GapHome_002
public import Structure.PA17_TM_Division_Compose_006a

/-! Real control for one archive-preserving flagged-field traversal. The
callee is always EAST of the caller's marked flag. Each return finds and
restores that same flag. The full final rewind is the checked GapHome code. -/

@[expose] public section

namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow

open Turing PSTRTMSeq005 PA17TMDivisionCompose006

def fieldControl : Machine 12 := fun q symbol =>
  match q.val with
  | 0 => some (1, .move .right)
  | 1 => if symbol then some (2, .write false) else some (7, .move .left)
  | 2 => some (3, .move .right)
  | 3 => some (4, .move .right)
  | 4 => if symbol then some (3, .move .right) else some (5, .move .right)
  | 6 => some (8, .move .left)
  | 8 => some (9, .move .left)
  | 10 => some (11, .move .left)
  | 11 => some (12, .write true)
  | 12 => some (0, .move .right)
  | _ => none

def controlState (q : Fin 13) (left right : List Bool) : MachineState 12 :=
  ⟨q, Tape.mk₂ left right⟩

def fieldTailScan (work : List Bool) : Nat → List Bool → List (MachineState 12)
  | 0, left =>
      [controlState 3 left (false :: false :: work),
       controlState 4 (false :: left) (false :: work),
       controlState 5 (false :: false :: left) work]
  | n + 1, left =>
      [controlState 3 left (false :: true :: (pairs true n ++ false :: false :: work)),
       controlState 4 (false :: left) (true :: (pairs true n ++ false :: false :: work))] ++
        fieldTailScan work n (true :: false :: left)

theorem fieldTailScan_head (work : List Bool) (n : Nat) (left : List Bool) :
    (fieldTailScan work n left).head? =
      some (controlState 3 left (pairs true n ++ false :: false :: work)) := by
  cases n <;> rfl

theorem fieldTailScan_last (work : List Bool) (n : Nat) (left : List Bool) :
    (fieldTailScan work n left).getLast? =
      some (controlState 5 (false :: false :: (marks n ++ left)) work) := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
    rw [fieldTailScan, List.getLast?_append, ih, marks_snoc]
    rfl

theorem fieldTailScan_length (work : List Bool) (n : Nat) (left : List Bool) :
    (fieldTailScan work n left).length = 2 * n + 3 := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih => simp only [fieldTailScan, List.length_append, List.length_cons, List.length_nil, ih]; omega

theorem fieldTailScan_chain (work : List Bool) (n : Nat) (left : List Bool) :
    (fieldTailScan work n left).IsChain (fun a b => TM0.step fieldControl a = some b) := by
  induction n generalizing left with
  | zero => simp [fieldTailScan, List.isChain_cons_cons, TM0.step, fieldControl, controlState, Tape.mk₂]
  | succ n ih =>
    simp only [fieldTailScan, List.cons_append, List.nil_append, List.isChain_cons_cons]
    refine ⟨?_, ?_⟩
    · simp [TM0.step, fieldControl, controlState, Tape.mk₂]
    · apply (ih (true :: false :: left)).cons
      intro state member
      rw [fieldTailScan_head] at member
      have equal := Option.mem_some_iff.mp member
      subst state
      simp [TM0.step, fieldControl, controlState, Tape.mk₂]

def fieldEnterTrace (left work : List Bool) (remaining : Nat) : List (MachineState 12) :=
  [controlState 0 left (false :: true :: (pairs true remaining ++ false :: false :: work)),
   controlState 1 (false :: left) (true :: (pairs true remaining ++ false :: false :: work)),
   controlState 2 (false :: left) (false :: (pairs true remaining ++ false :: false :: work))] ++
      fieldTailScan work remaining (false :: false :: left)

theorem fieldEnter_runsFrom (left work : List Bool) (remaining : Nat) :
    RunsFrom fieldControl
      (controlState 0 left (pairs true (remaining + 1) ++ false :: false :: work))
      (fieldEnterTrace left work remaining)
      (controlState 5 (false :: false :: (marks remaining ++ false :: false :: left)) work) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp only [fieldEnterTrace, List.cons_append, List.nil_append, List.isChain_cons_cons]
    refine ⟨?_, ?_, ?_⟩
    · simp [TM0.step, fieldControl, controlState, Tape.mk₂]
    · simp [TM0.step, fieldControl, controlState, Tape.mk₂]
    · apply (fieldTailScan_chain work remaining (false :: false :: left)).cons
      intro state member
      rw [fieldTailScan_head] at member
      have equal := Option.mem_some_iff.mp member
      subst state
      simp [TM0.step, fieldControl, controlState, Tape.mk₂]
  · rw [fieldEnterTrace, List.getLast?_append, fieldTailScan_last]
    rfl
  · simp [TM0.step, fieldControl, controlState]

theorem fieldEnter_length (left work : List Bool) (remaining : Nat) :
    (fieldEnterTrace left work remaining).length = 2 * remaining + 6 := by
  simp only [fieldEnterTrace, List.length_append, List.length_cons, List.length_nil, fieldTailScan_length]
  omega

def fieldReturnTrace (left work : List Bool) : List (MachineState 12) :=
  [controlState 6 (false :: false :: left) work,
   controlState 8 (false :: left) (false :: work),
   controlState 9 left (false :: false :: work)]

theorem fieldReturn_runsFrom (left work : List Bool) :
    RunsFrom fieldControl (controlState 6 (false :: false :: left) work)
      (fieldReturnTrace left work) (controlState 9 left (false :: false :: work)) := by
  refine ⟨rfl, ?_, rfl, ?_⟩
  · simp [fieldReturnTrace, List.isChain_cons_cons, TM0.step, fieldControl, controlState, Tape.mk₂]
  · simp [TM0.step, fieldControl, controlState]

def fieldRestoreTrace (left work : List Bool) : List (MachineState 12) :=
  [controlState 10 (false :: false :: left) work,
   controlState 11 (false :: left) (false :: work),
   controlState 12 (false :: left) (true :: work)]

theorem fieldRestore_segment (left work : List Bool) :
    Segment fieldControl (controlState 10 (false :: false :: left) work)
      (fieldRestoreTrace left work) (controlState 12 (false :: left) (true :: work)) := by
  refine ⟨rfl, ?_, rfl⟩
  simp [fieldRestoreTrace, List.isChain_cons_cons, TM0.step, fieldControl, controlState, Tape.mk₂]

theorem fieldRestore_next (left work : List Bool) :
    TM0.step fieldControl (controlState 12 (false :: left) (true :: work)) =
      some (controlState 0 (true :: false :: left) work) := by
  simp [TM0.step, fieldControl, controlState, Tape.mk₂]

def fieldFinishTrace (left work : List Bool) : List (MachineState 12) :=
  [controlState 0 left (false :: false :: work),
   controlState 1 (false :: left) (false :: work),
   controlState 7 left (false :: false :: work)]

theorem fieldFinish_runsFrom (left work : List Bool) :
    RunsFrom fieldControl (controlState 0 left (false :: false :: work))
      (fieldFinishTrace left work) (controlState 7 left (false :: false :: work)) := by
  refine ⟨rfl, ?_, rfl, ?_⟩
  · simp [fieldFinishTrace, List.isChain_cons_cons, TM0.step, fieldControl, controlState, Tape.mk₂]
  · simp [TM0.step, fieldControl, controlState]

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow
