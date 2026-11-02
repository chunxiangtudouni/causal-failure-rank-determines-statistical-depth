module

public import Structure.RootB23_Threshold_Window_GapHome_002

/-! Physically turn a copied original-data field into a zero-data counter.
Only its flags determine its length. The original archive and following
fields are retained, and every head motion, clear and final rewind is real. -/

@[expose] public section

namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow

open Turing PSTRTMSeq005

def counterDataMachine : Machine 3 := fun q symbol =>
  match q.val with
  | 0 => some (1, .write false)
  | 1 => some (2, .move .right)
  | 2 => if symbol then some (0, .move .right) else some (3, .move .left)
  | _ => none

def dataState (q : Fin 4) (left right : List Bool) : MachineState 3 := ⟨q, Tape.mk₂ left right⟩

def counterDataTrace (suffix : List Bool) : List Bool → List Bool → List (MachineState 3)
  | [], left =>
      [dataState 0 left (false :: false :: suffix),
       dataState 1 left (false :: false :: suffix),
       dataState 2 (false :: left) (false :: suffix),
       dataState 3 left (false :: false :: suffix)]
  | bit :: later, left =>
      [dataState 0 left (bit :: true :: (PSTRTMIncrement009.blocks later ++ false :: false :: suffix)),
       dataState 1 left (false :: true :: (PSTRTMIncrement009.blocks later ++ false :: false :: suffix)),
       dataState 2 (false :: left) (true :: (PSTRTMIncrement009.blocks later ++ false :: false :: suffix))] ++
        counterDataTrace suffix later (true :: false :: left)

theorem counterData_head (suffix digits left : List Bool) :
    (counterDataTrace suffix digits left).head? =
      some (dataState 0 left (PSTRTMIncrement009.blocks digits ++ false :: false :: suffix)) := by
  cases digits <;> rfl

theorem counterData_last (suffix digits left : List Bool) :
    (counterDataTrace suffix digits left).getLast? =
      some (dataState 3 (marks digits.length ++ left) (false :: false :: suffix)) := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    rw [counterDataTrace, List.getLast?_append, ih, marks_snoc]
    rfl

theorem counterData_length (suffix digits left : List Bool) :
    (counterDataTrace suffix digits left).length = 3 * digits.length + 4 := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    simp only [counterDataTrace, List.length_append, List.length_cons, List.length_nil, ih]
    omega

theorem counterData_chain (suffix digits left : List Bool) :
    (counterDataTrace suffix digits left).IsChain
      (fun a b => TM0.step counterDataMachine a = some b) := by
  induction digits generalizing left with
  | nil => simp [counterDataTrace, List.isChain_cons_cons, TM0.step, counterDataMachine, dataState, Tape.mk₂]
  | cons bit later ih =>
    simp only [counterDataTrace, List.cons_append, List.nil_append, List.isChain_cons_cons]
    refine ⟨?_, ?_, ?_⟩
    · simp [TM0.step, counterDataMachine, dataState, Tape.mk₂]
    · simp [TM0.step, counterDataMachine, dataState, Tape.mk₂]
    · apply (ih (true :: false :: left)).cons
      intro state member
      rw [counterData_head] at member
      have equal := Option.mem_some_iff.mp member
      subst state
      simp [TM0.step, counterDataMachine, dataState, Tape.mk₂]

theorem counterData_runsFrom (suffix digits left : List Bool) :
    RunsFrom counterDataMachine
      (dataState 0 left (PSTRTMIncrement009.blocks digits ++ false :: false :: suffix))
      (counterDataTrace suffix digits left)
      (dataState 3 (marks digits.length ++ left) (false :: false :: suffix)) :=
  ⟨counterData_head suffix digits left, counterData_chain suffix digits left,
    counterData_last suffix digits left, by simp [TM0.step, counterDataMachine, dataState]⟩

def normalizeCounterMachine : Machine 8 := seqMachine counterDataMachine (gapHomeMachine true)

def normalizeCounterTrace (archive suffix digits : List Bool) : List (MachineState 8) :=
  (counterDataTrace suffix digits (false :: archive)).map (leftCfg (b := 4)) ++
    (gapHomeTrace true archive (false :: false :: suffix) digits.length).map (rightCfg (a := 3))

theorem normalizeCounter_runsFrom (archive suffix digits : List Bool) :
    RunsFrom normalizeCounterMachine
      ⟨0, Tape.mk₂ (false :: archive) (PSTRTMIncrement009.blocks digits ++ false :: false :: suffix)⟩
      (normalizeCounterTrace archive suffix digits)
      (rightCfg (a := 3) (homeState 4 (false :: archive)
        (pairs true digits.length ++ false :: false :: suffix))) := by
  exact seq_runsFrom counterDataMachine (gapHomeMachine true) _ _ _ _ _
    (counterData_runsFrom suffix digits (false :: archive))
    (gapHome_runsFrom true archive (false :: false :: suffix) digits.length)

theorem normalizeCounter_length (archive suffix digits : List Bool) :
    (normalizeCounterTrace archive suffix digits).length = 6 * digits.length + 7 := by
  simp only [normalizeCounterTrace, List.length_append, List.length_map, counterData_length, gapHome_length]
  omega

theorem normalizeCounter_prefix_space (archive suffix digits : List Bool) (inputLength clock : Nat) :
    visitedSpace normalizeCounterMachine inputLength ((normalizeCounterTrace archive suffix digits).take clock) ≤
      inputLength + 12 * digits.length + 15 := by
  have general := PSTRTMTrace002.visitedSpace_le normalizeCounterMachine inputLength
    ((normalizeCounterTrace archive suffix digits).take clock)
  have taken : ((normalizeCounterTrace archive suffix digits).take clock).length ≤ 6 * digits.length + 7 := by
    rw [List.length_take, normalizeCounter_length]
    exact Nat.min_le_right _ _
  omega

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow
