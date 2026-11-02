module

public import Structure.RootB23_Threshold_Window_FieldIteration_005

/-! Single-layer real counted traversal, including its true final rewind.
The inner-run parameter is internal composition only. The later closed
recursive power producer discharges it with actual code at every depth. -/

@[expose] public section

namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow

open Turing PSTRTMSeq005 PA17TMDivisionCompose006

def fieldLoopCost (fee : Nat → Nat) (growth : Nat) : Nat → Nat → Nat → Nat
  | 0, done, _ => 3 * done + 6
  | n + 1, done, gap => 5 * n + 15 + fee gap + fieldLoopCost fee growth n (done + 1) (gap + growth)

def InnerRunContract {states : Nat} (body : Machine states) (exit : Fin (states + 1))
    (word : Nat → List Bool) (growth : Nat) (fee : Nat → Nat) : Prop :=
  ∀ (archive : List Bool) (gap : Nat), ∃ trace,
    RunsFrom body ⟨0, Tape.mk₂ (false :: archive) (word gap)⟩ trace
      ⟨exit, Tape.mk₂ (false :: archive) (word (gap + growth))⟩ ∧ trace.length ≤ fee gap

theorem field_loop_from {states : Nat} (body : Machine states) (exit : Fin (states + 1))
    (word : Nat → List Bool) (growth : Nat) (fee : Nat → Nat)
    (inner : InnerRunContract body exit word growth fee) (archive : List Bool) :
    ∀ (remaining done gap : Nat), ∃ trace,
      RunsFrom (fieldMachine body exit)
        (controlLift (controlState 0 (marks done ++ false :: archive)
          (pairs true remaining ++ false :: false :: word gap))) trace
        (homeLift 3 (homeState 4 (false :: archive)
          (pairs true (remaining + done) ++ false :: false :: word (gap + growth * remaining)))) ∧
      trace.length ≤ fieldLoopCost fee growth remaining done gap := by
  intro remaining
  induction remaining with
  | zero =>
    intro done gap
    obtain ⟨trace, run, time⟩ := field_finish body exit archive (word gap) done
    refine ⟨trace, ?_, ?_⟩
    · simpa only [pairs, List.nil_append, Nat.zero_add, Nat.mul_zero, Nat.add_zero] using run
    · simpa only [fieldLoopCost, time] using (Nat.le_refl (3 * done + 6))
  | succ n ih =>
    intro done gap
    let left := marks done ++ false :: archive
    let bodyArchive := false :: (marks n ++ false :: false :: left)
    obtain ⟨middle, middleRun, middleTime⟩ := inner bodyArchive gap
    obtain ⟨head, headSegment, headLength⟩ := field_iteration body exit left (word gap)
      (word (gap + growth)) n middle middleRun
    obtain ⟨tail, tailRun, tailTime⟩ := ih (done + 1) (gap + growth)
    have next := field_iteration_next body exit left
      (pairs true n ++ false :: false :: word (gap + growth))
    have toTail :
        TM0.step (fieldMachine body exit)
          (controlLift (controlState 12 (false :: left)
            (true :: (pairs true n ++ false :: false :: word (gap + growth))))) =
          some (controlLift (controlState 0 (marks (done + 1) ++ false :: archive)
            (pairs true n ++ false :: false :: word (gap + growth)))) := by
      simpa only [left, marks, List.cons_append] using next
    have tailSegment : Segment (fieldMachine body exit) _ tail _ :=
      ⟨tailRun.1, tailRun.2.1, tailRun.2.2.1⟩
    have full := segment_append (fieldMachine body exit) _ _ _ _ _ _ headSegment tailSegment toTail
    have fullRun := segment_runsFrom _ _ _ _ full tailRun.2.2.2
    have index : (gap + growth) + growth * n = gap + growth * (n + 1) := by ring
    have count : n + (done + 1) = (n + 1) + done := by omega
    refine ⟨head ++ tail, ?_, ?_⟩
    · simpa only [left, count, index] using fullRun
    · rw [List.length_append, headLength, fieldLoopCost]
      omega

def fieldExit (states : Nat) : Fin (fieldCap states + 1) :=
  label (3 : Fin 4) (padLabel (by omega : 4 ≤ states + 12) (4 : Fin 5))

theorem controlLift_zero {states : Nat} (tape : Tape Bool) :
    controlLift (⟨0, tape⟩ : MachineState 12) = (⟨0, tape⟩ : MachineState (fieldCap states)) := by
  simp [controlLift, padCfg, padLabel, blockCfg, label]

theorem field_loop_runsFrom {states : Nat} (body : Machine states) (exit : Fin (states + 1))
    (word : Nat → List Bool) (growth : Nat) (fee : Nat → Nat)
    (inner : InnerRunContract body exit word growth fee) (archive : List Bool) (n gap : Nat) :
    ∃ trace, RunsFrom (fieldMachine body exit)
      ⟨0, Tape.mk₂ (false :: archive) (pairs true n ++ false :: false :: word gap)⟩ trace
      ⟨fieldExit states, Tape.mk₂ (false :: archive)
        (pairs true n ++ false :: false :: word (gap + growth * n))⟩ ∧
      trace.length ≤ fieldLoopCost fee growth n 0 gap ∧
      ∀ inputLength clock,
        visitedSpace (fieldMachine body exit) inputLength (trace.take clock) ≤
          inputLength + 2 * fieldLoopCost fee growth n 0 gap + 1 := by
  obtain ⟨trace, run, time⟩ := field_loop_from body exit word growth fee inner archive n 0 gap
  have actual : RunsFrom (fieldMachine body exit)
      ⟨0, Tape.mk₂ (false :: archive) (pairs true n ++ false :: false :: word gap)⟩ trace
      ⟨fieldExit states, Tape.mk₂ (false :: archive)
        (pairs true n ++ false :: false :: word (gap + growth * n))⟩ := by
    simpa only [marks, List.nil_append, controlState, controlLift_zero, Nat.add_zero,
      homeLift, homeState, blockCfg, padCfg, fieldExit] using run
  refine ⟨trace, actual, time, ?_⟩
  intro inputLength clock
  have general := PSTRTMTrace002.visitedSpace_le (fieldMachine body exit) inputLength (trace.take clock)
  have taken : (trace.take clock).length ≤ trace.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  omega

theorem fieldLoopCost_le_constant (fee : Nat → Nat) (growth remaining done gap bound : Nat)
    (fees : ∀ index ≤ gap + growth * remaining, fee index ≤ bound) :
    fieldLoopCost fee growth remaining done gap ≤
      remaining * (bound + 8 * (remaining + done) + 18) + 3 * done + 6 := by
  induction remaining generalizing done gap with
  | zero => simp [fieldLoopCost]
  | succ n ih =>
    have current := fees gap (by omega)
    have later : ∀ index ≤ (gap + growth) + growth * n, fee index ≤ bound := by
      intro index beforeEnd
      apply fees index
      have endpoint : (gap + growth) + growth * n = gap + growth * (n + 1) := by ring
      omega
    have smaller := ih (done + 1) (gap + growth) later
    rw [fieldLoopCost]
    nlinarith

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow
