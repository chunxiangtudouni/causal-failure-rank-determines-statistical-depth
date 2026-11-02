module

public import PaperProofs.Paid.MenuCompiler

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem endpointTestingAction_ne_allocate (P : Parameters) (N K level : ℕ) (seed : MenuSeed N K)
    (history : List (VisibleEvent (freshInstance N K))) (stage : (freshInstance N K).Stage)
    (handle : MismatchHandle (freshInstance N K)) (tool : (freshInstance N K).Tool) :
    P.endpointTestingAction N K level seed history stage ≠ .allocate handle tool := by
  dsimp only [Parameters.endpointTestingAction]
  split_ifs <;> intro he <;> cases he

theorem menuRepairAction_allocate_choice (P : Parameters) (N K : ℕ)
    (history : List (VisibleEvent (freshInstance N K))) (stage : (freshInstance N K).Stage)
    (handle : MismatchHandle (freshInstance N K)) (tool : (freshInstance N K).Tool)
    (ha : P.menuRepairAction N K history stage = .allocate handle tool) :
    P.menuUnusedTool N K history = some tool := by
  unfold Parameters.menuRepairAction at ha
  by_cases hd : (historyExecutions history).any (fun pair => pair.1.stage == stage) = true
  · rw [ite_eq_left hd] at ha
    cases ha
  · rw [ite_eq_right hd] at ha
    cases hc : (historyCommitments history).find? (fun pair => pair.1.stage == stage) with
    | some pair => rw [hc] at ha; cases ha
    | none =>
      rw [hc] at ha
      cases hh : referenceVisibleHandle history stage with
      | none => rw [hh] at ha; cases ha
      | some selectedHandle =>
        rw [hh] at ha
        cases ht : P.menuUnusedTool N K history with
        | none => rw [ht] at ha; cases ha
        | some selectedTool =>
          rw [ht] at ha
          have heq : selectedTool = tool := (Action.allocate.inj ha).2
          exact congrArg some heq

/-- Every actual candidate allocation uses precisely the original finite
unused-tool query, rather than an arbitrary compatible witness. -/
theorem menuCandidateAction_allocate_choice (P : Parameters) (N K : ℕ) (table : MenuTable)
    (seed : MenuSeed N K) (history : List (VisibleEvent (freshInstance N K)))
    (handle : MismatchHandle (freshInstance N K)) (tool : (freshInstance N K).Tool)
    (ha : P.menuCandidateAction N K table seed history = .allocate handle tool) :
    P.menuUnusedTool N K history = some tool := by
  classical
  unfold Parameters.menuCandidateAction at ha
  by_cases hh : historyHalted history = true
  · rw [ite_eq_left hh] at ha
    cases ha
  · rw [ite_eq_right hh] at ha
    by_cases hc : historyCursor history < N
    · rw [dite_eq_left hc] at ha
      dsimp only at ha
      let stage : (freshInstance N K).Stage := ⟨historyCursor history, by simpa [freshInstance] using hc⟩
      cases hw : historyWrite history stage with
      | none =>
        rw [hw] at ha
        dsimp only at ha
        change (match (Parameters.menuEntryAt table (N - stage.val) (P.menuEntryTools N K history stage)).action with
          | .finish | .abandon => Action.abandon
          | .test level _ => P.endpointTestingAction N K level seed history stage) = .allocate handle tool at ha
        cases he : (Parameters.menuEntryAt table (N - stage.val) (P.menuEntryTools N K history stage)).action with
        | finish => simp only [he] at ha; cases ha
        | abandon => simp only [he] at ha; cases ha
        | test level bad =>
          simp only [he] at ha
          exact (endpointTestingAction_ne_allocate P N K level seed history stage handle tool ha).elim
      | some pair =>
        obtain ⟨bit, serial⟩ := pair
        rw [hw] at ha
        dsimp only at ha
        cases hr : historyReport history stage with
        | none => rw [hr] at ha; cases ha
        | some packet =>
          obtain ⟨truth, reportedSerial⟩ := packet
          rw [hr] at ha
          dsimp only at ha
          by_cases hserial : (serial != reportedSerial) = true
          · rw [ite_eq_left hserial] at ha
            cases ha
          · rw [ite_eq_right hserial] at ha
            by_cases hbit : (bit == truth) = true
            · rw [ite_eq_left hbit] at ha
              cases ha
            · rw [ite_eq_right hbit] at ha
              change (match (Parameters.menuEntryAt table (N - stage.val) (P.menuEntryTools N K history stage)).action with
                | .test _ .repair => P.menuRepairAction N K history stage
                | _ => Action.abandon) = .allocate handle tool at ha
              cases he : (Parameters.menuEntryAt table (N - stage.val) (P.menuEntryTools N K history stage)).action with
              | finish => simp only [he] at ha; cases ha
              | abandon => simp only [he] at ha; cases ha
              | test level bad =>
                simp only [he] at ha
                cases bad with
                | abandon => cases ha
                | repair => exact menuRepairAction_allocate_choice P N K history stage handle tool ha
    · rw [dite_eq_right hc] at ha
      split_ifs at ha

end PDMenu
