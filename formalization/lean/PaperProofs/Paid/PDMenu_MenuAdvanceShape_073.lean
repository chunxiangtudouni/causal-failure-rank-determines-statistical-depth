module

public import PaperProofs.Paid.MenuCompiler

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem endpointTestingAction_ne_advance (P : Parameters) (N K level : ℕ) (seed : MenuSeed N K)
    (history : List (VisibleEvent (freshInstance N K))) (stage next : (freshInstance N K).Stage) :
    P.endpointTestingAction N K level seed history stage ≠ .advance next := by
  dsimp only [Parameters.endpointTestingAction]
  split_ifs <;> intro he <;> cases he

theorem menuRepairAction_advance_spec (P : Parameters) (N K : ℕ)
    (history : List (VisibleEvent (freshInstance N K))) (stage next : (freshInstance N K).Stage)
    (ha : P.menuRepairAction N K history stage = .advance next) :
    next = stage ∧ ∃ pair ∈ historyExecutions history, pair.1.stage = next := by
  unfold Parameters.menuRepairAction at ha
  split_ifs at ha with hdone
  · have hs : stage = next := Action.advance.inj ha
    obtain ⟨pair, hp, hs'⟩ := List.any_eq_true.mp hdone
    have hpStage : pair.1.stage = stage := by simpa only [beq_iff_eq] using hs'
    exact ⟨hs.symm, pair, hp, hpStage.trans hs⟩
  · cases hc : (historyCommitments history).find? (fun pair => pair.1.stage == stage) with
    | some pair => simp only [hc] at ha; cases ha
    | none =>
      simp only [hc] at ha
      cases hh : referenceVisibleHandle history stage <;> simp only [hh] at ha
      · cases ha
      · cases ht : P.menuUnusedTool N K history <;> simp only [ht] at ha <;> cases ha

/-- A literal menu advance either accepts its actual public correct packet
or follows an actual physical execution. Merely holding a commitment is
not a third branch. -/
theorem menuCandidateAction_advance_spec (P : Parameters) (N K : ℕ) (table : MenuTable)
    (seed : MenuSeed N K) (history : List (VisibleEvent (freshInstance N K)))
    (next : (freshInstance N K).Stage) (ha : P.menuCandidateAction N K table seed history = .advance next) :
    (∃ bit serial, historyWritten history next = some bit ∧ historyReport history next = some (bit, serial)) ∨
      ∃ pair ∈ historyExecutions history, pair.1.stage = next := by
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
          | .test level _ => P.endpointTestingAction N K level seed history stage) = .advance next at ha
        cases he : (Parameters.menuEntryAt table (N - stage.val) (P.menuEntryTools N K history stage)).action with
        | finish => simp only [he] at ha; cases ha
        | abandon => simp only [he] at ha; cases ha
        | test level bad =>
          simp only [he] at ha
          exact (endpointTestingAction_ne_advance P N K level seed history stage next ha).elim
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
              have hs : stage = next := Action.advance.inj ha
              have hb : bit = truth := by simpa only [beq_iff_eq] using hbit
              subst next
              refine Or.inl ⟨bit, reportedSerial, ?_, ?_⟩
              · simp only [historyWritten, hw, Option.map_some]
              · simpa only [hb] using hr
            · rw [ite_eq_right hbit] at ha
              change (match (Parameters.menuEntryAt table (N - stage.val) (P.menuEntryTools N K history stage)).action with
                | .test _ .repair => P.menuRepairAction N K history stage
                | _ => Action.abandon) = .advance next at ha
              cases he : (Parameters.menuEntryAt table (N - stage.val) (P.menuEntryTools N K history stage)).action with
              | finish => simp only [he] at ha; cases ha
              | abandon => simp only [he] at ha; cases ha
              | test level bad =>
                simp only [he] at ha
                cases bad with
                | abandon => cases ha
                | repair => exact Or.inr (menuRepairAction_advance_spec P N K history stage next ha).2
    · rw [dite_eq_right hc] at ha
      split_ifs at ha

end PDMenu
