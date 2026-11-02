module

public import PaperProofs.Paid.MenuCompiler

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- Only earlier physical executions affect the original stage-entry
snapshot. Current allocation, write/report and execution packets do not. -/
theorem menuEntryTools_append_no_past_execution (P : Parameters) (N K : ℕ)
    (history packet : List (VisibleEvent (freshInstance N K))) (stage : (freshInstance N K).Stage)
    (hnopast : ∀ pair ∈ historyExecutions packet, ¬ pair.1.stage.val < stage.val) :
    P.menuEntryTools N K (history ++ packet) stage = P.menuEntryTools N K history stage := by
  have he : historyExecutions (history ++ packet) = historyExecutions history ++ historyExecutions packet := by
    simp only [historyExecutions, List.filterMap_append]
  have hp : (historyExecutions packet).filter (fun pair => pair.1.stage.val < stage.val) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro pair hpair
    simpa only [decide_eq_true_eq] using hnopast pair hpair
  simp only [Parameters.menuEntryTools, he, List.filter_append, hp, List.append_nil]

theorem menuEntryTools_append_no_execution (P : Parameters) (N K : ℕ)
    (history packet : List (VisibleEvent (freshInstance N K))) (stage : (freshInstance N K).Stage)
    (hnone : historyExecutions packet = []) :
    P.menuEntryTools N K (history ++ packet) stage = P.menuEntryTools N K history stage := by
  apply menuEntryTools_append_no_past_execution
  intro pair hpair
  rw [hnone] at hpair
  cases hpair

theorem menuEntryTools_append_event_no_execution (P : Parameters) (N K : ℕ)
    (history : List (VisibleEvent (freshInstance N K))) (stage : (freshInstance N K).Stage)
    (event : VisibleEvent (freshInstance N K)) (hnone : eventExecution event = none) :
    P.menuEntryTools N K (history ++ [event]) stage = P.menuEntryTools N K history stage := by
  apply menuEntryTools_append_no_execution
  simp only [historyExecutions, List.filterMap_cons, hnone, List.filterMap_nil]

theorem menuEntryTools_append_current_execution (P : Parameters) (N K : ℕ)
    (history : List (VisibleEvent (freshInstance N K))) (stage : (freshInstance N K).Stage)
    (handle : MismatchHandle (freshInstance N K)) (tool : (freshInstance N K).Tool) (hs : handle.stage = stage) :
    P.menuEntryTools N K (history ++ [.executed handle tool]) stage = P.menuEntryTools N K history stage := by
  apply menuEntryTools_append_no_past_execution
  intro pair hpair
  have heq : pair = (handle, tool) := by
    simpa only [historyExecutions, List.filterMap_cons, eventExecution, List.filterMap_nil, List.mem_singleton] using hpair
  subst pair
  exact (congrArg Fin.val hs) ▸ Nat.lt_irrefl stage.val

theorem menuEntryTools_append_writeResponses (P : Parameters) (N K : ℕ)
    (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (state : State (freshInstance N K)) (stage : (freshInstance N K).Stage) (bit : Bool) :
    P.menuEntryTools N K (state.history ++ writeResponses C state stage bit) stage =
      P.menuEntryTools N K state.history stage := by
  apply menuEntryTools_append_no_execution
  simp [historyExecutions, writeResponses, hearly, eventExecution]

end PDMenu
