module

public import PaperProofs.Retained.Controller
public import Mathlib.Data.List.FinRange

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetBudgetReplay117

open Common Common.Native

variable {I : Instance}

theorem replayStep_congr (left right : List (VisibleEvent I)) (cache : BudgetCache I) (stage : I.Stage)
    (h : reportedError left stage = reportedError right stage) :
    replayBudgetStep I left cache stage = replayBudgetStep I right cache stage := by
  unfold replayBudgetStep
  rw [h]

private theorem fold_congr (left right : List (VisibleEvent I)) (stages : List I.Stage)
    (h : ∀ stage ∈ stages, reportedError left stage = reportedError right stage) (cache : BudgetCache I) :
    stages.foldlM (replayBudgetStep I left) cache = stages.foldlM (replayBudgetStep I right) cache := by
  induction stages generalizing cache with
  | nil => rfl
  | cons stage rest ih =>
    rw [List.foldlM_cons, List.foldlM_cons, replayStep_congr left right cache stage (h stage (List.mem_cons_self))]
    cases hs : replayBudgetStep I right cache stage with
    | none => rfl
    | some next =>
      exact ih (fun child hc => h child (List.mem_cons_of_mem stage hc)) next

/-- The real budget replay reads exactly the already-reported prefix;
current-stage observations and an unprocessed current report cannot alter it. -/
theorem replayBudget_congr (budget : ℚ) (left right : List (VisibleEvent I)) (next : ℕ)
    (h : ∀ stage : I.Stage, stage.val < next → reportedError left stage = reportedError right stage) :
    replayBudget I budget left next = replayBudget I budget right next := by
  apply fold_congr
  intro stage hs
  apply h stage
  have hm := (List.mem_take_iff_idxOf_lt (List.mem_finRange stage)).mp hs
  simpa only [List.idxOf_finRange] using hm

/-- The genuine one-stage budget update is exactly the next original fold
step, with its actual reported bit, retained old set and rational risk. -/
theorem replayBudget_succ (budget : ℚ) (history : List (VisibleEvent I)) (stage : I.Stage) :
    replayBudget I budget history (stage.val + 1) =
      (replayBudget I budget history stage.val).bind (fun cache => replayBudgetStep I history cache stage) := by
  have hi : stage.val < (List.finRange I.compatibility.length).length := by
    rw [List.length_finRange]
    exact stage.isLt
  have hget : (List.finRange I.compatibility.length)[stage.val]'hi = stage := by
    rw [List.getElem_finRange]
    apply Fin.ext
    rfl
  have ht : (List.finRange I.compatibility.length).take (stage.val + 1) =
      (List.finRange I.compatibility.length).take stage.val ++ [stage] := by
    rw [List.take_succ_eq_append_getElem hi, hget]
  unfold replayBudget
  change ((List.finRange I.compatibility.length).take (stage.val + 1)).foldlM (replayBudgetStep I history) _ =
    (((List.finRange I.compatibility.length).take stage.val).foldlM (replayBudgetStep I history) _).bind _
  rw [ht, List.foldlM_append]
  simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
  simp only [Option.bind_eq_bind]

end PaperProofs.Retained.PRetBudgetReplay117
