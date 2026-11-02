module

public import PaperProofs.Paid.PDROC_CalibratedRuntime_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters
open PDROC.CalibratedRuntime

namespace PDROC.CalibratedIdeal

/-- Forgetting the enriched visited-stage trace preserves the original
analysis record on every path, including the infinite-stop branch. -/
theorem idealSummary_forget (P : Parameters) (table : MenuTable) (n k : ℕ)
    (seed : PDMenu.MenuAnalysisSeed n) (world : PDMenu.MenuAnalysisWorld P n) :
    (pathSummary P (idealFamily P) table n k seed world).observation =
      (PDMenu.menuPathSummary P table n k seed world).observation ∧
    (pathSummary P (idealFamily P) table n k seed world).failure =
      (PDMenu.menuPathSummary P table n k seed world).failure := by
  classical
  induction n generalizing k with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      cases ha : (menuEntryAt table (n + 1) k).action with
      | finish =>
          simp only [pathSummary, PDMenu.menuPathSummary, ha, abandonRecord,
            PDMenu.menuPathAbandon, and_self]
      | abandon =>
          simp only [pathSummary, PDMenu.menuPathSummary, ha, abandonRecord,
            PDMenu.menuPathAbandon, and_self]
      | test level bad =>
          simp only [pathSummary, PDMenu.menuPathSummary, ha, idealFamily]
          by_cases hs : (PDMenu.menuAnalysisTest P level).rule.stop (seed 0) (world 0).2 = ⊤
          · simp only [ite_eq_left hs]
            exact ⟨rfl, rfl⟩
          · simp only [ite_eq_right hs]
            by_cases hc : (PDMenu.menuAnalysisTest P level).rule.decision (seed 0) (world 0).2 = (world 0).1
            · simp only [ite_eq_left hc]
              have hi := ih k (Fin.tail seed) (Fin.tail world)
              exact ⟨congrArg (fun charge => _ + charge) hi.1, hi.2⟩
            · simp only [ite_eq_right hc]
              cases bad with
              | abandon => exact ⟨rfl, rfl⟩
              | repair =>
                  by_cases hk : k = 0
                  · simp only [ite_eq_left hk]
                    exact ⟨rfl, rfl⟩
                  · simp only [ite_eq_right hk]
                    have hi := ih (k - 1) (Fin.tail seed) (Fin.tail world)
                    exact ⟨congrArg (fun charge => _ + charge) hi.1, hi.2⟩

theorem idealSummary_observation (P : Parameters) (table : MenuTable) (n k : ℕ)
    (seed : PDMenu.MenuAnalysisSeed n) (world : PDMenu.MenuAnalysisWorld P n) :
    (pathSummary P (idealFamily P) table n k seed world).observation =
      (PDMenu.menuPathSummary P table n k seed world).observation :=
  (idealSummary_forget P table n k seed world).1

theorem idealSummary_failure (P : Parameters) (table : MenuTable) (n k : ℕ)
    (seed : PDMenu.MenuAnalysisSeed n) (world : PDMenu.MenuAnalysisWorld P n) :
    (pathSummary P (idealFamily P) table n k seed world).failure =
      (PDMenu.menuPathSummary P table n k seed world).failure :=
  (idealSummary_forget P table n k seed world).2

end PDROC.CalibratedIdeal
