module

public import PaperProofs.Paid.PDMenu_MenuPathSummary_087

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu

open PaperProofs.Paid

theorem menuPathSummary_test_correct (P : Parameters) (table : MenuTable) (n k level reviews : ℕ)
    (bad : MenuBadAction) (seed : MenuAnalysisSeed (n + 1)) (world : MenuAnalysisWorld P (n + 1))
    (ha : (Parameters.menuEntryAt table (n + 1) k).action = .test level bad)
    (hstop : (menuAnalysisTest P level).rule.stop (seed 0) (world 0).2 = reviews)
    (hcorrect : (menuAnalysisTest P level).rule.decision (seed 0) (world 0).2 = (world 0).1) :
    menuPathSummary P table (n + 1) k seed world =
      let child := menuPathSummary P table n k (Fin.tail seed) (Fin.tail world)
      { child with observation := P.experiment.observationCharge reviews + child.observation } := by
  simp only [menuPathSummary, ha, hstop, ENat.natCast_ne_top, ite_false, ite_eq_left hcorrect]

theorem menuPathSummary_test_abandon (P : Parameters) (table : MenuTable) (n k level reviews : ℕ)
    (seed : MenuAnalysisSeed (n + 1)) (world : MenuAnalysisWorld P (n + 1))
    (ha : (Parameters.menuEntryAt table (n + 1) k).action = .test level .abandon)
    (hstop : (menuAnalysisTest P level).rule.stop (seed 0) (world 0).2 = reviews)
    (hwrong : (menuAnalysisTest P level).rule.decision (seed 0) (world 0).2 ≠ (world 0).1) :
    menuPathSummary P table (n + 1) k seed world =
      { menuPathAbandon with observation := P.experiment.observationCharge reviews + menuPathAbandon.observation } := by
  simp only [menuPathSummary, ha, hstop, ENat.natCast_ne_top, ite_false, ite_eq_right hwrong]

theorem menuPathSummary_test_repair (P : Parameters) (table : MenuTable) (n k level reviews : ℕ)
    (seed : MenuAnalysisSeed (n + 1)) (world : MenuAnalysisWorld P (n + 1))
    (ha : (Parameters.menuEntryAt table (n + 1) k).action = .test level .repair)
    (hstop : (menuAnalysisTest P level).rule.stop (seed 0) (world 0).2 = reviews)
    (hwrong : (menuAnalysisTest P level).rule.decision (seed 0) (world 0).2 ≠ (world 0).1)
    (hk : k ≠ 0) :
    menuPathSummary P table (n + 1) k seed world =
      let child := menuPathSummary P table n (k - 1) (Fin.tail seed) (Fin.tail world)
      { observation := P.experiment.observationCharge reviews + child.observation,
        physicalRepairs := child.physicalRepairs + 1, failure := child.failure } := by
  simp only [menuPathSummary, ha, hstop, ENat.natCast_ne_top, ite_false, ite_eq_right hwrong, ite_eq_right hk]

theorem menuPathSummary_test_no_tool (P : Parameters) (table : MenuTable) (n level reviews : ℕ)
    (seed : MenuAnalysisSeed (n + 1)) (world : MenuAnalysisWorld P (n + 1))
    (ha : (Parameters.menuEntryAt table (n + 1) 0).action = .test level .repair)
    (hstop : (menuAnalysisTest P level).rule.stop (seed 0) (world 0).2 = reviews)
    (hwrong : (menuAnalysisTest P level).rule.decision (seed 0) (world 0).2 ≠ (world 0).1) :
    menuPathSummary P table (n + 1) 0 seed world =
      { menuPathAbandon with observation := P.experiment.observationCharge reviews + menuPathAbandon.observation } := by
  simp only [menuPathSummary, ha, hstop, ENat.natCast_ne_top, ite_false, ite_eq_right hwrong, ite_true]

end PDMenu
