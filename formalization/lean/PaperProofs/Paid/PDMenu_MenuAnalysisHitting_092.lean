module

public import PaperProofs.Paid.PDMenu_MenuAnalysisEndpoint_086
public import PaperProofs.Paid.PDMenu_MenuLiteralHitting_064

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu

open PaperProofs.Paid

def menuAnalysisBSCTape (P : Parameters) (tape : P.experiment.Tape) : P.binarySymmetric.experiment.Tape := tape

theorem menuAnalysisTest_positive_stop_eq (P : Parameters) (level : ℕ) (hlevel : level ≠ 0)
    (seed : Bool) (tape : P.experiment.Tape) :
    (menuAnalysisTest P level).rule.stop seed tape =
      (P.binarySymmetric.symmetricHittingTest level).rule.stop () (menuAnalysisBSCTape P tape) := by
  have ht : P.binarySymmetric.rocEndpointTest level = P.binarySymmetric.hittingTestOnBool level :=
    ite_eq_right hlevel
  exact congrArg (fun test : P.binarySymmetric.experiment.AdmissibleRule Bool =>
    test.rule.stop seed (menuAnalysisBSCTape P tape)) ht

theorem menuAnalysisTest_positive_decision_eq (P : Parameters) (level : ℕ) (hlevel : level ≠ 0)
    (seed : Bool) (tape : P.experiment.Tape) :
    (menuAnalysisTest P level).rule.decision seed tape =
      (P.binarySymmetric.symmetricHittingTest level).rule.decision () (menuAnalysisBSCTape P tape) := by
  have ht : P.binarySymmetric.rocEndpointTest level = P.binarySymmetric.hittingTestOnBool level :=
    ite_eq_right hlevel
  exact congrArg (fun test : P.binarySymmetric.experiment.AdmissibleRule Bool =>
    test.rule.decision seed (menuAnalysisBSCTape P tape)) ht

theorem menuAnalysisTest_stop_le_iff_positive (P : Parameters) (level : ℕ) (hlevel : level ≠ 0)
    (seed : Bool) (tape : P.experiment.Tape) (reviews : ℕ) :
    (menuAnalysisTest P level).rule.stop seed tape ≤ reviews ↔
      ∃ j ≤ reviews, level ≤ (Parameters.menuWordScore (List.ofFn (fun i : Fin j => (tape i.val).val))).natAbs := by
  rw [menuAnalysisTest_positive_stop_eq P level hlevel seed tape]
  exact menuScore_hitting_stop_le P.binarySymmetric level (menuAnalysisBSCTape P tape) reviews

theorem menuAnalysisTest_stop_eq_iff_positive (P : Parameters) (level : ℕ) (hlevel : level ≠ 0)
    (seed : Bool) (tape : P.experiment.Tape) (reviews : ℕ) :
    (menuAnalysisTest P level).rule.stop seed tape = reviews ↔
      level ≤ (Parameters.menuWordScore (List.ofFn (fun i : Fin reviews => (tape i.val).val))).natAbs ∧
      ∀ j < reviews, (Parameters.menuWordScore (List.ofFn (fun i : Fin j => (tape i.val).val))).natAbs < level := by
  rw [menuAnalysisTest_positive_stop_eq P level hlevel seed tape]
  exact menuScore_hitting_stop_eq P.binarySymmetric level (menuAnalysisBSCTape P tape) reviews

theorem menuAnalysisTest_finite_decision_positive (P : Parameters) (level : ℕ) (hlevel : level ≠ 0)
    (seed : Bool) (tape : P.experiment.Tape) (reviews : ℕ)
    (hs : (menuAnalysisTest P level).rule.stop seed tape = reviews) :
    (menuAnalysisTest P level).rule.decision seed tape =
      decide (0 ≤ Parameters.menuWordScore (List.ofFn (fun i : Fin reviews => (tape i.val).val))) := by
  have hs' : (P.binarySymmetric.symmetricHittingTest level).rule.stop () (menuAnalysisBSCTape P tape) = reviews :=
    (menuAnalysisTest_positive_stop_eq P level hlevel seed tape).symm.trans hs
  rw [menuAnalysisTest_positive_decision_eq P level hlevel seed tape]
  exact menuScore_hitting_decision P.binarySymmetric level (menuAnalysisBSCTape P tape) reviews hs'

end PDMenu
