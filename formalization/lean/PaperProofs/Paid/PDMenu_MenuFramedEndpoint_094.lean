module

public import PaperProofs.Paid.PDMenu_MenuFramedTesting_091
public import PaperProofs.Paid.PDMenu_MenuAnalysisHitting_092

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- The native input and original statistical experiment share the literal
review tape. This typed view avoids rewriting across experiment aliases. -/
def menuOriginalTape (P : Parameters) (N K : ℕ) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : (freshInstance N K).Stage)
    (tape : ((P.freshInput N K fee hfee).experiment stage).Tape) : P.experiment.Tape := tape

theorem compiledMenuRule_reviewFrame_beforeStop (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (stage : (freshInstance N K).Stage)
    (tape : ((P.freshInput N K fee hfee).experiment stage).Tape)
    (before : List (VisibleEvent (freshInstance N K))) (seed : MenuSeed N K)
    (reviews level tools : ℕ) (bad : MenuBadAction)
    (hh : historyHalted before = false) (hc : historyCursor before = stage.val)
    (hw : historyWrite before stage = none) (hk : P.menuEntryTools N K before stage = tools)
    (ha : (Parameters.menuEntryAt table (N - stage.val) tools).action = .test level bad)
    (ho : historyObservations before stage = [])
    (hr : (reviews : ℕ∞) < (menuAnalysisTest P level).rule.stop (seed stage)
      (menuOriginalTape P N K fee hfee stage tape)) :
    P.compiledMenuRule N K table seed
      (before ++ headReviewHistory (P.freshInput N K fee hfee) stage tape reviews) = .review stage := by
  have hlevel : level ≠ 0 := by
    intro hz
    rw [hz, menuAnalysisTest_zero_stop] at hr
    exact (not_lt_zero hr).elim
  rw [compiledMenuRule_reviewFrame P N K table fee hfee stage tape before seed reviews level tools bad hh hc hw hk ha,
    endpointTestingAction_reviewFrame_positive P N K fee hfee stage tape before seed reviews level hlevel ho]
  apply ite_eq_right
  intro hhit
  have hle := (menuAnalysisTest_stop_le_iff_positive P level hlevel (seed stage)
    (menuOriginalTape P N K fee hfee stage tape) reviews).mpr ⟨reviews, le_rfl, hhit⟩
  exact (not_le_of_gt hr) hle

theorem compiledMenuRule_reviewFrame_atStop (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (stage : (freshInstance N K).Stage)
    (tape : ((P.freshInput N K fee hfee).experiment stage).Tape)
    (before : List (VisibleEvent (freshInstance N K))) (seed : MenuSeed N K)
    (reviews level tools : ℕ) (bad : MenuBadAction)
    (hh : historyHalted before = false) (hc : historyCursor before = stage.val)
    (hw : historyWrite before stage = none) (hk : P.menuEntryTools N K before stage = tools)
    (ha : (Parameters.menuEntryAt table (N - stage.val) tools).action = .test level bad)
    (ho : historyObservations before stage = [])
    (hr : (menuAnalysisTest P level).rule.stop (seed stage)
      (menuOriginalTape P N K fee hfee stage tape) = reviews) :
    P.compiledMenuRule N K table seed
      (before ++ headReviewHistory (P.freshInput N K fee hfee) stage tape reviews) =
        .write stage ((menuAnalysisTest P level).rule.decision (seed stage)
          (menuOriginalTape P N K fee hfee stage tape)) := by
  rw [compiledMenuRule_reviewFrame P N K table fee hfee stage tape before seed reviews level tools bad hh hc hw hk ha]
  by_cases hz : level = 0
  · subst level
    rw [Parameters.endpointTestingAction_zero, menuAnalysisTest_zero_decision]
  · rw [endpointTestingAction_reviewFrame_positive P N K fee hfee stage tape before seed reviews level hz ho]
    have hhit := ((menuAnalysisTest_stop_eq_iff_positive P level hz (seed stage)
      (menuOriginalTape P N K fee hfee stage tape) reviews).mp hr).1
    have hhit' : level ≤ (Parameters.menuWordScore (List.ofFn (fun i : Fin reviews => (tape i.val).val))).natAbs := hhit
    rw [ite_eq_left hhit']
    exact congrArg (Action.write stage)
      (menuAnalysisTest_finite_decision_positive P level hz (seed stage)
        (menuOriginalTape P N K fee hfee stage tape) reviews hr).symm

end PDMenu
