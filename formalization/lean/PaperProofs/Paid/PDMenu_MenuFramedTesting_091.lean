module

public import PaperProofs.Paid.PDMenu_MenuReviewFrame_090

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- Literal testing behavior after an arbitrary visible entry prefix.
All assumptions here are visible history data; real entry facts are proved
separately, not inserted as native Policy performance fields. -/
theorem compiledMenuRule_reviewFrame (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (stage : (freshInstance N K).Stage)
    (tape : ((P.freshInput N K fee hfee).experiment stage).Tape)
    (before : List (VisibleEvent (freshInstance N K))) (seed : MenuSeed N K) (reviews level tools : ℕ) (bad : MenuBadAction)
    (hh : historyHalted before = false) (hc : historyCursor before = stage.val)
    (hw : historyWrite before stage = none) (hk : P.menuEntryTools N K before stage = tools)
    (ha : (Parameters.menuEntryAt table (N - stage.val) tools).action = .test level bad) :
    P.compiledMenuRule N K table seed (before ++ headReviewHistory (P.freshInput N K fee hfee) stage tape reviews) =
      P.endpointTestingAction N K level seed (before ++ headReviewHistory (P.freshInput N K fee hfee) stage tape reviews) stage := by
  classical
  let history := before ++ headReviewHistory (P.freshInput N K fee hfee) stage tape reviews
  have hhalt : historyHalted history = false := (menuReviewFrame_halted _ stage tape reviews before).trans hh
  have hcursor : historyCursor history = stage.val := (menuReviewFrame_cursor _ stage tape reviews before).trans hc
  have hwrite : historyWrite history stage = none := (menuReviewFrame_write _ stage tape reviews before).trans hw
  have htools : P.menuEntryTools N K history stage = tools :=
    (menuReviewFrame_entryTools P N K fee hfee stage tape reviews before).trans hk
  have hlt : historyCursor history < N := by
    rw [hcursor]
    simpa [freshInstance] using stage.isLt
  have hstage : (⟨historyCursor history, by simpa [freshInstance] using hlt⟩ : (freshInstance N K).Stage) = stage :=
    Fin.ext hcursor
  have hcandidate : P.menuCandidateAction N K table seed history = P.endpointTestingAction N K level seed history stage := by
    simp only [Parameters.menuCandidateAction, hhalt, Bool.false_eq_true, ite_false, dite_eq_left hlt, hstage,
      hwrite, htools]
    rw [hcursor, ha]
  have hopen : historyWritten history stage = none := by simp only [historyWritten, hwrite, Option.map_none]
  have hallow : historyAllowsAction history (P.endpointTestingAction N K level seed history stage) := by
    dsimp only [Parameters.endpointTestingAction]
    split_ifs <;> first | exact ⟨hcursor, hopen⟩ | trivial
  change (if historyAllowsAction history (P.menuCandidateAction N K table seed history)
    then P.menuCandidateAction N K table seed history else .abandon) = _
  rw [hcandidate]
  exact ite_eq_left hallow

theorem endpointTestingAction_reviewFrame_positive (P : Parameters) (N K : ℕ) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : (freshInstance N K).Stage) (tape : ((P.freshInput N K fee hfee).experiment stage).Tape)
    (before : List (VisibleEvent (freshInstance N K))) (seed : MenuSeed N K) (reviews level : ℕ)
    (hlevel : level ≠ 0) (hobs : historyObservations before stage = []) :
    P.endpointTestingAction N K level seed (before ++ headReviewHistory (P.freshInput N K fee hfee) stage tape reviews) stage =
      if level ≤ (Parameters.menuWordScore (List.ofFn (fun i : Fin reviews => (tape i.val).val))).natAbs then
        .write stage (decide (0 ≤ Parameters.menuWordScore (List.ofFn (fun i : Fin reviews => (tape i.val).val))))
      else .review stage := by
  have hletters : (List.ofFn (fun i : Fin reviews => (tape i.val).val)).all (fun symbol => symbol < 2) = true := by
    apply List.all_eq_true.mpr
    intro symbol hs
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
    have halphabet : ((P.freshInput N K fee hfee).experiment stage).alphabetSize = 2 := rfl
    exact decide_eq_true ((tape i.val).isLt.trans_eq halphabet)
  have hword : historyObservations (before ++ headReviewHistory (P.freshInput N K fee hfee) stage tape reviews) stage =
      List.ofFn (fun i : Fin reviews => (tape i.val).val) := by
    rw [menuReviewFrame_observations, hobs, List.nil_append]
  simp only [Parameters.endpointTestingAction, ite_eq_right hlevel, hword, hletters, ite_true]

end PDMenu
