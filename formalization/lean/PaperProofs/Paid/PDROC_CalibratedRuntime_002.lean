module

public import PaperProofs.Paid.PDROC_CalibratedRuntime_001
public import PaperProofs.Paid.PDMenu_MenuWrittenFrame_097
public import PaperProofs.Paid.PDMenu_MenuFramedTesting_091

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.CalibratedRuntime

/-- The fixed-table branch of the original guarded calibrated state rule. -/
def menuRule (P : Parameters) (table : MenuTable) :
    PolicyRule P.sharedInstance P.CalibratedMenuSeed :=
  searchGuardRule (P.calibratedMenuCandidate table)

theorem menuRule_legal (P : Parameters) (table : MenuTable) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract P.sharedInstance) (hearly : C.reporting = .early)
    (accounting : NormalAccounting P.sharedInstance) :
    LegalRule (P.input fee hfee) C .uncapped accounting (menuRule P table) :=
  searchGuardRule_uncapped_legal (P.input fee hfee) C hearly accounting (P.calibratedMenuCandidate table)

/-- The one initial bit selects an entire stored table once. -/
def selectedTable (state : MultiplierState) (selector : Bool) : MenuTable :=
  match state with
  | .exact solution => solution.table
  | .bracket lower upper => if selector then lower.table else upper.table

theorem calibratedStateRule_eq_menuRule (P : Parameters) (state : MultiplierState)
    (seed : P.CalibratedSearchSeed) (history : List (VisibleEvent P.sharedInstance)) :
    P.calibratedStateRule state seed history = menuRule P (selectedTable state seed.1) seed.2 history := by
  cases state <;> rfl

theorem calibratedStateRun_eq_menuRun (P : Parameters) (state : MultiplierState)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract P.sharedInstance) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance)
    (sample : P.CalibratedSearchSeed × (P.input fee hfee).World) (clock : ℕ) :
    run (P.input fee hfee) C mode accounting (P.calibratedStateRule state) sample clock =
      run (P.input fee hfee) C mode accounting (menuRule P (selectedTable state sample.1.1))
        (sample.1.2, sample.2) clock :=
  searchRun_seed_rule_eq (P.input fee hfee) C mode accounting _ _ sample.1 sample.1.2
    (calibratedStateRule_eq_menuRule P state sample.1) sample.2 clock

theorem calibratedTestingAction_allowed (P : Parameters) (level : ℕ) (seed : P.CalibratedMenuSeed)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage)
    (hc : historyCursor history = stage.val) (hw : historyWrite history stage = none) :
    historyAllowsAction history (P.calibratedTestingAction level seed history stage) := by
  have hopen : historyWritten history stage = none := by
    simp only [historyWritten, hw, Option.map_none]
  unfold calibratedTestingAction
  split
  · exact ⟨hc, hopen⟩
  · split
    · split
      · with_unfolding_all dsimp only [cappedTestingAction]
        with_unfolding_all split
        · with_unfolding_all split <;> exact ⟨hc, hopen⟩
        · trivial
      · exact ⟨hc, hopen⟩
    · trivial

/-- Review packets change neither the selected entry nor the original
visible guard, so this is a literal operational identity. -/
theorem menuRule_reviewFrame (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (stage : P.sharedInstance.Stage)
    (tape : ((P.input fee hfee).experiment stage).Tape)
    (before : List (VisibleEvent P.sharedInstance)) (seed : P.CalibratedMenuSeed)
    (reviews level tools : ℕ) (bad : MenuBadAction)
    (hh : historyHalted before = false) (hc : historyCursor before = stage.val)
    (hw : historyWrite before stage = none)
    (hk : P.menuEntryTools P.certificate.stages P.tools before stage = tools)
    (ha : (menuEntryAt table (P.certificate.stages - stage.val) tools).action = .test level bad) :
    menuRule P table seed (before ++ headReviewHistory (P.input fee hfee) stage tape reviews) =
      P.calibratedTestingAction level seed
        (before ++ headReviewHistory (P.input fee hfee) stage tape reviews) stage := by
  let history := before ++ headReviewHistory (P.input fee hfee) stage tape reviews
  have hhalt : historyHalted history = false := (PDMenu.menuReviewFrame_halted _ stage tape reviews before).trans hh
  have hcursor : historyCursor history = stage.val := (PDMenu.menuReviewFrame_cursor _ stage tape reviews before).trans hc
  have hwrite : historyWrite history stage = none := (PDMenu.menuReviewFrame_write _ stage tape reviews before).trans hw
  have htools : P.menuEntryTools P.certificate.stages P.tools history stage = tools :=
    (PDMenu.menuReviewFrame_entryTools P P.certificate.stages P.tools fee hfee stage tape reviews before).trans hk
  have hlt : historyCursor history < P.certificate.stages := by
    rw [hcursor]
    simpa [sharedInstance] using stage.isLt
  have hstage : (⟨historyCursor history, by simpa [sharedInstance] using hlt⟩ : P.sharedInstance.Stage) = stage :=
    Fin.ext hcursor
  have hcandidate : P.calibratedMenuCandidate table seed history = P.calibratedTestingAction level seed history stage := by
    simp only [calibratedMenuCandidate, hhalt, Bool.false_eq_true, ite_false, dite_eq_left hlt,
      hstage, hwrite, htools]
    rw [hcursor, ha]
  change (if historyAllowsAction history (P.calibratedMenuCandidate table seed history)
    then P.calibratedMenuCandidate table seed history else .abandon) = _
  rw [hcandidate]
  exact ite_eq_left (calibratedTestingAction_allowed P level seed history stage hcursor hwrite)

/-- Once the current port is written, the calibrated candidate is the
literal original menu candidate on the original fair-stage-bit seed. -/
theorem menuCandidate_written_eq_original (P : Parameters) (table : MenuTable)
    (seed : P.CalibratedMenuSeed) (history : List (VisibleEvent P.sharedInstance))
    (stage : P.sharedInstance.Stage) (bit : Bool) (serial : ℕ)
    (hc : historyCursor history = stage.val)
    (hw : historyWrite history stage = some (bit, serial)) :
    P.calibratedMenuCandidate table seed history =
      P.menuCandidateAction P.certificate.stages P.tools table seed.1 history := by
  have hlt : historyCursor history < P.certificate.stages := by
    rw [hc]
    simpa [sharedInstance] using stage.isLt
  have hs : (⟨historyCursor history, by simpa [sharedInstance] using hlt⟩ : P.sharedInstance.Stage) = stage :=
    Fin.ext hc
  have hltOld : @historyCursor (freshInstance P.certificate.stages P.tools) history <
      P.certificate.stages := hlt
  have hsOld : (⟨@historyCursor (freshInstance P.certificate.stages P.tools) history,
      by simpa [freshInstance] using hltOld⟩ :
      (freshInstance P.certificate.stages P.tools).Stage) = stage := Fin.ext hc
  have hwOld : @historyWrite (freshInstance P.certificate.stages P.tools) history stage =
      some (bit, serial) := hw
  with_unfolding_all simp only [calibratedMenuCandidate, menuCandidateAction,
    dite_eq_left hlt, dite_eq_left hltOld, hs, hsOld, hw, hwOld]
  with_unfolding_all rfl

theorem menuRule_written_eq_original (P : Parameters) (table : MenuTable)
    (seed : P.CalibratedMenuSeed) (history : List (VisibleEvent P.sharedInstance))
    (stage : P.sharedInstance.Stage) (bit : Bool) (serial : ℕ)
    (hc : historyCursor history = stage.val)
    (hw : historyWrite history stage = some (bit, serial)) :
    menuRule P table seed history =
      P.compiledMenuRule P.certificate.stages P.tools table seed.1 history := by
  have heq := menuCandidate_written_eq_original P table seed history stage bit serial hc hw
  exact congrArg (fun action : Action P.sharedInstance =>
    if historyAllowsAction history action then action else .abandon) heq

/-- The existing original early-report/physical-repair frame applies to
any actual calibrated prefix, without an old-menu prefix hypothesis. -/
theorem menuRule_writtenFrame (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract P.sharedInstance) (hearly : C.reporting = .early)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type*}
    (rule : PolicyRule P.sharedInstance Seed) (seed : Seed)
    (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {clock : ℕ} {state : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C .uncapped accounting rule seed truth tapes clock state)
    (menuSeed : P.CalibratedMenuSeed) (stage : P.sharedInstance.Stage) (bit : Bool)
    (hactive : state.halted = false) (hcursor : state.cursor = stage.val)
    (hbit : state.ledger.written stage = some bit) :
    menuRule P table menuSeed state.history =
      if bit == state.ledger.truth stage then .advance stage else
        match (menuEntryAt table (P.certificate.stages - stage.val)
          (P.menuEntryTools P.certificate.stages P.tools state.history stage)).action with
        | .test _ .repair => P.menuRepairAction P.certificate.stages P.tools state.history stage
        | _ => .abandon := by
  have hc : historyCursor state.history = stage.val :=
    (prefix_historyCursor (P.input fee hfee) C .uncapped accounting rule seed truth tapes hp).trans hcursor
  have hw : historyWrite state.history stage = some (bit, state.ledger.writeSerial stage) := by
    rw [prefix_historyWrite (P.input fee hfee) C .uncapped accounting rule seed truth tapes hp stage, hbit]
    rfl
  rw [menuRule_written_eq_original P table menuSeed state.history stage bit _ hc hw]
  exact PDMenu.compiledMenuRule_writtenFrame P P.certificate.stages P.tools table fee hfee C hearly accounting
    rule seed truth tapes hp menuSeed.1 stage bit hactive hcursor hbit

end PDROC.CalibratedRuntime
