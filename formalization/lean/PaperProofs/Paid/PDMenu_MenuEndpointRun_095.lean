module

public import PaperProofs.Paid.PDMenu_MenuFramedEndpoint_094
public import PaperProofs.Paid.PDMenu_MenuReviewFrom_093

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- Exact review states of the original interpreter at an arbitrary real
entry clock, including every finite prefix of a nonreturning endpoint. -/
theorem compiledMenu_run_reviewFrom (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K))
    (accounting : NormalAccounting (freshInstance N K))
    (sample : MenuSeed N K × (P.freshInput N K fee hfee).World)
    (stage : (freshInstance N K).Stage) (clock : ℕ) (start : State (freshInstance N K))
    (hstart : run (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) sample clock = start)
    (hactive : start.halted = false) (hcursor : start.cursor = stage.val)
    (hport : start.ledger.written stage = none) (hzero : start.ledger.reviews stage = 0)
    (hh : historyHalted start.history = false) (hc : historyCursor start.history = stage.val)
    (hw : historyWrite start.history stage = none) (ho : historyObservations start.history stage = [])
    (level tools : ℕ) (bad : MenuBadAction)
    (hk : P.menuEntryTools N K start.history stage = tools)
    (ha : (Parameters.menuEntryAt table (N - stage.val) tools).action = .test level bad)
    (steps : ℕ)
    (hsteps : (steps : ℕ∞) ≤ (menuAnalysisTest P level).rule.stop (sample.1 stage)
      (menuOriginalTape P N K fee hfee stage (worldTapes (P.freshInput N K fee hfee) sample.2 stage))) :
    run (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) sample (clock + steps) =
        menuReviewFrom (P.freshInput N K fee hfee) accounting stage start
          (worldTapes (P.freshInput N K fee hfee) sample.2 stage) steps := by
  apply menu_run_eq_reviewFrom (P.freshInput N K fee hfee) C accounting
    (P.compiledMenuRule N K table) sample stage clock start hstart hactive hcursor hport hzero steps
  intro j hj
  apply compiledMenuRule_reviewFrame_beforeStop P N K table fee hfee stage _ start.history sample.1
    j level tools bad hh hc hw hk ha ho
  have hj' : (j : ℕ∞) < (steps : ℕ∞) := by exact_mod_cast hj
  exact hj'.trans_le hsteps

/-- The real write/report state following the real review ledger, with
the same original normal accounting and all earlier obligations retained. -/
noncomputable def menuWrittenFrom {I : Instance} (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (stage : I.Stage) (start : State I)
    (tape : (input.experiment stage).Tape) (reviews : ℕ) (bit : Bool) : State I :=
  let state := menuReviewFrom input accounting stage start tape reviews
  record accounting state (.write stage bit) (writeResponses C state stage bit)
    (reportedWriteLedger C state stage bit) state.cursor false

theorem compiledMenu_run_writtenFrom (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K))
    (accounting : NormalAccounting (freshInstance N K))
    (sample : MenuSeed N K × (P.freshInput N K fee hfee).World)
    (stage : (freshInstance N K).Stage) (clock : ℕ) (start : State (freshInstance N K))
    (hstart : run (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) sample clock = start)
    (hactive : start.halted = false) (hcursor : start.cursor = stage.val)
    (hport : start.ledger.written stage = none) (hzero : start.ledger.reviews stage = 0)
    (hh : historyHalted start.history = false) (hc : historyCursor start.history = stage.val)
    (hw : historyWrite start.history stage = none) (ho : historyObservations start.history stage = [])
    (level tools : ℕ) (bad : MenuBadAction)
    (hk : P.menuEntryTools N K start.history stage = tools)
    (ha : (Parameters.menuEntryAt table (N - stage.val) tools).action = .test level bad)
    (reviews : ℕ)
    (hstop : (menuAnalysisTest P level).rule.stop (sample.1 stage)
      (menuOriginalTape P N K fee hfee stage (worldTapes (P.freshInput N K fee hfee) sample.2 stage)) = reviews) :
    run (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) sample (clock + reviews + 1) =
        menuWrittenFrom (P.freshInput N K fee hfee) C accounting stage start
          (worldTapes (P.freshInput N K fee hfee) sample.2 stage) reviews
          ((menuAnalysisTest P level).rule.decision (sample.1 stage)
            (menuOriginalTape P N K fee hfee stage (worldTapes (P.freshInput N K fee hfee) sample.2 stage))) := by
  let input := P.freshInput N K fee hfee
  let tape := worldTapes input sample.2 stage
  let bit := (menuAnalysisTest P level).rule.decision (sample.1 stage)
    (menuOriginalTape P N K fee hfee stage tape)
  let state := menuReviewFrom input accounting stage start tape reviews
  have hr : run input C .uncapped accounting (P.compiledMenuRule N K table) sample (clock + reviews) = state :=
    compiledMenu_run_reviewFrom P N K table fee hfee C accounting sample stage clock start hstart
      hactive hcursor hport hzero hh hc hw ho level tools bad hk ha reviews hstop.ge
  have hstateActive : state.halted = false := menuReviewFrom_active input accounting stage start tape hactive reviews
  have hstateCursor : state.cursor = stage.val :=
    (menuReviewFrom_cursor input accounting stage start tape reviews).trans hcursor
  have hstatePort : state.ledger.written stage = none :=
    (congrFun (menuReviewFrom_written input accounting stage start tape reviews) stage).trans hport
  have haction : P.compiledMenuRule N K table sample.1 state.history = .write stage bit := by
    rw [menuReviewFrom_history]
    exact compiledMenuRule_reviewFrame_atStop P N K table fee hfee stage tape start.history sample.1
      reviews level tools bad hh hc hw hk ha ho hstop
  apply run_succ_of_step input C .uncapped accounting (P.compiledMenuRule N K table) sample (clock + reviews) _
  · rw [hr]
    exact hstateActive
  · rw [hr, haction]
    exact Step.write state stage bit ⟨hstateActive, hstateCursor⟩ hstatePort (.inl rfl)

end PDMenu
