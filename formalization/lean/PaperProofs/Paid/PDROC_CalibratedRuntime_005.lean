module

public import PaperProofs.Paid.PDROC_CalibratedRuntime_003
public import PaperProofs.Paid.PDROC_CalibratedRuntime_004
public import PaperProofs.Paid.PDMenu_MenuEntryRun_096
public import PaperProofs.Paid.PDMenu_MenuWrittenEntryRecords_119

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters
open PDMenu

namespace PDROC.CalibratedRuntime

/-- Exact review states of the original interpreter at an arbitrary real
entry clock, including every finite prefix of a nonreturning endpoint. -/
theorem menu_run_reviewFrom (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance P.certificate.stages P.tools))
    (accounting : NormalAccounting (freshInstance P.certificate.stages P.tools))
    (sample : P.CalibratedMenuSeed × (P.freshInput P.certificate.stages P.tools fee hfee).World)
    (stage : (freshInstance P.certificate.stages P.tools).Stage) (clock : ℕ) (start : State (freshInstance P.certificate.stages P.tools))
    (hstart : run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
      (menuRule P table) sample clock = start)
    (hactive : start.halted = false) (hcursor : start.cursor = stage.val)
    (hport : start.ledger.written stage = none) (hzero : start.ledger.reviews stage = 0)
    (hh : historyHalted start.history = false) (hc : historyCursor start.history = stage.val)
    (hw : historyWrite start.history stage = none) (ho : historyObservations start.history stage = [])
    (level tools : ℕ) (bad : MenuBadAction) (valid : level ≤ P.certificate.M)
    (hk : P.menuEntryTools P.certificate.stages P.tools start.history stage = tools)
    (ha : (Parameters.menuEntryAt table (P.certificate.stages - stage.val) tools).action = .test level bad)
    (steps : ℕ)
    (hsteps : (steps : ℕ∞) ≤ (calibratedStageTest P level).rule.stop (sample.1.1 stage, sample.1.2 stage)
      (menuOriginalTape P P.certificate.stages P.tools fee hfee stage (worldTapes (P.freshInput P.certificate.stages P.tools fee hfee) sample.2 stage))) :
    run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
      (menuRule P table) sample (clock + steps) =
        menuReviewFrom (P.freshInput P.certificate.stages P.tools fee hfee) accounting stage start
          (worldTapes (P.freshInput P.certificate.stages P.tools fee hfee) sample.2 stage) steps := by
  apply menu_run_eq_reviewFrom (P.freshInput P.certificate.stages P.tools fee hfee) C accounting
    (menuRule P table) sample stage clock start hstart hactive hcursor hport hzero steps
  intro j hj
  have hj' : (j : ℕ∞) < (steps : ℕ∞) := by exact_mod_cast hj
  have hlocal := calibratedTestingAction_beforeStop P level valid sample.1 fee hfee stage
    (worldTapes (P.freshInput P.certificate.stages P.tools fee hfee) sample.2 stage) start.history j ho
    (hj'.trans_le hsteps)
  exact (menuRule_reviewFrame P table fee hfee stage
    (worldTapes (P.freshInput P.certificate.stages P.tools fee hfee) sample.2 stage)
    start.history sample.1 j level tools bad hh hc hw hk ha).trans hlocal

theorem menu_run_writtenFrom (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance P.certificate.stages P.tools))
    (accounting : NormalAccounting (freshInstance P.certificate.stages P.tools))
    (sample : P.CalibratedMenuSeed × (P.freshInput P.certificate.stages P.tools fee hfee).World)
    (stage : (freshInstance P.certificate.stages P.tools).Stage) (clock : ℕ) (start : State (freshInstance P.certificate.stages P.tools))
    (hstart : run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
      (menuRule P table) sample clock = start)
    (hactive : start.halted = false) (hcursor : start.cursor = stage.val)
    (hport : start.ledger.written stage = none) (hzero : start.ledger.reviews stage = 0)
    (hh : historyHalted start.history = false) (hc : historyCursor start.history = stage.val)
    (hw : historyWrite start.history stage = none) (ho : historyObservations start.history stage = [])
    (level tools : ℕ) (bad : MenuBadAction) (valid : level ≤ P.certificate.M)
    (hk : P.menuEntryTools P.certificate.stages P.tools start.history stage = tools)
    (ha : (Parameters.menuEntryAt table (P.certificate.stages - stage.val) tools).action = .test level bad)
    (reviews : ℕ)
    (hstop : (calibratedStageTest P level).rule.stop (sample.1.1 stage, sample.1.2 stage)
      (menuOriginalTape P P.certificate.stages P.tools fee hfee stage (worldTapes (P.freshInput P.certificate.stages P.tools fee hfee) sample.2 stage)) = reviews) :
    run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
      (menuRule P table) sample (clock + reviews + 1) =
        menuWrittenFrom (P.freshInput P.certificate.stages P.tools fee hfee) C accounting stage start
          (worldTapes (P.freshInput P.certificate.stages P.tools fee hfee) sample.2 stage) reviews
          ((calibratedStageTest P level).rule.decision (sample.1.1 stage, sample.1.2 stage)
            (menuOriginalTape P P.certificate.stages P.tools fee hfee stage (worldTapes (P.freshInput P.certificate.stages P.tools fee hfee) sample.2 stage))) := by
  let input := P.freshInput P.certificate.stages P.tools fee hfee
  let tape := worldTapes input sample.2 stage
  let bit := (calibratedStageTest P level).rule.decision (sample.1.1 stage, sample.1.2 stage)
    (menuOriginalTape P P.certificate.stages P.tools fee hfee stage tape)
  let state := menuReviewFrom input accounting stage start tape reviews
  have hr : run input C .uncapped accounting (menuRule P table) sample (clock + reviews) = state :=
    menu_run_reviewFrom P table fee hfee C accounting sample stage clock start hstart
      hactive hcursor hport hzero hh hc hw ho level tools bad valid hk ha reviews hstop.ge
  have hstateActive : state.halted = false := menuReviewFrom_active input accounting stage start tape hactive reviews
  have hstateCursor : state.cursor = stage.val :=
    (menuReviewFrom_cursor input accounting stage start tape reviews).trans hcursor
  have hstatePort : state.ledger.written stage = none :=
    (congrFun (menuReviewFrom_written input accounting stage start tape reviews) stage).trans hport
  have haction : menuRule P table sample.1 state.history = .write stage bit := by
    rw [menuReviewFrom_history]
    exact (menuRule_reviewFrame P table fee hfee stage tape start.history sample.1 reviews level tools bad hh hc hw hk ha).trans
      (calibratedTestingAction_atStop P level valid sample.1 fee hfee stage tape start.history reviews ho hstop)
  apply run_succ_of_step input C .uncapped accounting (menuRule P table) sample (clock + reviews) _
  · rw [hr]
    exact hstateActive
  · rw [hr, haction]
    exact Step.write state stage bit ⟨hstateActive, hstateCursor⟩ hstatePort (.inl rfl)


theorem menu_run_writtenFrom_firstEntry (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance P.certificate.stages P.tools)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance P.certificate.stages P.tools))
    (sample : P.CalibratedMenuSeed × (P.freshInput P.certificate.stages P.tools fee hfee).World)
    (stage : (freshInstance P.certificate.stages P.tools).Stage) (clock level reviews : ℕ) (bad : MenuBadAction) (valid : level ≤ P.certificate.M)
    (hentry : FirstEntryAt (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
      (menuRule P table) stage.val clock sample)
    (ha : (Parameters.menuEntryAt table (P.certificate.stages - stage.val)
      (P.menuEntryTools P.certificate.stages P.tools
        (run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample clock).history stage)).action =
          .test level bad)
    (hstop : (calibratedStageTest P level).rule.stop (sample.1.1 stage, sample.1.2 stage)
      (menuOriginalTape P P.certificate.stages P.tools fee hfee stage (worldTapes (P.freshInput P.certificate.stages P.tools fee hfee) sample.2 stage)) = reviews) :
    run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
      (menuRule P table) sample (clock + reviews + 1) =
        menuWrittenFrom (P.freshInput P.certificate.stages P.tools fee hfee) C accounting stage
          (run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample clock)
          (worldTapes (P.freshInput P.certificate.stages P.tools fee hfee) sample.2 stage) reviews
          ((calibratedStageTest P level).rule.decision (sample.1.1 stage, sample.1.2 stage)
            (menuOriginalTape P P.certificate.stages P.tools fee hfee stage (worldTapes (P.freshInput P.certificate.stages P.tools fee hfee) sample.2 stage))) := by
  have hlegal := menuRule_legal P table fee hfee C hearly accounting
  obtain ⟨hactive, hfresh⟩ := firstEntryAt_unborn (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
    (menuRule P table) hlegal sample stage.val clock hentry
  obtain ⟨hport, hzero⟩ := hfresh stage le_rfl
  obtain ⟨hh, hc, hw, ho⟩ := menuFirstEntry_visible_fresh (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
    (menuRule P table) hlegal sample stage clock hentry
  exact menu_run_writtenFrom P table fee hfee C accounting sample stage clock _ rfl
    hactive hentry.1 hport hzero hh hc hw ho level _ bad valid rfl ha reviews hstop


theorem menuEntry_run_written (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance P.certificate.stages P.tools)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance P.certificate.stages P.tools))
    (sample : P.CalibratedMenuSeed × (P.freshInput P.certificate.stages P.tools fee hfee).World)
    (cursor n clock : ℕ) (hfit : cursor + (n + 1) = P.certificate.stages)
    (stage : (freshInstance P.certificate.stages P.tools).Stage) (hstage : stage.val = cursor)
    (hentry : FirstEntryAt (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
      (menuRule P table) cursor clock sample)
    (level reviews : ℕ) (bad : MenuBadAction) (valid : level ≤ P.certificate.M)
    (ha : (Parameters.menuEntryAt table (n + 1)
      (P.tools - (run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample clock).ledger.executions.length)).action = .test level bad)
    (hstop : (calibratedStageTest P level).rule.stop (sample.1.1 stage, sample.1.2 stage)
      (menuOriginalTape P P.certificate.stages P.tools fee hfee stage (worldTapes (P.freshInput P.certificate.stages P.tools fee hfee) sample.2 stage)) = reviews) :
    run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample (clock + reviews + 1) =
      menuWrittenFrom (P.freshInput P.certificate.stages P.tools fee hfee) C accounting stage
        (run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample clock)
        (worldTapes (P.freshInput P.certificate.stages P.tools fee hfee) sample.2 stage) reviews
        ((calibratedStageTest P level).rule.decision (sample.1.1 stage, sample.1.2 stage)
          (menuOriginalTape P P.certificate.stages P.tools fee hfee stage (worldTapes (P.freshInput P.certificate.stages P.tools fee hfee) sample.2 stage))) := by
  let input := P.freshInput P.certificate.stages P.tools fee hfee
  let rule := menuRule P table
  have hlegal := menuRule_legal P table fee hfee C hearly accounting
  have hentry' : FirstEntryAt input C .uncapped accounting rule stage.val clock sample := hstage.symm ▸ hentry
  have hactive := (firstEntryAt_unborn input C .uncapped accounting rule hlegal sample cursor clock hentry).1
  have hport := ((firstEntryAt_unborn input C .uncapped accounting rule hlegal sample cursor clock hentry).2 stage (by omega)).1
  have hp := run_prefix_of_active input C .uncapped accounting rule hlegal sample clock hactive
  have hc : (run input C .uncapped accounting rule sample clock).cursor = stage.val := hentry.1.trans hstage.symm
  have hk := menuPrefix_entryTools_eq_physical_sub P table fee hfee C accounting sample.1
    (input.truthAt sample.2) (worldTapes input sample.2) hp stage hc hport
  have hrow : P.certificate.stages - stage.val = n + 1 := by omega
  apply menu_run_writtenFrom_firstEntry P table fee hfee C hearly accounting sample stage clock level reviews bad valid hentry'
  · rw [hrow, hk]
    exact ha
  · exact hstop


theorem menuEntry_written_records (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance P.certificate.stages P.tools)) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting (freshInstance P.certificate.stages P.tools))
    (sample : P.CalibratedMenuSeed × (P.freshInput P.certificate.stages P.tools fee hfee).World)
    (cursor n clock : ℕ) (hfit : cursor + (n + 1) = P.certificate.stages)
    (stage : (freshInstance P.certificate.stages P.tools).Stage) (hstage : stage.val = cursor)
    (hentry : FirstEntryAt (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
      (menuRule P table) cursor clock sample)
    (level reviews : ℕ) (bad : MenuBadAction) (valid : level ≤ P.certificate.M)
    (ha : (Parameters.menuEntryAt table (n + 1)
      (P.tools - (run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample clock).ledger.executions.length)).action = .test level bad)
    (hstop : (calibratedStageTest P level).rule.stop (sample.1.1 stage, sample.1.2 stage)
      (menuOriginalTape P P.certificate.stages P.tools fee hfee stage (worldTapes (P.freshInput P.certificate.stages P.tools fee hfee) sample.2 stage)) = reviews) :
    let start := run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample clock
    let written := run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample (clock + reviews + 1)
    let bit := (calibratedStageTest P level).rule.decision (sample.1.1 stage, sample.1.2 stage)
      (menuOriginalTape P P.certificate.stages P.tools fee hfee stage (worldTapes (P.freshInput P.certificate.stages P.tools fee hfee) sample.2 stage))
    written.halted = false ∧ written.cursor = cursor ∧ written.ledger.written stage = some bit ∧
    written.ledger.truth = (P.freshInput P.certificate.stages P.tools fee hfee).truthAt sample.2 ∧
    written.ledger.observationBill (P.freshInput P.certificate.stages P.tools fee hfee).fees =
      start.ledger.observationBill (P.freshInput P.certificate.stages P.tools fee hfee).fees + P.experiment.observationCharge reviews ∧
    written.ledger.executions = start.ledger.executions ∧
    P.menuEntryTools P.certificate.stages P.tools written.history stage = P.tools - start.ledger.executions.length ∧
    (Finset.univ \ historyUsed written.history).card = P.tools - start.ledger.executions.length ∧
    (∀ commitment ∈ written.ledger.commitments, commitment.handle.stage ≠ stage) := by
  let input := P.freshInput P.certificate.stages P.tools fee hfee
  let rule := menuRule P table
  let start := run input C .uncapped accounting rule sample clock
  let tape := worldTapes input sample.2 stage
  let bit := (calibratedStageTest P level).rule.decision (sample.1.1 stage, sample.1.2 stage) (menuOriginalTape P P.certificate.stages P.tools fee hfee stage tape)
  have hwrite := menuEntry_run_written P table fee hfee C hC.1.1 accounting sample cursor n clock hfit stage hstage
    hentry level reviews bad valid ha hstop
  have hf := menuWrittenFrom_fields input C accounting stage start tape reviews bit
  have hlegal := menuRule_legal P table fee hfee C hC.1.1 accounting
  obtain ⟨hactive, hfresh⟩ := firstEntryAt_unborn input C .uncapped accounting rule hlegal sample cursor clock hentry
  have hp := run_prefix_of_active input C .uncapped accounting rule hlegal sample clock hactive
  have hport : start.ledger.written stage = none := (hfresh stage (by omega)).1
  have hc : start.cursor = stage.val := hentry.1.trans hstage.symm
  have htruth : start.ledger.truth = input.truthAt sample.2 := prefix_truth input C .uncapped accounting rule sample.1 _ _ hp
  have hk : P.menuEntryTools P.certificate.stages P.tools start.history stage = P.tools - start.ledger.executions.length :=
    menuPrefix_entryTools_eq_physical_sub P table fee hfee C accounting sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) hp stage hc hport
  have havailable : (Finset.univ \ historyUsed start.history).card = P.tools - start.ledger.executions.length :=
    (menuPrefix_entryTools_eq_availableCard P table fee hfee C hC accounting sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) hp stage hc hport).symm.trans hk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hwrite]
    exact hf.2.1
  · rw [hwrite]
    exact hf.1.trans hentry.1
  · rw [hwrite]
    exact hf.2.2.2.2.2.2
  · rw [hwrite]
    exact hf.2.2.2.1.trans htruth
  · rw [hwrite, menuWrittenFrom_observationBill_exact]
    exact congrArg (fun charge => start.ledger.observationBill input.fees + charge)
      (P.experiment.observationCharge_nat reviews).symm
  · rw [hwrite]
    exact hf.2.2.2.2.2.1
  · rw [hwrite, menuWrittenFrom_entryTools P P.certificate.stages P.tools fee hfee C hC.1.1, hk]
  · rw [hwrite, menuWrittenFrom_used input C hC.1.1]
    exact havailable
  · rw [hwrite]
    exact menuWrittenFrom_no_current_commitment input C accounting rule sample.1 (input.truthAt sample.2)
      (worldTapes input sample.2) hp stage hport tape reviews bit


end PDROC.CalibratedRuntime
