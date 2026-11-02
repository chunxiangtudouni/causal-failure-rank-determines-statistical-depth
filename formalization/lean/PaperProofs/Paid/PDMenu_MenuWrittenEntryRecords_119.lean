module

public import PaperProofs.Paid.PDMenu_MenuEntryEndpoint_118
public import PaperProofs.Paid.PDMenu_MenuSegmentCharge_106

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem menuWrittenFrom_observationBill_exact {I : Instance} (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (stage : I.Stage) (start : State I)
    (tape : (input.experiment stage).Tape) (reviews : ℕ) (bit : Bool) (fees : Fees I) :
    (menuWrittenFrom input C accounting stage start tape reviews bit).ledger.observationBill fees =
      start.ledger.observationBill fees + ENNReal.ofReal (fees.observation stage : ℝ) * reviews := by
  classical
  simp only [menuWrittenFrom, record, reportedWriteLedger]
  split_ifs <;> exact menuReviewFrom_observationBill input accounting stage start tape reviews fees

/-- Complete actual written-entry data derived from the original first
entry and literal endpoint. In particular available tools and past ledger
facts are conclusions of real execution, never continuation inputs. -/
theorem menuEntry_written_records (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting (freshInstance N K))
    (sample : MenuSeed N K × (P.freshInput N K fee hfee).World)
    (cursor n clock : ℕ) (hfit : cursor + (n + 1) = N)
    (stage : (freshInstance N K).Stage) (hstage : stage.val = cursor)
    (hentry : FirstEntryAt (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) cursor clock sample)
    (level reviews : ℕ) (bad : MenuBadAction)
    (ha : (Parameters.menuEntryAt table (n + 1)
      (K - (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock).ledger.executions.length)).action = .test level bad)
    (hstop : (menuAnalysisTest P level).rule.stop (sample.1 stage)
      (menuOriginalTape P N K fee hfee stage (worldTapes (P.freshInput N K fee hfee) sample.2 stage)) = reviews) :
    let start := run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock
    let written := run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample (clock + reviews + 1)
    let bit := (menuAnalysisTest P level).rule.decision (sample.1 stage)
      (menuOriginalTape P N K fee hfee stage (worldTapes (P.freshInput N K fee hfee) sample.2 stage))
    written.halted = false ∧ written.cursor = cursor ∧ written.ledger.written stage = some bit ∧
    written.ledger.truth = (P.freshInput N K fee hfee).truthAt sample.2 ∧
    written.ledger.observationBill (P.freshInput N K fee hfee).fees =
      start.ledger.observationBill (P.freshInput N K fee hfee).fees + P.experiment.observationCharge reviews ∧
    written.ledger.executions = start.ledger.executions ∧
    P.menuEntryTools N K written.history stage = K - start.ledger.executions.length ∧
    (Finset.univ \ historyUsed written.history).card = K - start.ledger.executions.length ∧
    (∀ commitment ∈ written.ledger.commitments, commitment.handle.stage ≠ stage) := by
  let input := P.freshInput N K fee hfee
  let rule := P.compiledMenuRule N K table
  let start := run input C .uncapped accounting rule sample clock
  let tape := worldTapes input sample.2 stage
  let bit := (menuAnalysisTest P level).rule.decision (sample.1 stage) (menuOriginalTape P N K fee hfee stage tape)
  have hwrite := menuEntry_run_written P N K table fee hfee C hC.1.1 accounting sample cursor n clock hfit stage hstage
    hentry level reviews bad ha hstop
  have hf := menuWrittenFrom_fields input C accounting stage start tape reviews bit
  have hlegal := P.compiledMenuRule_uncapped_legal N K table fee hfee C hC.1.1 accounting
  obtain ⟨hactive, hfresh⟩ := firstEntryAt_unborn input C .uncapped accounting rule hlegal sample cursor clock hentry
  have hp := run_prefix_of_active input C .uncapped accounting rule hlegal sample clock hactive
  have hport : start.ledger.written stage = none := (hfresh stage (by omega)).1
  have hc : start.cursor = stage.val := hentry.1.trans hstage.symm
  have htruth : start.ledger.truth = input.truthAt sample.2 := prefix_truth input C .uncapped accounting rule sample.1 _ _ hp
  have hk : P.menuEntryTools N K start.history stage = K - start.ledger.executions.length :=
    menuPrefix_entryTools_eq_physical_sub P N K table fee hfee C accounting sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) hp stage hc hport
  have havailable : (Finset.univ \ historyUsed start.history).card = K - start.ledger.executions.length :=
    (menuPrefix_entryTools_eq_availableCard P N K table fee hfee C hC accounting sample.1
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
  · rw [hwrite, menuWrittenFrom_entryTools P N K fee hfee C hC.1.1, hk]
  · rw [hwrite, menuWrittenFrom_used input C hC.1.1]
    exact havailable
  · rw [hwrite]
    exact menuWrittenFrom_no_current_commitment input C accounting rule sample.1 (input.truthAt sample.2)
      (worldTapes input sample.2) hp stage hport tape reviews bit

end PDMenu
