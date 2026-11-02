module

public import PaperProofs.Paid.PDMenu_MenuWrittenEntryRecords_119
public import PaperProofs.Paid.PDMenu_MenuEntryRecordTarget_115
public import PaperProofs.Paid.PDMenu_MenuSummaryBranches_113
public import PaperProofs.Paid.PDMenu_MenuRepairRecords_109

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem menuRepairedFrom_observationBill_exact {I : Instance} (accounting : NormalAccounting I)
    (stage : I.Stage) (start : State I) (tool : I.Tool) (fees : Fees I) :
    (menuRepairedFrom accounting stage start tool).ledger.observationBill fees = start.ledger.observationBill fees := by
  unfold Ledger.observationBill
  rw [menuRepairedFrom_reviews]

/-- The repaired branch of the strict shorter-suffix induction uses the
same physical run, actual tools and all three real repair clocks. The IH
is applied only after the proved actual next first entry. -/
theorem menuEntryRunRecords_test_repair (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting (freshInstance N K))
    (sample : MenuSeed N K × (P.freshInput N K fee hfee).World)
    (cursor n clock : ℕ) (hfit : cursor + (n + 1) = N) (hnextfit : cursor + 1 + n = N)
    (stage : (freshInstance N K).Stage) (hstage : stage.val = cursor)
    (hentry : FirstEntryAt (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) cursor clock sample)
    (level reviews : ℕ)
    (ha : (Parameters.menuEntryAt table (n + 1)
      (K - (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock).ledger.executions.length)).action = .test level .repair)
    (hstop : (menuAnalysisTest P level).rule.stop (sample.1 stage)
      (menuOriginalTape P N K fee hfee stage (worldTapes (P.freshInput N K fee hfee) sample.2 stage)) = reviews)
    (hwrong : (menuAnalysisTest P level).rule.decision (sample.1 stage)
      (menuOriginalTape P N K fee hfee stage (worldTapes (P.freshInput N K fee hfee) sample.2 stage)) ≠
        (P.freshInput N K fee hfee).truthAt sample.2 stage)
    (hpos : 0 < K - (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock).ledger.executions.length)
    (ih : ∀ nextclock, FirstEntryAt (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) (cursor + 1) nextclock sample →
        MenuEntryRunRecords P N K table fee hfee C accounting sample (cursor + 1) n nextclock hnextfit) :
    MenuEntryRunRecords P N K table fee hfee C accounting sample cursor (n + 1) clock hfit := by
  let input := P.freshInput N K fee hfee
  let rule := P.compiledMenuRule N K table
  let start := run input C .uncapped accounting rule sample clock
  let writeclock := clock + reviews + 1
  let written := run input C .uncapped accounting rule sample writeclock
  let nextclock := writeclock + 3
  let k := K - start.ledger.executions.length
  let bit := (menuAnalysisTest P level).rule.decision (sample.1 stage)
    (menuOriginalTape P N K fee hfee stage (worldTapes input sample.2 stage))
  let child := menuPathSummary P table n (k - 1)
    (menuSuffixSeed N K (cursor + 1) n hnextfit sample.1)
    (menuSuffixWorld P N K (cursor + 1) n hnextfit fee hfee sample.2)
  obtain ⟨hactive, hcursor, hwritten, htruth, hobs, hexecutions, hsnapshot, havailable, hnoCurrent⟩ :=
    menuEntry_written_records P N K table fee hfee C hC accounting sample cursor n clock hfit stage hstage
      hentry level reviews .repair ha hstop
  have hcStage : written.cursor = stage.val := hcursor.trans hstage.symm
  have hbad : bit ≠ written.ledger.truth stage := fun he => hwrong (he.trans (congrFun htruth stage))
  have hrow : N - stage.val = n + 1 := by omega
  have hcell : (Parameters.menuEntryAt table (N - stage.val) (P.menuEntryTools N K written.history stage)).action = .test level .repair := by
    rw [hrow, hsnapshot]
    exact ha
  have htools : 0 < (Finset.univ \ historyUsed written.history).card := by
    rw [havailable]
    exact hpos
  obtain ⟨tool, _, _, hadv, hentryNext⟩ := compiledMenu_run_repair_threeSteps P N K table fee hfee C hC.1.1 accounting
    sample stage writeclock bit level hactive hcStage hwritten hbad hcell hnoCurrent htools
  have hrNext : run input C .uncapped accounting rule sample nextclock = menuRepairedFrom accounting stage written tool := hadv
  have hentryNext' : FirstEntryAt input C .uncapped accounting rule (cursor + 1) nextclock sample := by
    rw [hstage] at hentryNext
    exact hentryNext
  have heNext : (run input C .uncapped accounting rule sample nextclock).ledger.executions.length = start.ledger.executions.length + 1 := by
    rw [hrNext, menuRepairedFrom_executionCount]
    exact congrArg (fun count : ℕ => count + 1) (congrArg List.length hexecutions)
  have hkNext : K - (run input C .uncapped accounting rule sample nextclock).ledger.executions.length = k - 1 := by
    rw [heNext, Nat.sub_add_eq]
  have hoNext : (run input C .uncapped accounting rule sample nextclock).ledger.observationBill input.fees =
      start.ledger.observationBill input.fees + P.experiment.observationCharge reviews := by
    rw [hrNext, menuRepairedFrom_observationBill_exact]
    exact hobs
  obtain ⟨ended, hended, hhalt, hoChild, heChild, hsChild⟩ := ih nextclock hentryNext'
  rw [hkNext] at hoChild heChild hsChild
  rw [heNext] at heChild
  have hoChild' : (run input C .uncapped accounting rule sample ended).ledger.observationBill input.fees =
      (run input C .uncapped accounting rule sample nextclock).ledger.observationBill input.fees + child.observation := hoChild
  have heChild' : (run input C .uncapped accounting rule sample ended).ledger.executions.length =
      (start.ledger.executions.length + 1) + child.physicalRepairs := heChild
  have hsChild' : runSuccess input C .uncapped accounting rule sample ↔ child.failure = false := hsChild
  have hseed := menuSuffixSeed_head N K cursor n hfit sample.1 stage hstage
  have hworld := menuSuffixWorld_head P N K cursor n hfit fee hfee sample.2 stage hstage
  have hstopCrop : (menuAnalysisTest P level).rule.stop
      (menuSuffixSeed N K cursor (n + 1) hfit sample.1 0)
      (menuSuffixWorld P N K cursor (n + 1) hfit fee hfee sample.2 0).2 = reviews := by
    rw [hseed, hworld]
    exact hstop
  have hwrongCrop : (menuAnalysisTest P level).rule.decision
      (menuSuffixSeed N K cursor (n + 1) hfit sample.1 0)
      (menuSuffixWorld P N K cursor (n + 1) hfit fee hfee sample.2 0).2 ≠
        (menuSuffixWorld P N K cursor (n + 1) hfit fee hfee sample.2 0).1 := by
    rw [hseed, hworld]
    exact hwrong
  have hk : k ≠ 0 := Nat.ne_zero_of_lt hpos
  have hsummary : menuPathSummary P table (n + 1) k
      (menuSuffixSeed N K cursor (n + 1) hfit sample.1)
      (menuSuffixWorld P N K cursor (n + 1) hfit fee hfee sample.2) =
        { observation := P.experiment.observationCharge reviews + child.observation,
          physicalRepairs := child.physicalRepairs + 1, failure := child.failure } := by
    have hs := menuPathSummary_test_repair P table n k level reviews
      (menuSuffixSeed N K cursor (n + 1) hfit sample.1)
      (menuSuffixWorld P N K cursor (n + 1) hfit fee hfee sample.2) ha hstopCrop hwrongCrop hk
    rw [menuSuffixSeed_tail N K cursor n hfit hnextfit, menuSuffixWorld_tail P N K cursor n hfit hnextfit fee hfee] at hs
    exact hs
  unfold MenuEntryRunRecords
  dsimp only
  rw [hsummary]
  refine ⟨ended, (by dsimp only [nextclock, writeclock] at hended; omega), hhalt, ?_, ?_, hsChild'⟩
  · calc
      _ = (run input C .uncapped accounting rule sample nextclock).ledger.observationBill input.fees + child.observation := hoChild'
      _ = (start.ledger.observationBill input.fees + P.experiment.observationCharge reviews) + child.observation :=
        congrArg (fun charge => charge + child.observation) hoNext
      _ = _ := add_assoc _ _ _
  · exact heChild'.trans ((Nat.add_assoc _ _ _).trans
      (congrArg (fun count : ℕ => start.ledger.executions.length + count) (Nat.add_comm 1 child.physicalRepairs)))

end PDMenu
