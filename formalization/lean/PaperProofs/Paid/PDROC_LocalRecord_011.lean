module
public import PaperProofs.Paid.PDROC_LocalRecord_008

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
open PaperProofs.Common PaperProofs.Common.Native
open PaperProofs.Paid

namespace PDROC
universe u
variable {I : Instance} {Seed : Type u}

/-- Under the ORIGINAL current-payment contract, every real active unwritten
current stage admits only its own review/write, stop or abandonment. Old
execution/allocation requests are excluded by their genuine window guards. -/
theorem currentPayment_unwritten_action_cases (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentPayment) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting rule)
    (sample : Seed × input.World) (n : ℕ) (stage : I.Stage)
    (hactive : (run input C mode accounting rule sample n).halted = false)
    (hcursor : (run input C mode accounting rule sample n).cursor = stage.val)
    (hunwritten : (run input C mode accounting rule sample n).ledger.written stage = none) :
    rule sample.1 (run input C mode accounting rule sample n).history = .review stage ∨
      (∃ bit, rule sample.1 (run input C mode accounting rule sample n).history = .write stage bit) ∨
      rule sample.1 (run input C mode accounting rule sample n).history = .stop ∨
      rule sample.1 (run input C mode accounting rule sample n).history = .abandon := by
  obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting rule hlegal sample n
  obtain ⟨next, hs⟩ := hlegal sample.1 _ _ m _ hp hactive
  generalize ha : rule sample.1 (run input C mode accounting rule sample n).history = action at hs ⊢
  cases hs with
  | review current live port resources =>
    have he : current = stage := Fin.ext (live.2.symm.trans hcursor)
    subst current
    exact .inl rfl
  | write current bit live port resources =>
    have he : current = stage := Fin.ext (live.2.symm.trans hcursor)
    subst current
    exact .inr (.inl ⟨bit, rfl⟩)
  | allocate handle tool active valid compatible unused unallocated window resources =>
    have he : handle.stage = stage := Fin.ext ((window hC.1.2).symm.trans hcursor)
    have hv := valid.1
    rw [he, hunwritten] at hv
    cases hv
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    have he : handle.stage = stage := Fin.ext ((window hC.2).symm.trans hcursor)
    have hv := valid.1
    rw [he, hunwritten] at hv
    cases hv
  | advance current live written resources =>
    have he : current = stage := Fin.ext (live.2.symm.trans hcursor)
    subst current
    exact (written hunwritten).elim
  | stop active => exact .inr (.inr (.inl rfl))
  | abandon active => exact .inr (.inr (.inr rfl))

/-- No silent old execution occurs before the current first write, even
though the general suffix replay faithfully supports such executions. -/
theorem currentPayment_unwritten_oldRequest_none (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentPayment) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting rule)
    (sample : Seed × input.World) (n : ℕ) (stage : I.Stage)
    (hactive : (run input C mode accounting rule sample n).halted = false)
    (hcursor : (run input C mode accounting rule sample n).cursor = stage.val)
    (hunwritten : (run input C mode accounting rule sample n).ledger.written stage = none) :
    oldExecutionRequest stage.val (rule sample.1 (run input C mode accounting rule sample n).history) = none := by
  rcases currentPayment_unwritten_action_cases input C hC mode accounting rule hlegal sample n stage
    hactive hcursor hunwritten with hreview | ⟨bit, hwrite⟩ | hstop | habandon
  · simp only [hreview, oldExecutionRequest]
  · simp only [hwrite, oldExecutionRequest]
  · simp only [hstop, oldExecutionRequest]
  · simp only [habandon, oldExecutionRequest]

theorem currentPayment_unwritten_settle_eq (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentPayment) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting rule)
    (sample : Seed × input.World) (n : ℕ) (stage : I.Stage)
    (hactive : (run input C mode accounting rule sample n).halted = false)
    (hcursor : (run input C mode accounting rule sample n).cursor = stage.val)
    (hunwritten : (run input C mode accounting rule sample n).ledger.written stage = none) (fuel : ℕ) :
    settleOldExecutions stage.val accounting rule fuel sample.1
      (publicStartup (run input C mode accounting rule sample n)) =
        (publicStartup (run input C mode accounting rule sample n), 0) := by
  have ho := currentPayment_unwritten_oldRequest_none input C hC mode accounting rule hlegal sample n stage
    hactive hcursor hunwritten
  have hn : silentOldNext stage.val accounting (publicStartup (run input C mode accounting rule sample n))
      (rule sample.1 (publicStartup (run input C mode accounting rule sample n)).history) = none := by
    change (if (run input C mode accounting rule sample n).halted then none else
      (oldExecutionRequest stage.val (rule sample.1 (run input C mode accounting rule sample n).history)).map _) = none
    rw [hactive, ho]
    rfl
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [settleOldExecutions, hn]

theorem currentPayment_firstEntry_settle_eq (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentPayment) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting rule)
    (sample : Seed × input.World) (stage : I.Stage) (n : ℕ)
    (hentry : FirstEntryAt input C mode accounting rule stage.val n sample) (fuel : ℕ) :
    settleOldExecutions stage.val accounting rule fuel sample.1
      (publicStartup (run input C mode accounting rule sample n)) =
        (publicStartup (run input C mode accounting rule sample n), 0) := by
  have hunborn := firstEntryAt_unborn input C mode accounting rule hlegal sample stage.val n hentry
  exact currentPayment_unwritten_settle_eq input C hC mode accounting rule hlegal sample n stage hunborn.1 hentry.1
    (hunborn.2 stage le_rfl).1 fuel

end PDROC
