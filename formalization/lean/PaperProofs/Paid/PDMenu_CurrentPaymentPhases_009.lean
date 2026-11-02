module

public import PaperProofs.Paid.PDMenu_CurrentHeadRuns_007

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native

variable {I : Instance}

/-- Actual current-payment guard transport, with no continuation-performance
hypothesis. Native Step and the original available set are the only inputs. -/
theorem paidHeadThenRule_after_step {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hpayment : C.execution = .currentWindow)
    (accounting : NormalAccounting I)
    (head : I.Stage) (test : (input.experiment head).AdmissibleRule Seed)
    (available : Finset I.Tool) (after : PolicyRule I Seed) (seed : Seed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {m : ℕ} {s next : State I}
    (hp : Prefix input C .uncapped accounting (paidHeadThenRule input head test available after) seed truth tapes m s)
    (hwritten : s.ledger.written head ≠ none) (action : Action I)
    (ha : after seed s.history = action) (hs : Step input C .uncapped accounting tapes s action next)
    (havailable : ∀ handle tool, action = .allocate handle tool → tool ∈ available) :
    paidHeadThenRule input head test available after seed s.history = action := by
  have hw := prefix_historyWritten input C .uncapped accounting _ seed truth tapes hp head
  have hraw : bellmanHeadThenRaw input head test after seed s.history = action := by
    simp only [bellmanHeadThenRaw, hw, hwritten, ite_false]
    exact ha
  have hg := paidGuardedRule_eq_of_step input C ⟨⟨hearly, hcurrent⟩, hpayment⟩ accounting
    (paidHeadThenRule input head test available after) (bellmanHeadThenRaw input head test after)
    seed truth tapes hp available (by rw [hraw]; exact hs)
    (by intro handle tool hh; exact havailable handle tool (hraw.symm.trans hh))
  exact hg.trans hraw

theorem paidHeadThen_run_correct_advance {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hpayment : C.execution = .currentWindow)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (repair : Option I.Tool) (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hcorrect : test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head) :
    let after := bellmanPostHeadRaw input head repair good bad
    let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
    run input C .uncapped accounting (paidHeadThenRule input head test available after) sample (n + 2) =
      record accounting written (.advance head) [.advanced head] (advanceLedger written head) 1 false := by
  dsimp only
  let after := bellmanPostHeadRaw input head repair good bad
  let policy := paidHeadThenPolicy input C ⟨⟨hearly, hcurrent⟩, hpayment⟩ accounting head test available after
    (measurable_bellmanPostHeadRaw input head repair good bad hgood hbad)
  let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hr : run input C .uncapped accounting policy.val.rule sample (n + 1) = written :=
    paidHeadThen_run_write input C accounting head hhead test available after sample n hstop
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample (n + 1)
  rw [hr] at hp
  have ht := prefix_truth input C .uncapped accounting policy.val.rule sample.1 _ _ hp
  have hc : written.cursor = 0 := bellmanHeadWrittenState_cursor input C accounting head _ _ n _
  have hw : written.ledger.written head = some (written.ledger.truth head) := by
    rw [ht]
    exact (bellmanHeadWrittenState_written input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))).trans
      (congrArg some hcorrect)
  have hreport : ∃ clock, written.ledger.reportTime head = some clock := by
    refine ⟨(headReviewState input accounting head (input.truthAt sample.2) (worldTapes input sample.2 head) n).clock, ?_⟩
    simp only [written, bellmanHeadWrittenState, record, reportedWriteLedger, hearly, ↓reduceIte,
      writeLedger, Function.update_self]
  have hraw := bellmanPostHeadRaw_correct_of_prefix input C hearly .uncapped accounting policy.val.rule
    sample.1 _ _ hp head repair good bad hc hw hreport
  have hwriteVisible : historyWritten written.history head = written.ledger.written head :=
    prefix_historyWritten input C .uncapped accounting policy.val.rule sample.1 _ _ hp head
  have hafter : bellmanHeadThenRaw input head test after sample.1 written.history = .advance head := by
    simp only [bellmanHeadThenRaw, hwriteVisible, hw, reduceCtorEq, ↓reduceIte]
    exact hraw
  have hs : Step input C .uncapped accounting (worldTapes input sample.2) written (.advance head)
      (record accounting written (.advance head) [.advanced head] (advanceLedger written head) 1 false) := by
    have h := Step.advance (input := input) (C := C) (mode := .uncapped) (accounting := accounting)
      (tapes := worldTapes input sample.2) written head ⟨rfl, hc.trans hhead.symm⟩ (by rw [hw]; simp) (.inl rfl)
    simpa only [hc] using h
  have hguard := paidGuardedRule_eq_of_step input C ⟨⟨hearly, hcurrent⟩, hpayment⟩ accounting
    policy.val.rule (bellmanHeadThenRaw input head test after) sample.1 _ _ hp available
    (by rw [hafter]; exact hs) (by intro handle tool heq; rw [hafter] at heq; cases heq)
  change run input C .uncapped accounting policy.val.rule sample (n + 1 + 1) = _
  apply run_succ_of_step input C .uncapped accounting policy.val.rule sample (n + 1) _
  · rw [hr]
    rfl
  · rw [hr]
    change Step input C .uncapped accounting _ written
      (paidGuardedRule available (bellmanHeadThenRaw input head test after) sample.1 written.history) _
    rw [hguard, hafter]
    exact hs

theorem paidHeadThen_run_wrong_allocate {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hpayment : C.execution = .currentWindow)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (tool : I.Tool) (htool : tool ∈ available) (heligible : tool ∈ I.eligible head)
    (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hwrong : test.rule.decision sample.1 (worldTapes input sample.2 head) ≠ input.truthAt sample.2 head) :
    let after := bellmanPostHeadRaw input head (some tool) good bad
    let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
    run input C .uncapped accounting (paidHeadThenRule input head test available after) sample (n + 2) =
      bellmanAllocateState accounting written head tool := by
  dsimp only
  let after := bellmanPostHeadRaw input head (some tool) good bad
  let policy := paidHeadThenPolicy input C ⟨⟨hearly, hcurrent⟩, hpayment⟩ accounting head test available after
    (measurable_bellmanPostHeadRaw input head (some tool) good bad hgood hbad)
  let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  let handle : MismatchHandle I := ⟨head, written.ledger.writeSerial head⟩
  have hr : run input C .uncapped accounting policy.val.rule sample (n + 1) = written :=
    paidHeadThen_run_write input C accounting head hhead test available after sample n hstop
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample (n + 1)
  rw [hr] at hp
  have ht := prefix_truth input C .uncapped accounting policy.val.rule sample.1 _ _ hp
  have hc : written.cursor = 0 := bellmanHeadWrittenState_cursor input C accounting head _ _ n _
  have hw : written.ledger.written head = some (!written.ledger.truth head) := by
    rw [ht]
    exact (bellmanHeadWrittenState_written input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))).trans
      (congrArg some (Bool.eq_not_iff.mpr hwrong))
  have hreport : ∃ clock, written.ledger.reportTime head = some clock := by
    refine ⟨(headReviewState input accounting head (input.truthAt sample.2) (worldTapes input sample.2 head) n).clock, ?_⟩
    simp only [written, bellmanHeadWrittenState, record, reportedWriteLedger, hearly, ↓reduceIte,
      writeLedger, Function.update_self]
  have he : written.ledger.commitments = [] ∧ written.ledger.executions = [] :=
    bellmanHeadWrittenState_empty_corrections input C hearly accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hraw : after sample.1 written.history = .allocate handle tool := by
    have h := bellmanPostHeadRaw_wrong_of_prefix input C hearly .uncapped accounting policy.val.rule
      sample.1 _ _ hp head tool good bad hc hw hreport
    simpa only [he.1, List.map_nil, List.not_mem_nil, ↓reduceIte] using h
  have hwriteVisible : historyWritten written.history head = written.ledger.written head :=
    prefix_historyWritten input C .uncapped accounting policy.val.rule sample.1 _ _ hp head
  have hafter : bellmanHeadThenRaw input head test after sample.1 written.history = .allocate handle tool := by
    simp only [bellmanHeadThenRaw, hwriteVisible, hw, reduceCtorEq, ↓reduceIte]
    exact hraw
  have hs : Step input C .uncapped accounting (worldTapes input sample.2) written (.allocate handle tool)
      (bellmanAllocateState accounting written head tool) := by
    apply Step.allocate written handle tool rfl ⟨hw, rfl, hreport⟩ heligible
    · simp only [he.1, List.not_mem_nil, false_implies, implies_true]
    · simp only [he.1, List.not_mem_nil, false_implies, implies_true]
    · exact fun _ => hc.trans hhead.symm
    · exact .inl rfl
  have hguard := paidGuardedRule_eq_of_step input C ⟨⟨hearly, hcurrent⟩, hpayment⟩ accounting
    policy.val.rule (bellmanHeadThenRaw input head test after) sample.1 _ _ hp available
    (by rw [hafter]; exact hs) (by intro h t heq; rw [hafter] at heq; cases heq; exact htool)
  change run input C .uncapped accounting policy.val.rule sample (n + 1 + 1) = _
  apply run_succ_of_step input C .uncapped accounting policy.val.rule sample (n + 1) _
  · rw [hr]
    rfl
  · rw [hr]
    change Step input C .uncapped accounting _ written
      (paidGuardedRule available (bellmanHeadThenRaw input head test after) sample.1 written.history) _
    rw [hguard, hafter]
    exact hs

theorem paidHeadThen_run_wrong_execute {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hpayment : C.execution = .currentWindow)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (tool : I.Tool) (htool : tool ∈ available) (heligible : tool ∈ I.eligible head)
    (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hwrong : test.rule.decision sample.1 (worldTapes input sample.2 head) ≠ input.truthAt sample.2 head) :
    let after := bellmanPostHeadRaw input head (some tool) good bad
    let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
    let allocated := bellmanAllocateState accounting written head tool
    run input C .uncapped accounting (paidHeadThenRule input head test available after) sample (n + 3) =
      bellmanExecuteState accounting allocated head tool := by
  dsimp only
  let after := bellmanPostHeadRaw input head (some tool) good bad
  let policy := paidHeadThenPolicy input C ⟨⟨hearly, hcurrent⟩, hpayment⟩ accounting head test available after
    (measurable_bellmanPostHeadRaw input head (some tool) good bad hgood hbad)
  let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  let allocated := bellmanAllocateState accounting written head tool
  let handle : MismatchHandle I := ⟨head, allocated.ledger.writeSerial head⟩
  have hr : run input C .uncapped accounting policy.val.rule sample (n + 2) = allocated :=
    paidHeadThen_run_wrong_allocate input C hearly hcurrent hpayment accounting head hhead test available
      tool htool heligible good bad hgood hbad sample n hstop hwrong
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample (n + 2)
  rw [hr] at hp
  have ht := prefix_truth input C .uncapped accounting policy.val.rule sample.1 _ _ hp
  have hc : allocated.cursor = 0 := bellmanHeadWrittenState_cursor input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hw : allocated.ledger.written head = some (!allocated.ledger.truth head) := by
    rw [ht]
    exact (bellmanHeadWrittenState_written input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))).trans
      (congrArg some (Bool.eq_not_iff.mpr hwrong))
  have hreport : ∃ clock, allocated.ledger.reportTime head = some clock := by
    refine ⟨(headReviewState input accounting head (input.truthAt sample.2) (worldTapes input sample.2 head) n).clock, ?_⟩
    simp only [allocated, bellmanAllocateState, allocateLedger, written, bellmanHeadWrittenState, record,
      reportedWriteLedger, hearly, ↓reduceIte, writeLedger, Function.update_self]
  have he : written.ledger.commitments = [] ∧ written.ledger.executions = [] :=
    bellmanHeadWrittenState_empty_corrections input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hcomm : allocated.ledger.commitments = [⟨handle, tool, written.clock⟩] := by
    simp only [allocated, bellmanAllocateState, record, allocateLedger, he.1, List.nil_append, handle]
  have hexec : allocated.ledger.executions = [] := he.2
  have hraw : after sample.1 allocated.history = .execute handle tool := by
    have h := bellmanPostHeadRaw_wrong_of_prefix input C hearly .uncapped accounting policy.val.rule
      sample.1 _ _ hp head tool good bad hc hw hreport
    simpa [hcomm, hexec, handle] using h
  have hs : Step input C .uncapped accounting (worldTapes input sample.2) allocated (.execute handle tool)
      (bellmanExecuteState accounting allocated head tool) := by
    apply Step.execute allocated handle tool rfl ⟨hw, rfl, hreport⟩ heligible
    · exact ⟨⟨handle, tool, written.clock⟩, by simp only [hcomm, List.mem_cons, List.not_mem_nil, or_false], rfl, rfl⟩
    · simp only [hexec, List.not_mem_nil, false_implies, implies_true]
    · simp only [hexec, List.not_mem_nil, false_implies, implies_true]
    · exact fun _ => hc.trans hhead.symm
    · exact .inl rfl
  have haction := paidHeadThenRule_after_step input C hearly hcurrent hpayment accounting head test available after
    sample.1 _ _ hp (by rw [hw]; simp) (.execute handle tool) hraw hs
    (by intro h t hh; cases hh)
  change run input C .uncapped accounting policy.val.rule sample (n + 2 + 1) = _
  apply run_succ_of_step input C .uncapped accounting policy.val.rule sample (n + 2) _
  · rw [hr]
    rfl
  · rw [hr]
    change Step input C .uncapped accounting _ allocated
      (paidHeadThenRule input head test available after sample.1 allocated.history)
      (bellmanExecuteState accounting allocated head tool)
    rw [haction]
    exact hs

theorem paidHeadThen_run_wrong_advance {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hpayment : C.execution = .currentWindow)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (tool : I.Tool) (htool : tool ∈ available) (heligible : tool ∈ I.eligible head)
    (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hwrong : test.rule.decision sample.1 (worldTapes input sample.2 head) ≠ input.truthAt sample.2 head) :
    let after := bellmanPostHeadRaw input head (some tool) good bad
    let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
    let allocated := bellmanAllocateState accounting written head tool
    let executed := bellmanExecuteState accounting allocated head tool
    run input C .uncapped accounting (paidHeadThenRule input head test available after) sample (n + 4) =
      record accounting executed (.advance head) [.advanced head] (advanceLedger executed head) 1 false := by
  dsimp only
  let after := bellmanPostHeadRaw input head (some tool) good bad
  let policy := paidHeadThenPolicy input C ⟨⟨hearly, hcurrent⟩, hpayment⟩ accounting head test available after
    (measurable_bellmanPostHeadRaw input head (some tool) good bad hgood hbad)
  let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  let allocated := bellmanAllocateState accounting written head tool
  let executed := bellmanExecuteState accounting allocated head tool
  let handle : MismatchHandle I := ⟨head, executed.ledger.writeSerial head⟩
  have hr : run input C .uncapped accounting policy.val.rule sample (n + 3) = executed :=
    paidHeadThen_run_wrong_execute input C hearly hcurrent hpayment accounting head hhead test available
      tool htool heligible good bad hgood hbad sample n hstop hwrong
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample (n + 3)
  rw [hr] at hp
  have ht := prefix_truth input C .uncapped accounting policy.val.rule sample.1 _ _ hp
  have hc : executed.cursor = 0 := bellmanHeadWrittenState_cursor input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hw : executed.ledger.written head = some (!executed.ledger.truth head) := by
    rw [ht]
    exact (bellmanHeadWrittenState_written input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))).trans
      (congrArg some (Bool.eq_not_iff.mpr hwrong))
  have hreport : ∃ clock, executed.ledger.reportTime head = some clock := by
    refine ⟨(headReviewState input accounting head (input.truthAt sample.2) (worldTapes input sample.2 head) n).clock, ?_⟩
    simp only [executed, bellmanExecuteState, executeLedger, allocated, bellmanAllocateState, allocateLedger,
      written, bellmanHeadWrittenState, record, reportedWriteLedger, hearly, ↓reduceIte,
      writeLedger, Function.update_self]
  have he : written.ledger.commitments = [] ∧ written.ledger.executions = [] :=
    bellmanHeadWrittenState_empty_corrections input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hcomm : executed.ledger.commitments = [⟨handle, tool, written.clock⟩] := by
    simp only [executed, bellmanExecuteState, executeLedger, allocated, bellmanAllocateState,
      record, allocateLedger, he.1, List.nil_append, handle]
  have hexec : executed.ledger.executions = [⟨handle, tool, allocated.clock⟩] := by
    simp only [executed, bellmanExecuteState, record, executeLedger, allocated, bellmanAllocateState,
      allocateLedger, he.2, List.nil_append, handle]
  have hraw : after sample.1 executed.history = .advance head := by
    have h := bellmanPostHeadRaw_wrong_of_prefix input C hearly .uncapped accounting policy.val.rule
      sample.1 _ _ hp head tool good bad hc hw hreport
    simpa [hcomm, hexec, handle] using h
  have hs : Step input C .uncapped accounting (worldTapes input sample.2) executed (.advance head)
      (record accounting executed (.advance head) [.advanced head] (advanceLedger executed head) 1 false) := by
    have h := Step.advance (input := input) (C := C) (mode := .uncapped) (accounting := accounting)
      (tapes := worldTapes input sample.2) executed head ⟨rfl, hc.trans hhead.symm⟩ (by rw [hw]; simp) (.inl rfl)
    simpa only [hc] using h
  have haction := paidHeadThenRule_after_step input C hearly hcurrent hpayment accounting head test available after
    sample.1 _ _ hp (by rw [hw]; simp) (.advance head) hraw hs (by intro h t hh; cases hh)
  change run input C .uncapped accounting policy.val.rule sample (n + 3 + 1) = _
  apply run_succ_of_step input C .uncapped accounting policy.val.rule sample (n + 3) _
  · rw [hr]
    rfl
  · rw [hr]
    change Step input C .uncapped accounting _ executed
      (paidHeadThenRule input head test available after sample.1 executed.history)
      (record accounting executed (.advance head) [.advanced head] (advanceLedger executed head) 1 false)
    rw [haction]
    exact hs

theorem paidHeadThen_run_wrong_noTool {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hpayment : C.execution = .currentWindow)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hwrong : test.rule.decision sample.1 (worldTapes input sample.2 head) ≠ input.truthAt sample.2 head) :
    let after := bellmanPostHeadRaw input head none good bad
    let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
    run input C .uncapped accounting (paidHeadThenRule input head test available after) sample (n + 2) =
      stopState written true := by
  dsimp only
  let after := bellmanPostHeadRaw input head none good bad
  let policy := paidHeadThenPolicy input C ⟨⟨hearly, hcurrent⟩, hpayment⟩ accounting head test available after
    (measurable_bellmanPostHeadRaw input head none good bad hgood hbad)
  let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hr : run input C .uncapped accounting policy.val.rule sample (n + 1) = written :=
    paidHeadThen_run_write input C accounting head hhead test available after sample n hstop
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample (n + 1)
  rw [hr] at hp
  have ht := prefix_truth input C .uncapped accounting policy.val.rule sample.1 _ _ hp
  have hc : written.cursor = 0 := bellmanHeadWrittenState_cursor input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hw : written.ledger.written head = some (!written.ledger.truth head) := by
    rw [ht]
    exact (bellmanHeadWrittenState_written input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))).trans
      (congrArg some (Bool.eq_not_iff.mpr hwrong))
  have hreport : ∃ clock, written.ledger.reportTime head = some clock := by
    refine ⟨(headReviewState input accounting head (input.truthAt sample.2) (worldTapes input sample.2 head) n).clock, ?_⟩
    simp only [written, bellmanHeadWrittenState, record, reportedWriteLedger, hearly, ↓reduceIte,
      writeLedger, Function.update_self]
  have hraw := bellmanPostHeadRaw_wrong_noTool_of_prefix input C hearly .uncapped accounting policy.val.rule
    sample.1 _ _ hp head good bad hc hw hreport
  have hs : Step input C .uncapped accounting (worldTapes input sample.2) written .abandon (stopState written true) :=
    Step.abandon written rfl
  have haction := paidHeadThenRule_after_step input C hearly hcurrent hpayment accounting head test available after
    sample.1 _ _ hp (by rw [hw]; simp) .abandon hraw hs (by intro h t hh; cases hh)
  change run input C .uncapped accounting policy.val.rule sample (n + 1 + 1) = _
  apply run_succ_of_step input C .uncapped accounting policy.val.rule sample (n + 1) _
  · rw [hr]
    rfl
  · rw [hr]
    change Step input C .uncapped accounting _ written
      (paidHeadThenRule input head test available after sample.1 written.history) (stopState written true)
    rw [haction]
    exact hs

/- The actual correct branch provides the continuation initial view. The
clock is recovered from its real prefix, not assumed as an alignment field. -/

end PDMenu


