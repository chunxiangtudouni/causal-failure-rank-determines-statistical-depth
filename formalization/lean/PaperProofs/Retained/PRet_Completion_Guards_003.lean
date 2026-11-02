module

public import PaperProofs.Retained.PRet_Completion_Choices_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics

namespace PRetCompletion

variable {I : Instance}

theorem pending_spec (history : List (VisibleEvent I)) (stage : I.Stage) (found : pending I history = some stage) :
    stage ∈ reportedErrors I history I.stageCount ∧
      (historyExecutions history).any (fun e => e.1.stage == stage) = false := by
  classical
  have hp := List.find?_some (p := fun stage : I.Stage => decide (stage ∈ reportedErrors I history I.stageCount) &&
    !((historyExecutions history).any (fun e => e.1.stage == stage))) found
  refine ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp hp).1,?_⟩
  cases value : (historyExecutions history).any (fun e => e.1.stage == stage) <;> simp_all

theorem reportedErrors_full (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) {Seed : Type*} (source : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {state : State I} (path : Prefix input C .uncapped accounting source seed truth tapes n state) :
    reportedErrors I state.history I.stageCount = ordinaryMismatches state.ledger := by
  rw [PRetActualReportedErrors048.prefix_reportedErrors input C hearly .uncapped accounting source seed truth tapes path]
  have all : pastStages I I.stageCount = Finset.univ := by
    ext stage
    have bound : stage.val < I.stageCount := stage.isLt
    simp only [pastStages,Finset.mem_filter,Finset.mem_univ,true_and,bound]
  rw [all,Finset.inter_univ]

theorem commitment_valid (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    {Seed : Type*} (source : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {state : State I} (path : Prefix input C .uncapped accounting source seed truth tapes n state)
    (allocation : Commitment I) (member : allocation ∈ state.ledger.commitments) : validHandle state allocation.handle := by
  have invariant := prefix_invariant input C .uncapped accounting source seed truth tapes path
  obtain ⟨time,reported,_before⟩ := invariant.wellFormed.reported allocation member
  exact ⟨(invariant.commitment_genuine allocation member).1,
    (invariant.commitment_genuine allocation member).2,time,reported⟩

set_option backward.isDefEq.respectTransparency.types false in
theorem terminal_good_step (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {state : State I}
    (path : Prefix input C .uncapped accounting (retainedRule input budget limit) seed truth tapes n state)
    (active : state.halted = false) (matchable : Matchable I (ordinaryMismatches state.ledger)) :
    ∃ next, Step input C .uncapped accounting tapes state (terminalMatchingAction I state.history) next ∧
      terminalMatchingAction I state.history ≠ .abandon := by
  classical
  let errors := reportedErrors I state.history I.stageCount
  have errorsEq := reportedErrors_full input C hretained.1 accounting (retainedRule input budget limit) seed truth tapes path
  have matchableReported : Matchable I errors := by
    change Matchable I (reportedErrors I state.history I.stageCount)
    rw [errorsEq]
    exact matchable
  have canAssign : (firstAssignment I errors).isSome = true :=
    ((RootRetainedQueries.terminalAssignmentCorrect I).2 errors).mp matchableReported
  cases first : firstAssignment I errors with
  | none => rw [first] at canAssign; cases canAssign
  | some assignment =>
    have valid := (RootRetainedQueries.terminalAssignmentCorrect I).1 errors assignment first
    have equation : terminalMatchingAction I state.history =
        match pending I state.history with
        | none => .stop
        | some stage => match assignment[stage.val]?.join,referenceVisibleHandle state.history stage with
          | some tool,some handle => match (historyCommitments state.history).find? (fun a => a.1.stage == stage) with
            | none => .allocate handle tool
            | some old => if old.2 = tool then .execute handle tool else .abandon
          | _,_ => .abandon := by
      unfold terminalMatchingAction
      dsimp only
      change (match firstAssignment I errors with | none => Action.abandon | some assignment => _) = _
      rw [first]
      rfl
    cases found : pending I state.history with
    | none =>
      rw [found] at equation
      refine ⟨stopState state false,?_,?_⟩
      · rw [equation]
        exact Step.stop state active
      · rw [equation]
        intro impossible
        cases impossible
    | some stage =>
      obtain ⟨wrong,noExec⟩ := pending_spec state.history stage found
      have assignmentStage := valid.2.1 stage
      rw [ite_eq_left wrong] at assignmentStage
      obtain ⟨tool,slot,compatible⟩ := assignmentStage
      have ordinary : stage ∈ ordinaryMismatches state.ledger := errorsEq ▸ wrong
      have hwrong := (mem_ordinaryMismatches state.ledger stage).mp ordinary
      obtain ⟨time,reported⟩ := PRetEarlyReports034.prefix_written_reported input C hretained.1 .uncapped accounting
        (retainedRule input budget limit) seed truth tapes path stage (by rw [hwrong]; exact Option.some_ne_none _)
      let handle : MismatchHandle I := ⟨stage,state.ledger.writeSerial stage⟩
      have genuine : validHandle state handle := ⟨hwrong,rfl,time,reported⟩
      have visible := prefix_visibleHandle_of_valid input C hretained.1 .uncapped accounting
        (retainedRule input budget limit) seed truth tapes path handle genuine
      rw [found] at equation
      dsimp only at equation
      rw [slot] at equation
      rw [visible] at equation
      dsimp only at equation
      have uncorrected : ∀ execution ∈ state.ledger.executions, execution.handle.stage ≠ stage := by
        intro execution member equalStage
        have visibleExecution : (execution.handle,execution.tool) ∈ historyExecutions state.history := by
          rw [prefix_historyExecutions input C .uncapped accounting (retainedRule input budget limit) seed truth tapes path]
          exact List.mem_map.mpr ⟨execution,member,rfl⟩
        exact (List.any_eq_false.mp noExec) _ visibleExecution (beq_iff_eq.mpr equalStage)
      cases old : (historyCommitments state.history).find? (fun a => a.1.stage == stage) with
      | none =>
        rw [old] at equation
        have unallocated : ∀ allocation ∈ state.ledger.commitments, allocation.handle.stage ≠ stage := by
          intro allocation member equalStage
          apply (List.find?_eq_none.mp old) (allocation.handle,allocation.tool)
          · rw [prefix_historyCommitments input C .uncapped accounting (retainedRule input budget limit) seed truth tapes path]
            exact List.mem_map.mpr ⟨allocation,member,rfl⟩
          · exact beq_iff_eq.mpr equalStage
        have unused : ∀ allocation ∈ state.ledger.commitments, allocation.tool ≠ tool := by
          intro allocation member equalTool
          have chosen := prefix_assignmentChoices input C hretained.1 accounting budget limit seed truth tapes path allocation member assignment first
          have sameStage : allocation.handle.stage = stage :=
            valid.2.2 allocation.handle.stage stage tool (by rw [← equalTool]; exact chosen) slot
          exact unallocated allocation member sameStage
        refine ⟨record accounting state (.allocate handle tool) [.committed handle tool]
          (allocateLedger state handle tool) state.cursor false,?_,?_⟩
        · rw [equation]
          refine Step.allocate state handle tool active genuine compatible unused unallocated ?_ (Or.inl rfl)
          simp only [allocationOpen,hretained.2.1,reduceCtorEq,false_implies]
        · rw [equation]
          intro impossible
          cases impossible
      | some pair =>
        have pairMember := List.mem_of_find?_eq_some old
        rw [prefix_historyCommitments input C .uncapped accounting (retainedRule input budget limit) seed truth tapes path] at pairMember
        obtain ⟨allocation,member,pairEq⟩ := List.mem_map.mp pairMember
        have pairStage : pair.1.stage = stage := beq_iff_eq.mp
          (List.find?_some (p := fun a : MismatchHandle I × I.Tool => a.1.stage == stage) old)
        have allocHandle : allocation.handle = pair.1 := congrArg Prod.fst pairEq
        have allocTool : allocation.tool = pair.2 := congrArg Prod.snd pairEq
        have allocStage : allocation.handle.stage = stage := (congrArg MismatchHandle.stage allocHandle).trans pairStage
        have chosen := prefix_assignmentChoices input C hretained.1 accounting budget limit seed truth tapes path allocation member assignment first
        rw [allocStage,slot] at chosen
        have equalTool : pair.2 = tool := allocTool.symm.trans (Option.some.inj chosen).symm
        rw [old] at equation
        dsimp only at equation
        rw [ite_eq_left equalTool] at equation
        have oldVisible := prefix_visibleHandle_of_valid input C hretained.1 .uncapped accounting
          (retainedRule input budget limit) seed truth tapes path allocation.handle
          (commitment_valid input C accounting (retainedRule input budget limit) seed truth tapes path allocation member)
        rw [allocStage,visible] at oldVisible
        have equalHandle : allocation.handle = handle := (Option.some.inj oldVisible).symm
        have unused : ∀ execution ∈ state.ledger.executions, execution.tool ≠ tool := by
          intro execution executed equal
          have invariant := prefix_invariant input C .uncapped accounting (retainedRule input budget limit) seed truth tapes path
          obtain ⟨backing,backed,backHandle,backTool,_time⟩ := invariant.wellFormed.backed execution executed
          have equalAllocation : backing = allocation :=
            List.inj_on_of_nodup_map invariant.wellFormed.commitment_tools backed member
              (backTool.trans (equal.trans (allocTool.trans equalTool).symm))
          apply uncorrected execution executed
          rw [← backHandle,equalAllocation,equalHandle]
        refine ⟨record accounting state (.execute handle tool) [.executed handle tool]
          (executeLedger state handle tool) state.cursor false,?_,?_⟩
        · rw [equation]
          refine Step.execute state handle tool active genuine compatible
            ⟨allocation,member,equalHandle,allocTool.trans equalTool⟩ unused uncorrected ?_ (Or.inl rfl)
          simp only [executionOpen,hretained.2.2,reduceCtorEq,false_implies]
        · rw [equation]
          intro impossible
          cases impossible

end PRetCompletion
