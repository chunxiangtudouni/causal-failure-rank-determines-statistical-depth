module
public import PaperProofs.Structure.PA17_L01HistoryPrefix_Strategy_002b

/-! Every actual commitment retains the original TABLE callback equality at
its own stage-entry used set. Later commitments cannot alter that earlier set. -/
@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2400000
namespace PaperProofs.Common.Native.PA17L01HistoryPrefixStrategy002
open PaperProofs.Statistics PaperProofs.Structure
open PaperProofs.Structure.LaminarTree CompactPrice PSTRStatistics.TableAlignment
variable {I : Instance}

theorem step_toolsBefore (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hwindow : C.allocation = .currentWindow)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I} (step : Step input C mode accounting tapes s action next)
    (stage : Nat) (hs : stage ≤ s.cursor) : toolsBefore next.history stage = toolsBefore s.history stage := by
  cases step with
  | allocate handle tool active valid compatible unused unallocated window resources =>
    change toolsBefore (s.history ++ [.committed handle tool]) stage = _
    rw [toolsBefore_commit]
    have hc := window hwindow
    exact ite_eq_right (by omega)
  | review =>
    apply toolsBefore_congr
    simp [record, historyCommitments, List.filterMap_append, eventCommitment]
  | write =>
    apply toolsBefore_congr
    simp [record, writeResponses, hearly, historyCommitments, List.filterMap_append, eventCommitment]
  | execute =>
    apply toolsBefore_congr
    simp [record, historyCommitments, List.filterMap_append, eventCommitment]
  | advance =>
    apply toolsBefore_congr
    simp [record, historyCommitments, List.filterMap_append, eventCommitment]
  | stop =>
    apply toolsBefore_congr
    simp [stopState, historyCommitments, List.filterMap_append, eventCommitment]
  | abandon =>
    apply toolsBefore_congr
    simp [stopState, historyCommitments, List.filterMap_append, eventCommitment]

theorem prefix_toolsBefore_current_eq_used {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hwindow : C.allocation = .currentWindow)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (stage : I.Stage) (hc : s.cursor = stage.val)
    (hno : ∀ a ∈ s.ledger.commitments, a.handle.stage ≠ stage) :
    toolsBefore s.history stage.val = historyUsed s.history := by
  apply toolsBefore_eq_used
  intro pair hm
  rw [prefix_historyCommitments input C mode accounting rule seed truth tapes hp] at hm
  obtain ⟨a, ha, heq⟩ := List.mem_map.mp hm
  subst pair
  have hb := prefix_commitment_stage_le input C hearly hwindow mode accounting rule seed truth tapes hp a ha
  have hn := hno a ha
  have hnv : a.handle.stage.val ≠ stage.val := fun he => hn (Fin.ext he)
  change a.handle.stage.val < stage.val
  omega

theorem prefix_commit_selected (input : StatisticalInput I) (C : Contract I)
    (hl : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hb : 0 < budget) (hsmall : budget ≤ 1 / 2) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes n s) :
    ∀ a ∈ s.ledger.commitments,
      (tableReply I available a.handle.stage (toolsBefore s.history a.handle.stage.val)).tool = some a.tool := by
  induction hp with
  | initial => simp [initial]
  | @next n s next earlier step ih =>
    generalize haction : tableRule input available budget limit seed s.history = action at step
    have bounds := prefix_commitment_stage_le input C current.1 current.2 .uncapped accounting
      (tableRule input available budget limit) seed truth tapes earlier
    have frame := step_toolsBefore input C current.1 current.2 .uncapped accounting tapes step
    have oldSelected (a : Commitment I) (ha : a ∈ s.ledger.commitments) :
        (tableReply I available a.handle.stage (toolsBefore next.history a.handle.stage.val)).tool = some a.tool := by
      rw [frame a.handle.stage.val (bounds a ha)]
      exact ih a ha
    cases step with
    | allocate handle tool active valid compatible unused unallocated window resources =>
      have hcursor := window current.2
      obtain ⟨cache, aligned, phase, pick⟩ := table_allocate_info input C hl current.1 accounting
        available budget hb hsmall limit seed truth tapes earlier handle tool active hcursor haction
      have hused := prefix_toolsBefore_current_eq_used input C current.1 current.2 .uncapped accounting
        (tableRule input available budget limit) seed truth tapes earlier handle.stage hcursor unallocated
      have hentry : historyUsed cache.entryHistory = historyUsed s.history := by
        simpa only [referenceEntryToolsFit, phase, aligned.seen] using aligned.entry_tools
      change ∀ a ∈ s.ledger.commitments ++ [⟨handle, tool, s.clock⟩],
        (tableReply I available a.handle.stage
          (toolsBefore (s.history ++ [.committed handle tool]) a.handle.stage.val)).tool = some a.tool
      have newSelected : (tableReply I available handle.stage
          (toolsBefore (s.history ++ [.committed handle tool]) handle.stage.val)).tool = some tool := by
        rw [toolsBefore_commit, ite_eq_right (Nat.lt_irrefl _), hused, ← hentry]
        exact pick
      intro a ha
      rcases List.mem_append.mp ha with hold | hnew
      · exact oldSelected a hold
      · have heq := List.mem_singleton.mp hnew
        subst a
        exact newSelected
    | review =>
      change ∀ a ∈ s.ledger.commitments, _
      intro a ha
      exact oldSelected a ha
    | write =>
      simpa only [record, reportedWriteLedger, current.1, ite_true, writeLedger] using oldSelected
    | execute => exact oldSelected
    | advance => exact oldSelected
    | stop => exact oldSelected
    | abandon => exact oldSelected

end PaperProofs.Common.Native.PA17L01HistoryPrefixStrategy002
