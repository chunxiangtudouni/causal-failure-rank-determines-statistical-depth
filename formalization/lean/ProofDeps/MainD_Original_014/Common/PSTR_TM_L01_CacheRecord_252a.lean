module
public import Structure.PA17_L01HistoryPrefix_Strategy_002c

/-! The cache's entry used-set is derived from the REAL TABLE Prefix.
Current-stage commitments are excluded by stage filtering. Allocated and
executed phases use the actual ledger's two Nodup invariants and backing,
not a supplied cache/records correctness hypothesis. No new H0 is used. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRTML01CacheRecord252
open PaperProofs.Statistics PaperProofs.Structure
open PaperProofs.Structure.LaminarTree CompactPrice PSTRStatistics.TableAlignment
open PA17L01HistoryPrefixStrategy002

variable {I : Instance} {Seed : Type*}

private theorem prefix_used_mem (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s) (tool : I.Tool) :
    tool ∈ historyUsed s.history ↔ ∃ a ∈ s.ledger.commitments, a.tool = tool := by
  rw [historyUsed,prefix_historyCommitments input C mode accounting rule seed truth tapes hp,List.map_map]
  simp only [List.mem_toFinset,List.mem_map,Function.comp_apply]

private theorem prefix_before_mem (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (stage : Nat) (tool : I.Tool) :
    tool ∈ toolsBefore s.history stage ↔
      ∃ a ∈ s.ledger.commitments, a.tool = tool ∧ a.handle.stage.val < stage := by
  rw [mem_toolsBefore,prefix_historyCommitments input C mode accounting rule seed truth tapes hp]
  constructor
  · rintro ⟨handle,member,older⟩
    obtain ⟨a,present,equal⟩ := List.mem_map.mp member
    have handleEq : a.handle = handle := congrArg Prod.fst equal
    have toolEq : a.tool = tool := congrArg Prod.snd equal
    exact ⟨a,present,toolEq,by simpa only [handleEq] using older⟩
  · rintro ⟨a,present,equal,older⟩
    refine ⟨a.handle,List.mem_map.mpr ⟨a,present,?_⟩,older⟩
    rw [equal]

/-- A real current-stage commitment contributes exactly the one tool
removed by the stage-entry filter. Both uniqueness facts come from the
actual Prefix ledger, never from an assumed candidate replay invariant. -/
theorem prefix_before_erase_current (input : StatisticalInput I) (C : Contract I)
    (current : C.IsCurrentAllocation) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (a : Commitment I) (present : a ∈ s.ledger.commitments) (stage : I.Stage)
    (cursor : s.cursor = stage.val) (sameStage : a.handle.stage = stage) :
    toolsBefore s.history stage.val = (historyUsed s.history).erase a.tool := by
  classical
  have wf := prefix_ledgerWellFormed input C mode accounting rule seed truth tapes hp
  have bounds := prefix_commitment_stage_le input C current.1 current.2 mode accounting rule seed truth tapes hp
  ext tool
  rw [prefix_before_mem input C mode accounting rule seed truth tapes hp,
    Finset.mem_erase,prefix_used_mem input C mode accounting rule seed truth tapes hp]
  constructor
  · rintro ⟨b,member,selected,older⟩
    refine ⟨?_,b,member,selected⟩
    intro sameTool
    have equal : b = a := List.inj_on_of_nodup_map wf.commitment_tools member present (selected.trans sameTool)
    subst b
    rw [sameStage] at older
    exact Nat.lt_irrefl _ older
  · rintro ⟨different,b,member,selected⟩
    have before := bounds b member
    have unequal : b.handle.stage ≠ stage := by
      intro same
      have equal : b = a := List.inj_on_of_nodup_map wf.commitment_stages member present (same.trans sameStage.symm)
      subst b
      exact different selected.symm
    have values : b.handle.stage.val ≠ stage.val := fun equal => unequal (Fin.ext equal)
    refine ⟨b,member,selected,?_⟩
    rw [cursor] at before
    omega

private theorem aligned_entry_before (input : StatisticalInput I) (C : Contract I)
    (current : C.IsCurrentAllocation) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : Rat) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes n s)
    (cache : ReferenceReplayCache I) (aligned : TableStateAligned input available budget cache s)
    (stage : I.Stage) (cursor : s.cursor = stage.val) :
    historyUsed cache.entryHistory = toolsBefore s.history stage.val := by
  have fields := aligned.current_fields stage cursor
  have entries := aligned.entry_tools
  have wf := prefix_ledgerWellFormed input C .uncapped accounting
    (tableRule input available budget limit) seed truth tapes hp
  cases phase : cache.phase with
  | testing =>
    simp only [phase,referenceCurrentLedgerFits] at fields
    have entry : historyUsed cache.entryHistory = historyUsed s.history := by
      simpa only [referenceEntryToolsFit,phase,aligned.seen] using entries
    exact entry.trans (prefix_toolsBefore_current_eq_used input C current.1 current.2 .uncapped accounting
      (tableRule input available budget limit) seed truth tapes hp stage cursor fields.2.2.1).symm
  | written =>
    simp only [phase,referenceCurrentLedgerFits] at fields
  | reported =>
    simp only [phase,referenceCurrentLedgerFits] at fields
    have entry : historyUsed cache.entryHistory = historyUsed s.history := by
      simpa only [referenceEntryToolsFit,phase,aligned.seen] using entries
    exact entry.trans (prefix_toolsBefore_current_eq_used input C current.1 current.2 .uncapped accounting
      (tableRule input available budget limit) seed truth tapes hp stage cursor fields.2.2.1).symm
  | allocated tool =>
    simp only [phase,referenceCurrentLedgerFits] at fields
    obtain ⟨handle,handleStage,_valid,_compatible,⟨a,member,handleEq,toolEq⟩,_unused,_executionStage⟩ := fields
    have stageEq : a.handle.stage = stage := (congrArg MismatchHandle.stage handleEq).trans handleStage
    have before := prefix_before_erase_current input C current .uncapped accounting
      (tableRule input available budget limit) seed truth tapes hp a member stage cursor stageEq
    rw [toolEq] at before
    have fit : insert tool (historyUsed cache.entryHistory) = historyUsed s.history ∧
        tool ∉ historyUsed cache.entryHistory := by
      simpa only [referenceEntryToolsFit,phase,aligned.seen] using entries
    have erased : (historyUsed s.history).erase tool = historyUsed cache.entryHistory := by
      rw [←fit.1]
      exact Finset.erase_insert fit.2
    exact erased.symm.trans before.symm
  | executed tool =>
    simp only [phase,referenceCurrentLedgerFits] at fields
    obtain ⟨_written,e,member,executionStage,executionTool⟩ := fields
    obtain ⟨a,present,handleEq,toolEq,_time⟩ := wf.backed e member
    have stageEq : a.handle.stage = stage := (congrArg MismatchHandle.stage handleEq).trans executionStage
    have selected : a.tool = tool := toolEq.trans executionTool
    have before := prefix_before_erase_current input C current .uncapped accounting
      (tableRule input available budget limit) seed truth tapes hp a present stage cursor stageEq
    rw [selected] at before
    have fit : insert tool (historyUsed cache.entryHistory) = historyUsed s.history ∧
        tool ∉ historyUsed cache.entryHistory := by
      simpa only [referenceEntryToolsFit,phase,aligned.seen] using entries
    have erased : (historyUsed s.history).erase tool = historyUsed cache.entryHistory := by
      rw [←fit.1]
      exact Finset.erase_insert fit.2
    exact erased.symm.trans before.symm

/-- All cache correctness is DISCHARGED from the original actual Prefix.
No supplied cache alignment, record correctness, success event or H0.
The stronger statement includes halted prefixes as well as active clocks. -/
theorem actual_cache_entry (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : Rat)
    (positive : 0 < budget) (small : budget ≤ 1/2) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes n s) :
    ∃ cache, TableStateAligned input available budget cache s ∧
      ∀ stage : I.Stage, s.cursor = stage.val → historyUsed cache.entryHistory = toolsBefore s.history stage.val := by
  obtain ⟨cache,aligned⟩ := prefix_tableStateAligned laminar input C current.1 accounting
    available budget positive small limit seed truth tapes hp
  exact ⟨cache,aligned,fun stage cursor => aligned_entry_before input C current accounting
    available budget limit seed truth tapes hp cache aligned stage cursor⟩

/-- A computed Option equation with no candidate-cache premise. -/
theorem actual_entry_used (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : Rat)
    (positive : 0 < budget) (small : budget ≤ 1/2) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes n s)
    (stage : I.Stage) (cursor : s.cursor = stage.val) :
    (tableReplay input available budget s.history).map (fun cache => historyUsed cache.entryHistory) =
      some (toolsBefore s.history stage.val) := by
  obtain ⟨cache,aligned,used⟩ := actual_cache_entry input C laminar current accounting available budget positive small
    limit seed truth tapes hp
  rw [aligned.parsed]
  exact congrArg some (used stage cursor)

end PaperProofs.Common.Native.PSTRTML01CacheRecord252
