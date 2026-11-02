module
public import PaperProofs.Structure.PA17_L01HistoryPrefix_Strategy_002c

/-! Completed-stage used-set increments and the actual native evidence for
an error declaration. Wrong writes are never assumed repaired in Native.Step. -/
@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2400000
namespace PaperProofs.Common.Native.PA17L01HistoryPrefixStrategy002
open PaperProofs.Statistics PaperProofs.Structure
open PaperProofs.Structure.LaminarTree CompactPrice PSTRStatistics.TableAlignment
variable {I : Instance}

theorem toolsBefore_succ_no_stage (history : List (VisibleEvent I)) (stage : Nat)
    (hno : ∀ pair ∈ historyCommitments history, pair.1.stage.val ≠ stage) :
    toolsBefore history (stage + 1) = toolsBefore history stage := by
  ext tool
  rw [mem_toolsBefore, mem_toolsBefore]
  constructor
  · rintro ⟨handle, hm, hs⟩
    have hn := hno (handle, tool) hm
    change handle.stage.val ≠ stage at hn
    exact ⟨handle, hm, by omega⟩
  · rintro ⟨handle, hm, hs⟩
    exact ⟨handle, hm, by omega⟩

theorem toolsBefore_succ_one_stage (history : List (VisibleEvent I)) (stage : Nat)
    (handle : MismatchHandle I) (tool : I.Tool)
    (hm : (handle, tool) ∈ historyCommitments history) (hs : handle.stage.val = stage)
    (hunique : ∀ pair ∈ historyCommitments history, pair.1.stage.val = stage → pair.2 = tool) :
    toolsBefore history (stage + 1) = insert tool (toolsBefore history stage) := by
  ext value
  rw [mem_toolsBefore, Finset.mem_insert, mem_toolsBefore]
  constructor
  · rintro ⟨h, hmem, hlt⟩
    by_cases he : h.stage.val = stage
    · exact Or.inl (hunique (h, value) hmem he)
    · exact Or.inr ⟨h, hmem, by omega⟩
  · rintro (rfl | ⟨h, hmem, hlt⟩)
    · exact ⟨handle, hm, by omega⟩
    · exact ⟨h, hmem, by omega⟩

theorem declaration_replay_correct (history : List (VisibleEvent I))
    (cache : ReferenceReplayCache I) (stage : I.Stage) (hseen : cache.seen = history)
    (hc : referenceReplayCorrect cache stage = true) : CompactPrice.declaration history stage = .correct := by
  cases hw : historyWrite cache.seen stage with
  | none => simp [referenceReplayCorrect, hw] at hc
  | some written =>
    rcases written with ⟨bit, serial⟩
    cases hr : historyReport cache.seen stage with
    | none => simp [referenceReplayCorrect, hw, hr] at hc
    | some reported =>
      rcases reported with ⟨truth, reportedSerial⟩
      simp only [referenceReplayCorrect, hw, hr, decide_eq_true_eq] at hc
      rw [CompactPrice.declaration, ← hseen, hw, hr]
      change (if bit = truth then CompactControllerClaims.Command.correct else .error) = .correct
      exact ite_eq_left hc.1

theorem declaration_of_execution {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (stage : I.Stage) (e : Execution I) (he : e ∈ s.ledger.executions) (hes : e.handle.stage = stage) :
    CompactPrice.declaration s.history stage = .error := by
  have wf := prefix_ledgerWellFormed input C mode accounting rule seed truth tapes hp
  obtain ⟨a, ha, hae, _, _⟩ := wf.backed e he
  obtain ⟨time, hreport, _⟩ := wf.reported a ha
  have hreport' : s.ledger.reportTime stage = some time := by simpa only [hae, hes] using hreport
  have hwrite := (wf.genuine e he).1
  rw [hes] at hwrite
  have hw := prefix_historyWrite input C mode accounting rule seed truth tapes hp stage
  have hr := prefix_historyReport_early input C hearly mode accounting rule seed truth tapes hp stage
  rw [hwrite] at hw
  rw [hreport'] at hr
  simp only [Option.map_some] at hw hr
  rw [CompactPrice.declaration, hw, hr]
  cases s.ledger.truth stage <;> rfl

theorem advance_stage_transition (input : StatisticalInput I) (C : Contract I)
    (hl : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hb : 0 < budget) (hsmall : budget ≤ 1 / 2) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes n s)
    (stage : I.Stage) (hactive : s.halted = false) (hcursor : s.cursor = stage.val)
    (haction : tableRule input available budget limit seed s.history = .advance stage) :
    (CompactPrice.declaration s.history stage = .correct ∧
      stageUsed available s.history (stage.val + 1) = stageUsed available s.history stage.val) ∨
    ∃ tool, CompactPrice.declaration s.history stage = .error ∧
      (tableReply I available stage (toolsBefore s.history stage.val)).tool = some tool ∧
      stageUsed available s.history (stage.val + 1) = insert tool (stageUsed available s.history stage.val) := by
  obtain ⟨cache, aligned, outcomes⟩ := table_advance_info input C hl current.1 accounting available budget hb hsmall limit seed truth tapes hp
    stage hactive hcursor haction
  have hm := prefix_historyCommitments input C .uncapped accounting (tableRule input available budget limit) seed truth tapes hp
  rcases outcomes with ⟨phase, correct⟩ | ⟨tool, phase⟩
  · apply Or.inl
    refine ⟨declaration_replay_correct s.history cache stage aligned.seen correct, ?_⟩
    have fields := aligned.current_fields stage hcursor
    simp only [phase, referenceCurrentLedgerFits] at fields
    unfold stageUsed
    rw [toolsBefore_succ_no_stage s.history stage.val (by
      intro pair hpair heq
      rw [hm] at hpair
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hpair
      exact fields.2.2.1 a ha (Fin.ext heq))]
  · have fields := aligned.current_fields stage hcursor
    simp only [phase, referenceCurrentLedgerFits] at fields
    obtain ⟨e, he, hstage, htool⟩ := fields.2
    have wf := prefix_ledgerWellFormed input C .uncapped accounting (tableRule input available budget limit) seed truth tapes hp
    obtain ⟨a, ha, hae, hat, _⟩ := wf.backed e he
    have has : a.handle.stage = stage := (congrArg MismatchHandle.stage hae).trans hstage
    have hatool : a.tool = tool := hat.trans htool
    have hpair : (a.handle, tool) ∈ historyCommitments s.history := by
      rw [hm]
      exact List.mem_map.mpr ⟨a, ha, by rw [hatool]⟩
    have pick := prefix_commit_selected input C hl current accounting available budget hb hsmall limit seed truth tapes hp a ha
    apply Or.inr
    refine ⟨tool, declaration_of_execution input C current.1 .uncapped accounting
      (tableRule input available budget limit) seed truth tapes hp stage e he hstage, ?_, ?_⟩
    · simpa only [has, hatool] using pick
    · unfold stageUsed
      rw [toolsBefore_succ_one_stage s.history stage.val a.handle tool hpair (congrArg Fin.val has) (by
        intro pair hp hps
        rw [hm] at hp
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
        have hbs : b.handle.stage = stage := Fin.ext hps
        have heq : b = a := List.inj_on_of_nodup_map wf.commitment_stages hb ha (hbs.trans has.symm)
        rw [heq, hatool])]
      simp

end PaperProofs.Common.Native.PA17L01HistoryPrefixStrategy002
