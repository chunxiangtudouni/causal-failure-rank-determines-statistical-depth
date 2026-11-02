module
public import PaperProofs.Structure.PA17_L01HistoryPrefix_Strategy_002a

/-! The original TABLE rule's real allocate and advance actions. These facts
are obtained from its own replay/cache, without identifying any generic run. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2200000
namespace PaperProofs.Common.Native.PA17L01HistoryPrefixStrategy002
open PaperProofs.Statistics PaperProofs.Structure
open PaperProofs.Structure.LaminarTree CompactPrice PSTRStatistics.TableAlignment
variable {I : Instance}

theorem table_allocate_info (input : StatisticalInput I) (C : Contract I)
    (hl : LaminarSchedule I.compatibility) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hb : 0 < budget) (hsmall : budget ≤ 1 / 2) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes n s)
    (handle : MismatchHandle I) (tool : I.Tool) (hactive : s.halted = false)
    (hcursor : s.cursor = handle.stage.val)
    (ha : tableRule input available budget limit seed s.history = .allocate handle tool) :
    ∃ cache, TableStateAligned input available budget cache s ∧ cache.phase = .reported ∧
      (tableReply I available handle.stage (historyUsed cache.entryHistory)).tool = some tool := by
  obtain ⟨cache, aligned⟩ := prefix_tableStateAligned hl input C hearly accounting available budget hb hsmall limit seed truth tapes hp
  have hc := tableRule_eq_candidate_of_prefix hl input C hearly accounting available budget hb hsmall limit seed truth tapes hp
  have ha' : tableCandidate input available budget limit s.history = .allocate handle tool := hc.symm.trans ha
  have hh : cache.halted = false := aligned.halted.trans hactive
  have hs := tableStateAligned_stage input available budget cache s aligned handle.stage hcursor
  cases phase : cache.phase with
  | testing =>
    have ht : tableTestingAction input available budget limit cache handle.stage = .allocate handle tool := by
      simpa only [tableCandidate, aligned.parsed, hh, Bool.false_eq_true, ite_false, hs, phase] using ha'
    rcases PSTRStatistics.tableTestingAction_supported input available budget limit cache handle.stage with hr | ⟨bit, hw⟩ | ha
    · rw [hr] at ht; cases ht
    · rw [hw] at ht; cases ht
    · rw [ha] at ht; cases ht
  | written => simp only [tableCandidate, aligned.parsed, hh, Bool.false_eq_true, ite_false, hs, phase] at ha'; cases ha'
  | reported =>
    cases correct : referenceReplayCorrect cache handle.stage with
    | true => simp only [tableCandidate, aligned.parsed, hh, Bool.false_eq_true, ite_false, hs, phase, correct, ite_true] at ha'; cases ha'
    | false =>
      cases risk : referenceReplayRisk budget cache with
      | none => simp only [tableCandidate, aligned.parsed, hh, Bool.false_eq_true, ite_false, hs, phase, correct, risk] at ha'; cases ha'
      | some value =>
        cases visible : referenceVisibleHandle s.history handle.stage with
        | none => simp only [tableCandidate, aligned.parsed, hh, Bool.false_eq_true, ite_false, hs, phase, correct, risk, visible] at ha'; cases ha'
        | some chosenHandle =>
          cases pick : (tableReply I available handle.stage (historyUsed cache.entryHistory)).tool with
          | none => simp only [tableCandidate, aligned.parsed, hh, Bool.false_eq_true, ite_false, hs, phase, correct, risk, visible, pick] at ha'; cases ha'
          | some chosenTool =>
            simp only [tableCandidate, aligned.parsed, hh, Bool.false_eq_true, ite_false, hs, phase, correct, risk, visible, pick] at ha'
            injection ha' with _ htool
            exact ⟨cache, aligned, phase, pick.trans (congrArg some htool)⟩
  | allocated value =>
    cases visible : referenceVisibleHandle s.history handle.stage <;>
      simp only [tableCandidate, aligned.parsed, hh, Bool.false_eq_true, ite_false, hs, phase, visible] at ha' <;> cases ha'
  | executed value => simp only [tableCandidate, aligned.parsed, hh, Bool.false_eq_true, ite_false, hs, phase] at ha'; cases ha'

theorem table_advance_info (input : StatisticalInput I) (C : Contract I)
    (hl : LaminarSchedule I.compatibility) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hb : 0 < budget) (hsmall : budget ≤ 1 / 2) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes n s)
    (stage : I.Stage) (hactive : s.halted = false) (hcursor : s.cursor = stage.val)
    (ha : tableRule input available budget limit seed s.history = .advance stage) :
    ∃ cache, TableStateAligned input available budget cache s ∧
      ((cache.phase = .reported ∧ referenceReplayCorrect cache stage = true) ∨ ∃ tool, cache.phase = .executed tool) := by
  obtain ⟨cache, aligned⟩ := prefix_tableStateAligned hl input C hearly accounting available budget hb hsmall limit seed truth tapes hp
  have hc := tableRule_eq_candidate_of_prefix hl input C hearly accounting available budget hb hsmall limit seed truth tapes hp
  have ha' : tableCandidate input available budget limit s.history = .advance stage := hc.symm.trans ha
  have hh : cache.halted = false := aligned.halted.trans hactive
  have hs := tableStateAligned_stage input available budget cache s aligned stage hcursor
  cases phase : cache.phase with
  | testing =>
    have ht : tableTestingAction input available budget limit cache stage = .advance stage := by
      simpa only [tableCandidate, aligned.parsed, hh, Bool.false_eq_true, ite_false, hs, phase] using ha'
    rcases PSTRStatistics.tableTestingAction_supported input available budget limit cache stage with hr | ⟨bit, hw⟩ | ha
    · rw [hr] at ht; cases ht
    · rw [hw] at ht; cases ht
    · rw [ha] at ht; cases ht
  | written => simp only [tableCandidate, aligned.parsed, hh, Bool.false_eq_true, ite_false, hs, phase] at ha'; cases ha'
  | reported =>
    cases correct : referenceReplayCorrect cache stage with
    | true => exact ⟨cache, aligned, Or.inl ⟨phase, correct⟩⟩
    | false =>
      cases risk : referenceReplayRisk budget cache <;>
        cases visible : referenceVisibleHandle s.history stage <;>
        cases pick : (tableReply I available stage (historyUsed cache.entryHistory)).tool <;>
        simp only [tableCandidate, aligned.parsed, hh, Bool.false_eq_true, ite_false, hs, phase, correct, risk, visible, pick] at ha' <;> cases ha'
  | allocated value =>
    cases visible : referenceVisibleHandle s.history stage <;>
      simp only [tableCandidate, aligned.parsed, hh, Bool.false_eq_true, ite_false, hs, phase, visible] at ha' <;> cases ha'
  | executed value => exact ⟨cache, aligned, Or.inr ⟨value, phase⟩⟩

end PaperProofs.Common.Native.PA17L01HistoryPrefixStrategy002
