module

public import PaperProofs.Paid.PDROC_FirstFailure_003
public import PaperProofs.Paid.PDROC_TruthfulContinuation_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

/-- A real correction extension preserves all ordinary writes, truths,
cursor and prior physical executions; the current stage is now corrected. -/
def CurrentCorrectionExtension (s next : State I) (stage : I.Stage) : Prop :=
  next.halted = false ∧ next.cursor = s.cursor ∧ next.ledger.written = s.ledger.written ∧
    next.ledger.truth = s.ledger.truth ∧ s.ledger.executions.Sublist next.ledger.executions ∧
    ∃ execution ∈ next.ledger.executions, execution.handle.stage = stage

theorem execute_currentCommitment (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input) (s : State I)
    (hinv : Invariant C s) (ha : s.halted = false) (stage : I.Stage) (hcursor : s.cursor = stage.val)
    (hnone : ∀ execution ∈ s.ledger.executions, execution.handle.stage ≠ stage)
    (commitment : Commitment I) (hc : commitment ∈ s.ledger.commitments)
    (hstage : commitment.handle.stage = stage) (hcompatible : commitment.tool ∈ I.eligible stage) :
    ∃ next : State I, Step input C .uncapped accounting tapes s
        (.execute commitment.handle commitment.tool) next ∧ CurrentCorrectionExtension s next stage := by
  have hg := hinv.commitment_genuine commitment hc
  obtain ⟨time, hreport, _⟩ := hinv.wellFormed.reported commitment hc
  have hvalid : validHandle s commitment.handle := ⟨hg.1, hg.2, time, hreport⟩
  have hunused : ∀ execution ∈ s.ledger.executions, execution.tool ≠ commitment.tool := by
    intro execution he htool
    obtain ⟨old, hold, hhandle, holdtool, _⟩ := hinv.wellFormed.backed execution he
    have heq : old = commitment := List.inj_on_of_nodup_map hinv.wellFormed.commitment_tools hold hc (holdtool.trans htool)
    have hexstage : execution.handle.stage = stage := by rw [← hhandle, heq, hstage]
    exact hnone execution he hexstage
  let next := record accounting s (.execute commitment.handle commitment.tool)
    [.executed commitment.handle commitment.tool] (executeLedger s commitment.handle commitment.tool) s.cursor false
  have hstep : Step input C .uncapped accounting tapes s (.execute commitment.handle commitment.tool) next :=
    .execute s commitment.handle commitment.tool ha hvalid (hstage ▸ hcompatible)
      ⟨commitment, hc, rfl, rfl⟩ hunused (by simpa only [hstage] using hnone)
      (fun _ => by simpa only [hstage] using hcursor) (Or.inl rfl)
  refine ⟨next, hstep, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact List.sublist_append_left _ _
  · exact ⟨⟨commitment.handle, commitment.tool, s.clock⟩, by simp [next, record, executeLedger], hstage⟩

theorem currentCorrectionExtension_trans {s middle next : State I} {stage : I.Stage}
    (hm : middle.halted = false ∧ middle.cursor = s.cursor ∧ middle.ledger.written = s.ledger.written ∧
      middle.ledger.truth = s.ledger.truth ∧ middle.ledger.executions = s.ledger.executions)
    (hn : CurrentCorrectionExtension middle next stage) : CurrentCorrectionExtension s next stage := by
  rcases hm with ⟨_, hcursor, hwritten, htruth, hexecution⟩
  rcases hn with ⟨ha, hc, hw, ht, he, hex⟩
  exact ⟨ha, hc.trans hcursor, hw.trans hwritten, ht.trans htruth, hexecution ▸ he, hex⟩

/-- If a wrong current write is not in the exhausted case, a genuine old
commitment or unused physical right supplies an actual correction now. -/
theorem currentRepair_exists (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input) (s : State I)
    (hinv : Invariant C s) (ha : s.halted = false) (stage : I.Stage) (hcursor : s.cursor = stage.val)
    (hwrong : s.ledger.written stage = some (!s.ledger.truth stage))
    (hreport : ∃ time, s.ledger.reportTime stage = some time)
    (hnone : ∀ execution ∈ s.ledger.executions, execution.handle.stage ≠ stage)
    (hnotexhausted : ¬ ExhaustedUnrepairedError s stage)
    (hpool : ∀ tool : I.Tool, tool ∈ I.eligible stage) :
    ∃ next : State I,
      Relation.ReflTransGen (fun before after => ∃ action,
        Step input C .uncapped accounting tapes before action after) s next ∧
      CurrentCorrectionExtension s next stage := by
  classical
  by_cases hcommit : ∃ commitment ∈ s.ledger.commitments, commitment.handle.stage = stage
  · obtain ⟨commitment, hc, hstage⟩ := hcommit
    obtain ⟨next, hs, hext⟩ := execute_currentCommitment input C accounting tapes s hinv ha stage hcursor hnone commitment hc hstage (hpool commitment.tool)
    exact ⟨next, .single ⟨_, hs⟩, hext⟩
  · have hno : ∀ commitment ∈ s.ledger.commitments, commitment.handle.stage ≠ stage := by
      intro commitment hc hstage
      exact hcommit ⟨commitment, hc, hstage⟩
    have hfresh : ∃ tool : I.Tool, ∀ commitment ∈ s.ledger.commitments, commitment.tool ≠ tool := by
      by_contra hh
      apply hnotexhausted
      refine ⟨hwrong, hnone, hno, ?_⟩
      push Not at hh
      exact hh
    obtain ⟨tool, htool⟩ := hfresh
    let handle : MismatchHandle I := ⟨stage, s.ledger.writeSerial stage⟩
    have hvalid : validHandle s handle := ⟨hwrong, rfl, hreport⟩
    let middle := record accounting s (.allocate handle tool) [.committed handle tool]
      (allocateLedger s handle tool) s.cursor false
    have hstep : Step input C .uncapped accounting tapes s (.allocate handle tool) middle :=
      .allocate s handle tool ha hvalid (hpool tool) htool hno (fun _ => hcursor) (Or.inl rfl)
    let fresh : Commitment I := ⟨handle, tool, s.clock⟩
    have hmem : fresh ∈ middle.ledger.commitments := by simp [fresh, middle, record, allocateLedger]
    have hinv' := step_invariant input C .uncapped accounting tapes hstep hinv
    obtain ⟨next, hs, hext⟩ := execute_currentCommitment input C accounting tapes middle hinv' rfl stage hcursor hnone fresh hmem rfl (hpool tool)
    refine ⟨next, (Relation.ReflTransGen.single ⟨_, hstep⟩).tail ⟨_, hs⟩, ?_⟩
    exact currentCorrectionExtension_trans (s := s) (middle := middle) (next := next) (stage := stage) ⟨rfl, rfl, rfl, rfl, rfl⟩ hext

end PDROC


