module

public import PaperProofs.Paid.PA17_D31Witness_Coverage_012

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Paid.PA17D31WitnessTerminal013

open Common Common.Native MeasureTheory PA17D31Witness001 PA17D31WitnessPolicy008
open PA17D31WitnessPath007 PA17D31WitnessCompletion009 PA17D31WitnessFullError010
open PA17D31WitnessIncidence011 PA17D31WitnessCoverage012

theorem candidate_stop_pending_none (P : Parameters) (seed : Unit)
    (history : List (VisibleEvent P.sharedInstance)) (hactive : historyHalted history = false)
    (hcursor : historyCursor history = P.certificate.stages) (hnotfull : ¬ allReportsWrong P history)
    (ha : blindCandidate P seed history = .stop) :
    (historyCommitments history).find? (fun pair =>
      !(historyExecutions history).any (fun e => e.1.stage == pair.1.stage)) = none := by
  unfold blindCandidate at ha
  simp only [hactive, Bool.false_eq_true, ↓reduceIte] at ha
  rw [dite_eq_right (by omega), ite_eq_left hcursor, ite_eq_right hnotfull] at ha
  cases hf : (historyCommitments history).find? (fun pair =>
      !(historyExecutions history).any (fun e => e.1.stage == pair.1.stage)) with
  | none => rfl
  | some pair => rw [hf] at ha; cases ha

theorem prefix_halted_nonfull_executes (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) (seed : Unit) (truth : P.sharedInstance.Stage → Bool)
    (tapes : ReviewTapes (P.input fee hfee)) (hnotfull : ¬ ∀ stage, truth stage = true)
    {n : ℕ} {s : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) (blindRule P) seed truth tapes n s)
    (hh : s.halted = true) : committedStages s.ledger ⊆ executedStages s.ledger := by
  cases hp with
  | initial => cases hh
  | @next n s next hp hs =>
    have hm := nativeRule_nonbinding P fee hfee allocation seed truth tapes hp
    have hactive := step_source_active (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
      .native (blindCallAccounting P.sharedInstance) tapes hs
    have hhist := (prefix_historyHalted (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
      .native (blindCallAccounting P.sharedInstance) (blindRule P) seed truth tapes hp).trans hactive
    have hc := prefix_historyCursor (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
      .native (blindCallAccounting P.sharedInstance) (blindRule P) seed truth tapes hp
    generalize ha : blindRule P seed s.history = action at hs
    cases hs with
    | stop =>
      have hcursor := blindCandidate_stop_cursor P seed s.history hhist (hm.symm.trans ha)
      have hledgercursor := hc.symm.trans hcursor
      have hnreport : ¬ allReportsWrong P s.history := by
        intro hr
        exact hnotfull ((terminal_allReportsWrong_iff P fee hfee
          (P.retainedPaymentExampleContract allocation) rfl .native (blindCallAccounting P.sharedInstance)
          (blindRule P) seed truth tapes hp hledgercursor).mp hr)
      have hn := candidate_stop_pending_none P seed s.history hhist hcursor hnreport (hm.symm.trans ha)
      intro stage hstage
      change stage ∈ committedStages s.ledger at hstage
      change stage ∈ executedStages s.ledger
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hstage)
      have hmem : (a.handle, a.tool) ∈ historyCommitments s.history := by
        rw [prefix_historyCommitments (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
          .native (blindCallAccounting P.sharedInstance) (blindRule P) seed truth tapes hp]
        exact List.mem_map.mpr ⟨a, ha, rfl⟩
      have hkeep := List.find?_eq_none.mp hn (a.handle, a.tool) hmem
      have hany : (historyExecutions s.history).any (fun e => e.1.stage == a.handle.stage) = true := by
        cases hb : (historyExecutions s.history).any (fun e => e.1.stage == a.handle.stage)
        · simp only [hb, Bool.not_false, not_true_eq_false] at hkeep
        · rfl
      obtain ⟨pair, he, heq⟩ := List.any_eq_true.mp hany
      rw [prefix_historyExecutions (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
        .native (blindCallAccounting P.sharedInstance) (blindRule P) seed truth tapes hp] at he
      obtain ⟨execution, hexecution, rfl⟩ := List.mem_map.mp he
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨execution, hexecution, by simpa only [beq_iff_eq] using heq⟩)
    | abandon =>
      have hb := (prefix_cursorInvariant (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
        .native (blindCallAccounting P.sharedInstance) (blindRule P) seed truth tapes hp).bound
      rw [P.stageCount_eq] at hb
      exact (PA17D31WitnessPath007.blindCandidate_ne_abandon P seed s.history (hc.symm ▸ hb)
        (hm.symm.trans ha)).elim
    | review | write | allocate | execute | advance => cases hh

theorem prefix_halted_nonfull_execution_count (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) (hK : P.tools = P.certificate.stages - 1)
    (seed : Unit) (truth : P.sharedInstance.Stage → Bool)
    (tapes : ReviewTapes (P.input fee hfee)) (hnotfull : ¬ ∀ stage, truth stage = true)
    {n : ℕ} {s : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) (blindRule P) seed truth tapes n s)
    (hh : s.halted = true) : s.ledger.executions.length = (errorStages truth).card := by
  have hinv := prefix_invariant (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
    .native (blindCallAccounting P.sharedInstance) (blindRule P) seed truth tapes hp
  have hfalse := prefix_written_false (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
    .native (blindCallAccounting P.sharedInstance) (blindRule P) (blindRule_write_false P) seed truth tapes hp
  have htruth := prefix_truth (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
    .native (blindCallAccounting P.sharedInstance) (blindRule P) seed truth tapes hp
  have hc := prefix_halted_cursor P fee hfee allocation (blindRule P)
    (fun seed truth tapes _ _ hp _ => nativeRule_nonbinding P fee hfee allocation seed truth tapes hp)
    seed truth tapes hp hh
  have herrlt : (errorStages truth).card < P.certificate.stages := by
    have hproper : errorStages truth ≠ Finset.univ := by
      intro heq
      apply hnotfull
      intro stage
      have hs : stage ∈ errorStages truth := heq.symm ▸ Finset.mem_univ stage
      exact (Finset.mem_filter.mp hs).2
    have h := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hproper⟩)
    have hcard : (Finset.univ : Finset P.sharedInstance.Stage).card = P.certificate.stages := by
      calc
        (Finset.univ : Finset P.sharedInstance.Stage).card = Fintype.card P.sharedInstance.Stage := Finset.card_univ
        _ = P.sharedInstance.stageCount := Fintype.card_fin _
        _ = P.certificate.stages := P.stageCount_eq
    rwa [hcard] at h
  have hcount : (errorStages s.ledger.truth).card ≤ P.sharedInstance.toolCount := by
    rw [htruth]
    change (errorStages truth).card ≤ P.tools
    omega
  have hcomm := committedStages_eq_errors_of_coverage (P.retainedPaymentExampleContract allocation)
    s hinv hfalse hcount (by
      intro stage hs
      have ht : s.ledger.truth stage = true := (Finset.mem_filter.mp hs).2
      apply prefix_past_error_coverage P fee hfee allocation seed truth tapes hp stage
      · rw [hc]; exact stage_lt_stages P stage
      · exact ht)
  have hex := prefix_halted_nonfull_executes P fee hfee allocation seed truth tapes hnotfull hp hh
  have hexeq : executedStages s.ledger = errorStages s.ledger.truth :=
    Finset.Subset.antisymm (executedStages_subset_errors (P.retainedPaymentExampleContract allocation) s hinv hfalse)
      (hcomm ▸ hex)
  rw [← executedStages_card s.ledger hinv.wellFormed, hexeq, htruth]

end PaperProofs.Paid.PA17D31WitnessTerminal013
