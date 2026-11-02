module

public import PaperProofs.Paid.PA17_D31Witness_Terminal_013
public import PaperProofs.Paid.PA17_D31Witness_Law_004
public import PaperProofs.Common.NativeDeadlines

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal

namespace PaperProofs.Paid.PA17D31WitnessCount014

open Common Common.Native MeasureTheory PA17D31Witness001 PA17D31WitnessPolicy008
open PA17D31WitnessPath007 PA17D31WitnessCompletion009 PA17D31WitnessFullError010
open PA17D31WitnessIncidence011 PA17D31WitnessCoverage012 PA17D31WitnessTerminal013

theorem nativePolicy_prefix_execution_count_le (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) (sample : Unit × (P.input fee hfee).World) (n : ℕ) :
    (run (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) (nativePolicy P fee hfee allocation).rule sample n).ledger.executions.length ≤
        P.blindErrorCount fee hfee sample := by
  obtain ⟨m, _, hp⟩ := run_has_prefix (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
    .native (blindCallAccounting P.sharedInstance) (nativePolicy P fee hfee allocation).rule
    (nativePolicy P fee hfee allocation).legal sample n
  have hinv := prefix_invariant (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
    .native (blindCallAccounting P.sharedInstance) (blindRule P) sample.1 _ _ hp
  have hfalse := prefix_written_false (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
    .native (blindCallAccounting P.sharedInstance) (blindRule P) (blindRule_write_false P) sample.1 _ _ hp
  have hsub := executedStages_subset_errors (P.retainedPaymentExampleContract allocation) _ hinv hfalse
  have hc := Finset.card_le_card hsub
  rw [executedStages_card _ hinv.wellFormed,
    prefix_truth (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
      .native (blindCallAccounting P.sharedInstance) (blindRule P) sample.1 _ _ hp] at hc
  exact hc

theorem nativePolicy_runRepairCount (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) (hK : P.tools = P.certificate.stages - 1)
    (sample : Unit × (P.input fee hfee).World) :
    runRepairCount (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) (nativePolicy P fee hfee allocation).rule sample =
        if P.blindErrorCount fee hfee sample = P.certificate.stages then 0
        else (P.blindErrorCount fee hfee sample : ℝ≥0∞) := by
  by_cases hfull : P.blindErrorCount fee hfee sample = P.certificate.stages
  · rw [ite_eq_left hfull]
    exact nativePolicy_fullTruth_runRepairCount_zero P fee hfee allocation sample
      ((PA17D31WitnessLaw004.blindErrorCount_eq_stages_iff P fee hfee sample).mp hfull)
  · rw [ite_eq_right hfull]
    apply le_antisymm
    · apply iSup_le
      intro n
      exact_mod_cast nativePolicy_prefix_execution_count_le P fee hfee allocation sample n
    · let stopIndex := nativeActionBound (P.retainedPaymentExampleContract allocation) + 1
      have hh := run_halted_nativeActionBound_succ (P.input fee hfee)
        (P.retainedPaymentExampleContract allocation) (blindCallAccounting P.sharedInstance)
        (blindRule P) (nativePolicy P fee hfee allocation).legal sample
      obtain ⟨m, _, hp⟩ := run_has_prefix (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
        .native (blindCallAccounting P.sharedInstance) (blindRule P)
        (nativePolicy P fee hfee allocation).legal sample stopIndex
      have hnotfull : ¬ ∀ stage, (P.input fee hfee).truthAt sample.2 stage = true := by
        intro hf
        exact hfull ((PA17D31WitnessLaw004.blindErrorCount_eq_stages_iff P fee hfee sample).mpr hf)
      have hc := prefix_halted_nonfull_execution_count P fee hfee allocation hK sample.1 _ _ hnotfull hp hh
      have hle := le_iSup (fun n =>
        ((run (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
          (blindCallAccounting P.sharedInstance) (blindRule P) sample n).ledger.executions.length : ℝ≥0∞)) stopIndex
      rw [hc] at hle
      exact hle

theorem prefix_halted_flags (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) (seed : Unit) (truth : P.sharedInstance.Stage → Bool)
    (tapes : ReviewTapes (P.input fee hfee)) {n : ℕ} {s : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) (blindRule P) seed truth tapes n s)
    (hh : s.halted = true) : s.ledger.finished = true ∧ s.ledger.abandoned = false := by
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
      have hcursor := hc.symm.trans (blindCandidate_stop_cursor P seed s.history hhist (hm.symm.trans ha))
      have hall : allWritten s.ledger := by
        intro stage
        apply prefix_written_before_cursor (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
          .native (blindCallAccounting P.sharedInstance) (blindRule P) seed truth tapes hp stage
        rw [hcursor]
        exact stage_lt_stages P stage
      refine ⟨?_, rfl⟩
      simp only [stopState, hall, decide_true]
    | abandon =>
      have hb := (prefix_cursorInvariant (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
        .native (blindCallAccounting P.sharedInstance) (blindRule P) seed truth tapes hp).bound
      rw [P.stageCount_eq] at hb
      exact (PA17D31WitnessPath007.blindCandidate_ne_abandon P seed s.history (hc.symm ▸ hb)
        (hm.symm.trans ha)).elim
    | review | write | allocate | execute | advance => cases hh

end PaperProofs.Paid.PA17D31WitnessCount014
