module

public import PaperProofs.Paid.PA17_D31Witness_Count_014

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Paid.PA17D31WitnessSuccess015

open Common Common.Native MeasureTheory PA17D31Witness001 PA17D31WitnessPolicy008
open PA17D31WitnessPath007 PA17D31WitnessCompletion009 PA17D31WitnessFullError010
open PA17D31WitnessIncidence011 PA17D31WitnessTerminal013 PA17D31WitnessCount014

theorem nativePolicy_runSuccess_iff (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) (hK : P.tools = P.certificate.stages - 1)
    (sample : Unit × (P.input fee hfee).World) :
    runSuccess (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) (nativePolicy P fee hfee allocation).rule sample ↔
        P.blindErrorCount fee hfee sample ≠ P.certificate.stages := by
  constructor
  · rintro ⟨n, _, hsuccess⟩ hfull
    have htruth : ∀ stage, (P.input fee hfee).truthAt sample.2 stage = true :=
      (PA17D31WitnessLaw004.blindErrorCount_eq_stages_iff P fee hfee sample).mp hfull
    let stage : P.sharedInstance.Stage := ⟨0, by
      change 0 < P.sharedInstance.stageCount
      rw [P.stageCount_eq]
      exact P.certificate.stages_pos⟩
    obtain ⟨m, _, hp⟩ := run_has_prefix (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
      .native (blindCallAccounting P.sharedInstance) (nativePolicy P fee hfee allocation).rule
      (nativePolicy P fee hfee allocation).legal sample n
    have ht := prefix_truth (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
      .native (blindCallAccounting P.sharedInstance) (nativePolicy P fee hfee allocation).rule sample.1 _ _ hp
    rcases hsuccess.2.2.2 stage with hw | ⟨e, he, _⟩
    · have hb := nativePolicy_written_false P fee hfee allocation sample n stage _ hw
      rw [ht, htruth stage] at hb
      cases hb
    · rw [nativePolicy_run_executions_nil P fee hfee allocation sample htruth n] at he
      cases he
  · intro hnonfull
    let stopIndex := nativeActionBound (P.retainedPaymentExampleContract allocation) + 1
    have hh := run_halted_nativeActionBound_succ (P.input fee hfee)
      (P.retainedPaymentExampleContract allocation) (blindCallAccounting P.sharedInstance)
      (blindRule P) (nativePolicy P fee hfee allocation).legal sample
    obtain ⟨m, _, hp⟩ := run_has_prefix (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
      .native (blindCallAccounting P.sharedInstance) (blindRule P)
      (nativePolicy P fee hfee allocation).legal sample stopIndex
    let s := run (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) (blindRule P) sample stopIndex
    have hc := prefix_halted_cursor P fee hfee allocation (blindRule P)
      (fun seed truth tapes _ _ hp _ => nativeRule_nonbinding P fee hfee allocation seed truth tapes hp)
      sample.1 _ _ hp hh
    have hnotfull : ¬ ∀ stage, (P.input fee hfee).truthAt sample.2 stage = true := by
      intro hf
      exact hnonfull ((PA17D31WitnessLaw004.blindErrorCount_eq_stages_iff P fee hfee sample).mpr hf)
    have hflags := prefix_halted_flags P fee hfee allocation sample.1 _ _ hp hh
    have hinv := prefix_invariant (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
      .native (blindCallAccounting P.sharedInstance) (blindRule P) sample.1 _ _ hp
    have hfalse := prefix_written_false (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
      .native (blindCallAccounting P.sharedInstance) (blindRule P) (blindRule_write_false P) sample.1 _ _ hp
    have ht := prefix_truth (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
      .native (blindCallAccounting P.sharedInstance) (blindRule P) sample.1 _ _ hp
    have hsub := executedStages_subset_errors (P.retainedPaymentExampleContract allocation) s hinv hfalse
    have hcount := prefix_halted_nonfull_execution_count P fee hfee allocation hK sample.1 _ _ hnotfull hp hh
    have hexeq : executedStages s.ledger = errorStages s.ledger.truth :=
      Finset.eq_of_subset_of_card_le hsub (by
        rw [executedStages_card s.ledger hinv.wellFormed, ht]
        exact hcount.ge)
    refine ⟨stopIndex, hh, ?_⟩
    apply (prefix_success_iff_physical (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
      .native (blindCallAccounting P.sharedInstance) (blindRule P) sample.1 _ _ hp).mpr
    refine ⟨hflags.1, hflags.2, ?_⟩
    intro stage
    apply (finalOutput_correct_iff s.ledger stage).mpr
    cases hb : s.ledger.truth stage with
    | false =>
      left
      have hwritten : s.ledger.written stage ≠ none := by
        apply prefix_written_before_cursor (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
          .native (blindCallAccounting P.sharedInstance) (blindRule P) sample.1 _ _ hp stage
        rw [hc]
        exact stage_lt_stages P stage
      cases hw : s.ledger.written stage with
      | none => exact (hwritten hw).elim
      | some bit => simp only [hfalse stage bit hw]
    | true =>
      right
      have hs : stage ∈ executedStages s.ledger := by
        rw [hexeq]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ stage, hb⟩
      exact List.mem_map.mp (List.mem_toFinset.mp hs)

theorem nativePolicy_risk_of_assignment_mass (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) (hK : P.tools = P.certificate.stages - 1)
    (hmass : (P.input fee hfee).seededWorldLaw (Measure.dirac ())
      {sample | P.blindErrorCount fee hfee sample = P.certificate.stages} = P.targetRisk) :
    risk (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) (nativePolicy P fee hfee allocation).rule (Measure.dirac ()) = P.targetRisk := by
  unfold risk
  simp_rw [nativePolicy_runSuccess_iff P fee hfee allocation hK, not_not]
  exact hmass

end PaperProofs.Paid.PA17D31WitnessSuccess015
