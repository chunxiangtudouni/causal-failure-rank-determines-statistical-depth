module

public import PaperProofs.Paid.PDROC_CalibratedIdeal_007
public import PaperProofs.Paid.PDROC_CalibratedSignature_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters
open PDMenu PDROC.CalibratedRuntime

namespace PDROC.CalibratedIdeal

theorem idealPathAgreement_of_finite (P : Parameters) (table : MenuTable) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (sample : MenuSeed P.certificate.stages P.tools × (P.input fee hfee).World)
    (finite : MenuEndpointFiniteSample P P.certificate.stages P.tools fee hfee sample) :
    MenuNativePathAgreement P P.certificate.stages P.tools table fee hfee C.val accounting sample :=
  menuNativePathAgreement_of_abort_records P P.certificate.stages P.tools table fee hfee C.val C.property accounting sample
    finite (PDROC.menuNativeAbortClaims P P.certificate.stages P.tools table fee hfee C.val C.property accounting sample)

/-- Every visited correct/wrong flag and every physical stage/tool pair is
the original run's exact eventual signature. The only sample restriction is
the frozen probability-one endpoint-finiteness set, not a caller performance
or return condition. -/
theorem ideal_executionSignature_of_finite (P : Parameters) (table : MenuTable) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (sample : MenuSeed P.certificate.stages P.tools × (P.input fee hfee).World)
    (finite : MenuEndpointFiniteSample P P.certificate.stages P.tools fee hfee sample) :
    P.executionSignature fee hfee C .uncapped accounting
        (P.compiledMenuRule P.certificate.stages P.tools table) sample =
      outcomeSignature P ((pathSummary P (idealFamily P) table P.certificate.stages P.tools
        (menuSeedFinEquiv P.certificate.stages P.tools sample.1)
        (menuWorldFinEquiv P P.certificate.stages P.tools fee hfee sample.2)).outcome) := by
  classical
  let input := P.input fee hfee
  let rule := P.compiledMenuRule P.certificate.stages P.tools table
  let record := pathSummary P (idealFamily P) table P.certificate.stages P.tools
    (menuSeedFinEquiv P.certificate.stages P.tools sample.1)
    (menuWorldFinEquiv P P.certificate.stages P.tools fee hfee sample.2)
  have legal := P.compiledMenuRule_uncapped_legal P.certificate.stages P.tools table fee hfee C.val C.property.1.1 accounting
  obtain ⟨ended, halted, matched⟩ := rootTrace_of_finite P table fee hfee C accounting sample finite
  have agreement := idealPathAgreement_of_finite P table fee hfee C accounting sample finite
  have success : runSuccess input C.val .uncapped accounting rule sample ↔ record.failure = false := by
    dsimp only [record]
    rw [idealSummary_failure]
    with_unfolding_all exact agreement.2.2
  have failure : decide (¬ runSuccess input C.val .uncapped accounting rule sample) = record.failure := by
    by_cases hs : runSuccess input C.val .uncapped accounting rule sample
    · rw [success.mp hs]
      simp only [hs, not_true_eq_false, decide_false]
    · have ht : record.failure = true := by
        cases hb : record.failure with
        | false => exact (hs (success.mpr hb)).elim
        | true => rfl
      rw [ht]
      simp only [hs, not_false_eq_true, decide_true]
  rw [CalibratedSignature.executionSignature_eq_of_halted P fee hfee C .uncapped accounting rule legal sample ended halted]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext stage
    change decide ((run input C.val .uncapped accounting rule sample ended).ledger.written stage =
      some ((run input C.val .uncapped accounting rule sample ended).ledger.truth stage)) = _
    rw [matched.1 stage (Nat.zero_le _), Nat.sub_zero]
    exact traceBit_correct_flag record.trace stage.val _
  · funext stage
    change decide ((run input C.val .uncapped accounting rule sample ended).ledger.written stage =
      some (!(run input C.val .uncapped accounting rule sample ended).ledger.truth stage)) = _
    rw [matched.1 stage (Nat.zero_le _), Nat.sub_zero]
    exact traceBit_wrong_flag record.trace stage.val _
  · funext stage tool
    change decide (∃ execution ∈ (run input C.val .uncapped accounting rule sample ended).ledger.executions,
      execution.handle.stage = stage ∧ execution.tool = tool) =
      decide ((stage.val, tool) ∈ repairPairs P.tools 0 ∅ record.trace)
    apply decide_eq_decide.mpr
    rw [← executionPairs_mem P _ stage tool, matched.2]
    rfl
  · change decide (¬ (run input C.val .uncapped accounting rule sample ended).ledger.success C.val) = record.failure
    rw [← menu_runSuccess_iff_of_halted input C.val .uncapped accounting rule sample ended halted]
    exact failure

theorem ideal_observation_of_finite (P : Parameters) (table : MenuTable) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (sample : MenuSeed P.certificate.stages P.tools × (P.input fee hfee).World)
    (finite : MenuEndpointFiniteSample P P.certificate.stages P.tools fee hfee sample) :
    runObservationBill (P.input fee hfee) C.val .uncapped accounting
        (P.compiledMenuRule P.certificate.stages P.tools table) sample =
      (pathSummary P (idealFamily P) table P.certificate.stages P.tools
        (menuSeedFinEquiv P.certificate.stages P.tools sample.1)
        (menuWorldFinEquiv P P.certificate.stages P.tools fee hfee sample.2)).observation := by
  rw [idealSummary_observation]
  exact (idealPathAgreement_of_finite P table fee hfee C accounting sample finite).1

/-- Both outputs use the actual original menu seed/world joint law. The
sample finiteness condition is discharged internally, including N=0/K=0. -/
theorem ideal_run_summary_ae (P : Parameters) (table : MenuTable) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw (menuSeedLaw P.certificate.stages P.tools),
      P.executionSignature fee hfee C .uncapped accounting
          (P.compiledMenuRule P.certificate.stages P.tools table) sample =
        outcomeSignature P ((pathSummary P (idealFamily P) table P.certificate.stages P.tools
          (menuSeedFinEquiv P.certificate.stages P.tools sample.1)
          (menuWorldFinEquiv P P.certificate.stages P.tools fee hfee sample.2)).outcome) ∧
      runObservationBill (P.input fee hfee) C.val .uncapped accounting
          (P.compiledMenuRule P.certificate.stages P.tools table) sample =
        (pathSummary P (idealFamily P) table P.certificate.stages P.tools
          (menuSeedFinEquiv P.certificate.stages P.tools sample.1)
          (menuWorldFinEquiv P P.certificate.stages P.tools fee hfee sample.2)).observation := by
  filter_upwards [menuEndpointFiniteSample_ae P P.certificate.stages P.tools fee hfee] with sample finite
  exact ⟨ideal_executionSignature_of_finite P table fee hfee C accounting sample finite,
    ideal_observation_of_finite P table fee hfee C accounting sample finite⟩

end PDROC.CalibratedIdeal
