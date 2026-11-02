module

public import PaperProofs.Paid.PDROC_CalibratedRuntime_014
public import PaperProofs.Paid.PDROC_CalibratedSignature_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters
open PDMenu

namespace PDROC.CalibratedRuntime

/-- The actual original fixed-table calibrated run has exactly the shared
complete outcome signature and observation charge, on every original world.
Unvisited stages have neither write flag, and tools are the proved physical
first-unused choices. There is no performance or return premise. -/
theorem menu_path_agreement (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (sample : P.CalibratedMenuSeed × (P.input fee hfee).World) :
    let summary := pathSummary P (calibratedFamily P) table P.certificate.stages P.tools
      (calibratedSuffixSeed P 0 P.certificate.stages (Nat.zero_add P.certificate.stages) sample.1)
      (menuSuffixWorld P P.certificate.stages P.tools 0 P.certificate.stages
        (Nat.zero_add P.certificate.stages) fee hfee sample.2)
    P.executionSignature fee hfee C .uncapped accounting (menuRule P table) sample =
      outcomeSignature P summary.outcome ∧
    runObservationBill (P.input fee hfee) C.val .uncapped accounting (menuRule P table) sample = summary.observation := by
  classical
  let input := P.input fee hfee
  let rule := menuRule P table
  let summary := pathSummary P (calibratedFamily P) table P.certificate.stages P.tools
    (calibratedSuffixSeed P 0 P.certificate.stages (Nat.zero_add P.certificate.stages) sample.1)
    (menuSuffixWorld P P.certificate.stages P.tools 0 P.certificate.stages
      (Nat.zero_add P.certificate.stages) fee hfee sample.2)
  have legal := menuRule_legal P table fee hfee C.val C.property.1.1 accounting
  have records := root_records P table fee hfee C.val C.property accounting sample
  dsimp only [EntryRecords] at records
  have hcount : P.tools - (run input C.val .uncapped accounting rule sample 0).ledger.executions.length = P.tools := rfl
  rw [hcount] at records
  obtain ⟨ended, _, halted, hobs, htrace, hsuccess⟩ := records
  let final := run input C.val .uncapped accounting rule sample ended
  have hobs0 : (run input C.val .uncapped accounting rule sample 0).ledger.observationBill input.fees = 0 := by
    simp only [run, initial, Ledger.observationBill, ENat.toENNReal_zero, mul_zero, Finset.sum_const_zero]
  rw [hobs0, zero_add] at hobs
  have hused0 : historyUsed (run input C.val .uncapped accounting rule sample 0).history = ∅ := rfl
  rw [hused0] at htrace
  have hpairs0 : executionPairs P (run input C.val .uncapped accounting rule sample 0).ledger = [] := rfl
  have hpairs : executionPairs P final.ledger = repairPairs P.tools 0 ∅ summary.trace := by
    have h := htrace.2
    rw [hpairs0, List.nil_append] at h
    exact h
  have hwritten (stage : P.sharedInstance.Stage) :
      final.ledger.written stage = traceBit summary.trace stage.val (final.ledger.truth stage) := by
    simpa only [Nat.sub_zero] using htrace.1 stage (Nat.zero_le stage.val)
  have hsignature : P.executionSignature fee hfee C .uncapped accounting rule sample =
      outcomeSignature P summary.outcome := by
    rw [PDROC.CalibratedSignature.executionSignature_eq_of_halted P fee hfee C .uncapped accounting rule legal sample ended halted]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · funext stage
      change decide (final.ledger.written stage = some (final.ledger.truth stage)) =
        match summary.trace[stage.val]? with | none => false | some event => !event.1
      rw [hwritten stage]
      exact traceBit_correct_flag summary.trace stage.val _
    · funext stage
      change decide (final.ledger.written stage = some (!final.ledger.truth stage)) =
        match summary.trace[stage.val]? with | none => false | some event => event.1
      rw [hwritten stage]
      exact traceBit_wrong_flag summary.trace stage.val _
    · funext stage tool
      change decide (∃ execution ∈ final.ledger.executions,
        execution.handle.stage = stage ∧ execution.tool = tool) =
          decide ((stage.val, tool) ∈ repairPairs P.tools 0 ∅ summary.trace)
      apply decide_eq_decide.mpr
      rw [← executionPairs_mem P final.ledger stage tool, hpairs]
      with_unfolding_all rfl
    · change decide (¬final.ledger.success C.val) = summary.failure
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq]
      constructor
      · intro hn
        cases hf : summary.failure
        · exact (hn ((menu_runSuccess_iff_of_halted input C.val .uncapped accounting rule sample ended halted).mp
            (hsuccess.mpr hf))).elim
        · rfl
      · intro hf hs
        have hfalse := hsuccess.mp ((menu_runSuccess_iff_of_halted input C.val .uncapped accounting rule sample ended halted).mpr hs)
        rw [hf] at hfalse
        cases hfalse
  refine ⟨hsignature, ?_⟩
  exact (menu_runObservationBill_of_halted input C.val .uncapped accounting rule legal sample ended halted).trans hobs

end PDROC.CalibratedRuntime
