module

public import PaperProofs.Paid.PDMenu_PaidBadEntryPartition_048
public import PaperProofs.Paid.PDMenu_PaidHeadWeights_049
public import PaperProofs.Paid.PDMenu_PaidGoodEntryPartition_050
public import PaperProofs.Paid.PDMenu_PaidMissedExecution_051

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open EntryContinuationPartition

variable {Seed : Type*} [MeasurableSpace Seed]

private theorem paid_option_wrong (value : Option Bool) (truth : Bool)
    (hnone : value ≠ none) (hcorrect : value ≠ some truth) : value = some (!truth) := by
  cases value with
  | none => exact (hnone rfl).elim
  | some bit => cases truth <;> cases bit <;> simp_all

/-- All actual first-entry records, with the original full paid successors.
The bad case distinguishes a physical execution from an unpaid commitment. -/
theorem paidFresh_entry_record_lower (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    (C : Contract (freshInstance (n + 1) k)) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting (freshInstance (n + 1) k))
    (policy : Policy (P.freshInput (n + 1) k fee hfee) C .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (head next : (freshInstance (n + 1) k).Stage) (hhead : head.val = 0) (hnext : next.val = 1)
    (clock : ℕ) (startup : Startup (freshInstance (n + 1) k)) (gate : Set Seed) (hgate : MeasurableSet gate)
    (penalty : ℝ≥0∞) :
    let input := P.freshInput (n + 1) k fee hfee
    (startupObservationCharge input startup + paidEntryContinuationWeight head startup
      (P.paidGoodSuccessor fee hfee (n + 1) k penalty) (P.paidBadSuccessor fee hfee (n + 1) k penalty)) *
      input.seededWorldLaw ν (recordEvent input C .uncapped accounting policy.rule next clock startup gate) ≤
      ∫⁻ sample in recordEvent input C .uncapped accounting policy.rule next clock startup gate,
        runPaidPenaltyCharge input C accounting policy.rule penalty sample ∂input.seededWorldLaw ν := by
  classical
  intro input
  let E := recordEvent input C .uncapped accounting policy.rule next clock startup gate
  let μ := input.seededWorldLaw ν
  by_cases hEempty : E = ∅
  · change _ * μ E ≤ ∫⁻ sample in E, _ ∂μ
    simp only [hEempty, measure_empty, mul_zero, setLIntegral_empty, le_refl]
  by_cases hcorrect : HeadCorrectStartup head startup
  · simp only [paidEntryContinuationWeight, hcorrect, ↓reduceIte]
    have h := paidStageEntryRecordBridge_at input C hC accounting policy ν next clock startup gate hgate
      fee (fun _ _ => rfl) penalty
    have hv : paidPenaltyValue (input.freshSuffix next.val) (paidRelaxedContract _) (zeroNormalAccounting _) penalty =
        P.paidGoodSuccessor fee hfee (n + 1) k penalty := by
      have hs := freshPaidPenalty_suffix_eq P (n + 1) k next.val fee hfee penalty
      simpa only [hnext, Parameters.paidGoodSuccessor] using hs
    rwa [hv] at h
  · simp only [paidEntryContinuationWeight, hcorrect, ↓reduceIte]
    by_cases hno : startup.executions = []
    · rw [← setLIntegral_const]
      apply setLIntegral_mono' (measurableSet_recordEvent input C .uncapped accounting policy.rule
        policy.measurable_rule next clock startup gate hgate)
      intro sample hs
      have hf := recordEvent_firstEntry input C .uncapped accounting policy.rule next clock startup gate sample hs
      have hentry : FirstEntryAt input C .uncapped accounting policy.rule 1 clock sample :=
        ⟨hf.1.1.trans hnext, fun before hbefore hcursor => hf.1.2 before hbefore (hcursor.trans hnext.symm)⟩
      have hwn := firstEntry_one_head_written input C .uncapped accounting policy.rule policy.legal head hhead sample clock hentry
      obtain ⟨prefixClock, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.rule policy.legal sample clock
      have hwrong : (run input C .uncapped accounting policy.rule sample clock).ledger.written head =
          some (!(run input C .uncapped accounting policy.rule sample clock).ledger.truth head) := by
        apply paid_option_wrong _ _ hwn
        intro hc
        apply hcorrect
        rw [← hf.2]
        exact (headCorrectStartup_iff input C hC.1.1 .uncapped accounting policy.rule sample.1 _ _ hp head hwn).mpr hc
      have hnone : ∀ e ∈ (run input C .uncapped accounting policy.rule sample clock).ledger.executions,
          e.handle.stage ≠ head := by
        intro e he
        change e ∈ (publicStartup (run input C .uncapped accounting policy.rule sample clock)).executions at he
        rw [hf.2, hno] at he
        cases he
      have hfailure := paidWrong_unexecuted_behind_cursor_failure input C hC.2 .uncapped accounting policy.rule
        policy.legal sample clock head (by rw [hentry.1, hhead]; exact Nat.zero_lt_one) hwrong hnone
      have hprefix : (run input C .uncapped accounting policy.rule sample clock).ledger.observationBill input.fees =
          startupObservationCharge input startup := congrArg (startupObservationCharge input) hf.2
      have hobs : startupObservationCharge input startup ≤ runActualBill input C .uncapped accounting policy.rule sample := by
        rw [← hprefix]
        exact ((run input C .uncapped accounting policy.rule sample clock).ledger.observationBill_le_actualBill input.fees).trans
          (prefixBill_le_runActualBill input C .uncapped accounting policy.rule sample clock)
      have hbad : P.paidBadSuccessor fee hfee (n + 1) k penalty ≤ penalty := by
        cases k with
        | zero => exact le_rfl
        | succ k => exact min_le_left _ _
      unfold runPaidPenaltyCharge
      simp only [hfailure, ↓reduceIte]
      exact add_le_add hobs hbad
    · obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil startup.executions hno
      obtain ⟨sample, hs⟩ := Set.nonempty_iff_ne_empty.mpr hEempty
      have hf := recordEvent_firstEntry input C .uncapped accounting policy.rule next clock startup gate sample hs
      have hentry : FirstEntryAt input C .uncapped accounting policy.rule 1 clock sample :=
        ⟨hf.1.1.trans hnext, fun before hbefore hcursor => hf.1.2 before hbefore (hcursor.trans hnext.symm)⟩
      have heActual : e ∈ (run input C .uncapped accounting policy.rule sample clock).ledger.executions := by
        change e ∈ (publicStartup (run input C .uncapped accounting policy.rule sample clock)).executions
        rw [hf.2]
        exact he
      obtain ⟨a, ha, hhandle, _htool, _htime⟩ :=
        (run_ledgerWellFormed input C .uncapped accounting policy.rule policy.legal sample clock).backed e heActual
      have hstage : e.handle.stage = head := (congrArg MismatchHandle.stage hhandle).symm.trans
        (firstEntry_one_commitment_stage input C .uncapped accounting policy.rule policy.legal head hhead
          sample clock hentry a ha)
      have hold : e.handle.stage.val < 1 := by rw [hstage, hhead]; exact Nat.zero_lt_one
      cases k with
      | zero => exact Fin.elim0 e.tool
      | succ k =>
        have h := paidBadEntryRecordBridge_at P fee hfee n k C hC accounting policy ν next hnext
          clock startup gate hgate e he hold penalty
        have hv : startupObservationCharge input startup + P.paidBadSuccessor fee hfee (n + 1) (k + 1) penalty ≤
            startupObservationCharge input startup + ENNReal.ofReal (fee : ℝ) + P.freshPaidPenalty fee hfee n k penalty := by
          calc
            _ ≤ startupObservationCharge input startup +
                (ENNReal.ofReal (fee : ℝ) + P.freshPaidPenalty fee hfee n k penalty) :=
              add_le_add le_rfl (min_le_right _ _)
            _ = _ := by ac_rfl
        exact (mul_le_mul_left hv _).trans h

end PDMenu



