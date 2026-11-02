module

public import PaperProofs.Paid.PDMenu_PaidErasedReplayLower_047
public import PaperProofs.Paid.PDMenu_PaidEntryPartition_029
public import PaperProofs.Common.EntryContinuationPartition

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open EntryContinuationPartition

variable {Seed : Type*} [MeasurableSpace Seed]

/-- The original bad repaired entry pays the old actual head execution AND
the sharp k-tool continuation infimum. No conditional normalization,
attainment, termination or continuation performance is supplied. -/
theorem paidBadEntryRecordBridge_at (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (n k : ℕ) (C : Contract (freshInstance (n + 1) (k + 1))) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting (freshInstance (n + 1) (k + 1)))
    (policy : Policy (P.freshInput (n + 1) (k + 1) fee hfee) C .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (next : (freshInstance (n + 1) (k + 1)).Stage) (hnext : next.val = 1)
    (clock : ℕ) (startup : Startup (freshInstance (n + 1) (k + 1)))
    (gate : Set Seed) (hgate : MeasurableSet gate)

    (e : Execution (freshInstance (n + 1) (k + 1))) (he : e ∈ startup.executions)
    (hold : e.handle.stage.val < 1) (penalty : ℝ≥0∞) :
    let input := P.freshInput (n + 1) (k + 1) fee hfee
    (startupObservationCharge input startup + ENNReal.ofReal (fee : ℝ) +
      P.freshPaidPenalty fee hfee n k penalty) *
      input.seededWorldLaw ν (recordEvent input C .uncapped accounting policy.rule next clock startup gate) ≤
      ∫⁻ sample in recordEvent input C .uncapped accounting policy.rule next clock startup gate,
        runPaidPenaltyCharge input C accounting policy.rule penalty sample ∂input.seededWorldLaw ν := by
  intro input
  let E := recordEvent input C .uncapped accounting policy.rule next clock startup gate
  let μ := input.seededWorldLaw ν
  by_cases hEempty : E = ∅
  · change _ * μ E ≤ ∫⁻ sample in E, _ ∂μ
    simp only [hEempty, measure_empty, mul_zero, setLIntegral_empty, le_refl]
  have hnot : e.tool ∉ startup.availableTools := by
    obtain ⟨sample, hs⟩ := Set.nonempty_iff_ne_empty.mpr hEempty
    have hstartup : publicStartup (run input C .uncapped accounting policy.rule sample clock) = startup := (recordEvent_firstEntry input C .uncapped accounting policy.rule next clock startup gate sample hs).2
    have heActual : e ∈ (run input C .uncapped accounting policy.rule sample clock).ledger.executions := by
      change e ∈ (publicStartup (run input C .uncapped accounting policy.rule sample clock)).executions
      rw [hstartup]
      exact he
    have h := executedTool_not_available input C .uncapped accounting policy.rule policy.legal sample clock e heActual
    rwa [hstartup] at h
  let record := entrySeedStartupAt input C .uncapped accounting policy.rule next clock
  let η := μ.map record
  let A : Set (Seed × Option (Startup (freshInstance (n + 1) (k + 1)))) := gate ×ˢ {some startup}
  let D : Set ((Seed × Option (Startup (freshInstance (n + 1) (k + 1)))) × (input.freshSuffix 1).World) := A ×ˢ Set.univ
  let joint := fun sample : Seed × input.World => (record sample, input.restrictFreshWorld 1 sample.2)
  let targetRule := paidGuardedRule (I := (freshInstance (n + 1) (k + 1)).freshSuffix 1) startup.availableTools
    (replayedSuffixCandidate 1 accounting policy.rule startup)
  let F := fun pair : (Seed × Option (Startup (freshInstance (n + 1) (k + 1)))) × (input.freshSuffix 1).World =>
    startupObservationCharge input startup + ENNReal.ofReal (fee : ℝ) +
    runPaidPenaltyCharge (input.freshSuffix 1) (paidRelaxedContract _) (zeroNormalAccounting _)
      targetRule penalty (pair.1.1, pair.2)
  let value := startupObservationCharge input startup + ENNReal.ofReal (fee : ℝ) + P.freshPaidPenalty fee hfee n k penalty
  have hmrecord : Measurable record := measurable_entrySeedStartupAt input C .uncapped accounting policy.rule policy.measurable_rule next clock
  have hmA : MeasurableSet A := hgate.prod (measurableSet_singleton _)
  have hmD : MeasurableSet D := hmA.prod MeasurableSet.univ
  have hmE : MeasurableSet E := measurableSet_recordEvent input C .uncapped accounting policy.rule policy.measurable_rule next clock startup gate hgate
  have hmjoint : Measurable joint := hmrecord.prodMk ((input.measurable_restrictFreshWorld 1).comp measurable_snd)
  have hmTarget : MeasurableRule targetRule := measurable_paidGuardedRule _ _
    (measurable_replayedSuffixCandidate 1 accounting policy.rule policy.measurable_rule startup)
  have hmF : Measurable F := measurable_const.add ((measurable_runPaidPenaltyCharge _ _ _ _ hmTarget penalty).comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hmap : μ.map joint = η.prod (input.freshSuffix 1).worldLaw := by
    cases next with
    | mk value hvalue =>
      change value = 1 at hnext
      subst value
      exact entrySeedStartupAt_jointFreshSuffixLaw input C .uncapped accounting policy ν ⟨1, hvalue⟩ clock
  have hE : E = record ⁻¹' A := by ext sample; rfl
  have hpre : joint ⁻¹' D = E := by
    rw [hE]
    ext sample
    simp only [joint, D, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
  have hmass : η A = μ E := by rw [Measure.map_apply hmrecord hmA, ← hE]
  have hrow (r : Seed × Option (Startup (freshInstance (n + 1) (k + 1)))) :
      value ≤ ∫⁻ fresh, F (r, fresh) ∂(input.freshSuffix 1).worldLaw := by
    change _ ≤ ∫⁻ fresh, (startupObservationCharge input startup + ENNReal.ofReal (fee : ℝ)) +
      runPaidPenaltyCharge _ _ _ targetRule penalty (r.1, fresh) ∂(input.freshSuffix 1).worldLaw
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    exact add_le_add le_rfl (freshPaidPenalty_le_paidReplay_erased_dirac P fee hfee n k accounting
      policy.rule policy.measurable_rule startup e.tool hnot r.1 penalty)
  change value * μ E ≤ _
  calc
    value * μ E = value * η A := by rw [hmass]
    _ = ∫⁻ _r in A, value ∂η := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ r in A, ∫⁻ fresh, F (r, fresh) ∂(input.freshSuffix 1).worldLaw ∂η := lintegral_mono hrow
    _ = ∫⁻ pair in D, F pair ∂η.prod (input.freshSuffix 1).worldLaw := by
      rw [setLIntegral_prod F hmF.aemeasurable, Measure.restrict_univ]
    _ = ∫⁻ sample in E, F (joint sample) ∂μ := by
      rw [← hmap, setLIntegral_map hmD hmF hmjoint, hpre]
    _ ≤ ∫⁻ sample in E, runPaidPenaltyCharge input C accounting policy.rule penalty sample ∂μ := by
      apply setLIntegral_mono' hmE
      intro sample hs
      have hstartup : publicStartup (run input C .uncapped accounting policy.rule sample clock) = startup := (recordEvent_firstEntry input C .uncapped accounting policy.rule next clock startup gate sample hs).2
      have heActual : e ∈ (run input C .uncapped accounting policy.rule sample clock).ledger.executions := by
        change e ∈ (publicStartup (run input C .uncapped accounting policy.rule sample clock)).executions
        rw [hstartup]
        exact he
      have h := paidReplay_withHead_runPaidPenaltyCharge_le input C hC accounting policy.rule policy.legal sample
        1 clock (by simpa only [hnext] using (recordEvent_firstEntry input C .uncapped accounting policy.rule next clock startup gate sample hs).1) fee (fun _ _ => rfl) e heActual hold penalty
      have hprefix : (run input C .uncapped accounting policy.rule sample clock).ledger.observationBill input.fees =
          startupObservationCharge input startup := congrArg (startupObservationCharge input) hstartup
      dsimp only at h
      rw [hstartup, hprefix] at h
      exact h

end PDMenu



