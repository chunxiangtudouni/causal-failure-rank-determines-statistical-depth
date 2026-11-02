module

public import PaperProofs.Paid.PDMenu_CurrentReplayPaidCharge_026
public import PaperProofs.Paid.PDMenu_CurrentReplayDirac_027
public import PaperProofs.Common.HistorySuffixBridge

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def startupObservationCharge (input : StatisticalInput I) (startup : Startup I) : ℝ≥0∞ :=
  ∑ stage : I.Stage, ENNReal.ofReal (input.fees.observation stage : ℝ) * (startup.reviews stage : ℝ≥0∞)

/-- Unnormalized real entry-history comparison for the original full paid
value. It retains the original prefix observation charge and ALL actual
future fees and failure charge. Zero-mass histories and infinite costs are
included; no conditional law or continuation performance is supplied. -/
theorem paidStageEntryHistoryBridge_at (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentPayment) (accounting : NormalAccounting I)
    (policy : Policy input C .uncapped accounting Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (next : I.Stage) (n : ℕ) (startup : Startup I) (gate : Set Seed) (hgate : MeasurableSet gate)
    (hentry : ∀ sample ∈ historyGate input C .uncapped accounting policy.rule n startup gate,
      FirstEntryAt input C .uncapped accounting policy.rule next.val n sample)
    (fee : ℚ) (hfee : ∀ stage tool, input.fees.correction stage tool = fee) (penalty : ℝ≥0∞) :
    (startupObservationCharge input startup +
      paidPenaltyValue (input.freshSuffix next.val) (paidRelaxedContract (I.freshSuffix next.val))
        (zeroNormalAccounting (I.freshSuffix next.val)) penalty) *
      input.seededWorldLaw ν (historyGate input C .uncapped accounting policy.rule n startup gate) ≤
      ∫⁻ sample in historyGate input C .uncapped accounting policy.rule n startup gate,
        runPaidPenaltyCharge input C accounting policy.rule penalty sample ∂input.seededWorldLaw ν := by
  let E := historyGate input C .uncapped accounting policy.rule n startup gate
  let μ := input.seededWorldLaw ν
  let record := entrySeedStartupAt input C .uncapped accounting policy.rule next n
  let η := μ.map record
  let A : Set (Seed × Option (Startup I)) := gate ×ˢ {some startup}
  let D : Set ((Seed × Option (Startup I)) × (input.freshSuffix next.val).World) := A ×ˢ Set.univ
  let joint := fun sample : Seed × input.World => (record sample, input.restrictFreshWorld next.val sample.2)
  let targetRule := paidGuardedRule (I := I.freshSuffix next.val) startup.availableTools
    (replayedSuffixCandidate next.val accounting policy.rule startup)
  let F := fun pair : (Seed × Option (Startup I)) × (input.freshSuffix next.val).World =>
    startupObservationCharge input startup +
    runPaidPenaltyCharge (input.freshSuffix next.val) (paidRelaxedContract (I.freshSuffix next.val))
      (zeroNormalAccounting (I.freshSuffix next.val)) targetRule penalty (pair.1.1, pair.2)
  let value := startupObservationCharge input startup +
    paidPenaltyValue (input.freshSuffix next.val) (paidRelaxedContract (I.freshSuffix next.val))
      (zeroNormalAccounting (I.freshSuffix next.val)) penalty
  have hmrecord : Measurable record := measurable_entrySeedStartupAt input C .uncapped accounting policy.rule policy.measurable_rule next n
  have hmA : MeasurableSet A := hgate.prod (measurableSet_singleton _)
  have hmD : MeasurableSet D := hmA.prod MeasurableSet.univ
  have hmE : MeasurableSet E := measurableSet_historyGate input C .uncapped accounting policy.rule policy.measurable_rule n startup gate hgate
  have hmjoint : Measurable joint := hmrecord.prodMk ((input.measurable_restrictFreshWorld next.val).comp measurable_snd)
  have hmTarget : MeasurableRule targetRule := measurable_paidGuardedRule _ _
    (measurable_replayedSuffixCandidate next.val accounting policy.rule policy.measurable_rule startup)
  have hmF : Measurable F := measurable_const.add ((measurable_runPaidPenaltyCharge _ _ _ _ hmTarget penalty).comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hmap : μ.map joint = η.prod (input.freshSuffix next.val).worldLaw :=
    entrySeedStartupAt_jointFreshSuffixLaw input C .uncapped accounting policy ν next n
  have hE : E = record ⁻¹' A := historyGate_eq_entryRecordGate input C .uncapped accounting policy.rule next n startup gate hentry
  have hpre : joint ⁻¹' D = E := by
    rw [hE]
    ext sample
    simp only [joint, D, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
  have hmass : η A = μ E := by rw [Measure.map_apply hmrecord hmA, ← hE]
  have hrow (r : Seed × Option (Startup I)) : value ≤ ∫⁻ fresh, F (r, fresh) ∂(input.freshSuffix next.val).worldLaw := by
    change _ ≤ ∫⁻ fresh, startupObservationCharge input startup +
      runPaidPenaltyCharge _ _ _ targetRule penalty (r.1, fresh) ∂(input.freshSuffix next.val).worldLaw
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    exact add_le_add le_rfl (paidPenaltyValue_le_paidReplay_dirac input next.val accounting policy.rule policy.measurable_rule startup r.1 penalty)
  change value * μ E ≤ _
  calc
    value * μ E = value * η A := by rw [hmass]
    _ = ∫⁻ _r in A, value ∂η := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ r in A, ∫⁻ fresh, F (r, fresh) ∂(input.freshSuffix next.val).worldLaw ∂η := lintegral_mono hrow
    _ = ∫⁻ pair in D, F pair ∂η.prod (input.freshSuffix next.val).worldLaw := by
      rw [setLIntegral_prod F hmF.aemeasurable, Measure.restrict_univ]
    _ = ∫⁻ sample in E, F (joint sample) ∂μ := by
      rw [← hmap, setLIntegral_map hmD hmF hmjoint, hpre]
    _ ≤ ∫⁻ sample in E, runPaidPenaltyCharge input C accounting policy.rule penalty sample ∂μ := by
      apply setLIntegral_mono' hmE
      intro sample hs
      have h := paidReplay_runPaidPenaltyCharge_le input C hC accounting policy.rule policy.legal sample
        next.val n (hentry sample hs) fee hfee penalty
      have hstartup : publicStartup (run input C .uncapped accounting policy.rule sample n) = startup := hs.1
      have hprefix : (run input C .uncapped accounting policy.rule sample n).ledger.observationBill input.fees =
          startupObservationCharge input startup :=
        congrArg (startupObservationCharge input) hstartup
      dsimp only at h
      rw [hstartup, hprefix] at h
      exact h

end PDMenu
