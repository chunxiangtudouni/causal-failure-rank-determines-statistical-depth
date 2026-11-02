module

public import PaperProofs.Common.HistorySuffixSuccess

/-! B09 integration: Dirac-seed legal comparisons and the exact joint law
of real first-entry records with the complete fresh suffix world. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

theorem measurable_runPenaltyCharge (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hm : MeasurableRule rule) (penalty : ℝ≥0∞) :
    Measurable (runPenaltyCharge input C mode accounting rule penalty) := by
  classical
  unfold runPenaltyCharge
  exact (measurable_runObservationBill input C mode accounting rule hm).add
    (Measurable.ite (measurableSet_runSuccess input C mode accounting rule hm) measurable_const measurable_const)

theorem penaltyObjective_eq_lintegral_runPenaltyCharge (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hm : MeasurableRule rule) (ν : Measure Seed) (penalty : ℝ≥0∞) :
    penaltyObjective input C mode accounting rule ν penalty =
      ∫⁻ sample, runPenaltyCharge input C mode accounting rule penalty sample ∂input.seededWorldLaw ν := by
  classical
  have hfail : MeasurableSet {sample | ¬ runSuccess input C mode accounting rule sample} :=
    (measurableSet_runSuccess input C mode accounting rule hm).compl
  have heq : (fun sample => runPenaltyCharge input C mode accounting rule penalty sample) =
      fun sample => runObservationBill input C mode accounting rule sample +
        {sample | ¬ runSuccess input C mode accounting rule sample}.indicator (fun _ => penalty) sample := by
    funext sample
    by_cases hs : runSuccess input C mode accounting rule sample <;>
      simp only [runPenaltyCharge, hs, ↓reduceIte, Set.indicator, Set.mem_ofPred_eq, not_true_eq_false,
        not_false_eq_true, add_zero]
  rw [heq, lintegral_add_left (measurable_runObservationBill input C mode accounting rule hm),
    lintegral_indicator_const hfail]
  rfl

/-- The same globally legal replay policy can be compared under every
Dirac seed. This is a pointwise value lower bound, including zero/infinite
penalties, and needs no conditioning or normalization. -/
theorem healthyPenalty_le_replayedSuffix_dirac (input : StatisticalInput I) (first : ℕ)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hm : MeasurableRule rule)
    (startup : Startup I) (seed : Seed) (penalty : ℝ≥0∞) :
    let targetRule := guardedReplayRule (I := I.freshSuffix first) startup.availableTools
      (replayedSuffixCandidate first accounting rule startup)
    input.healthyPenalty first startup.availableTools penalty ≤
      ∫⁻ fresh, runPenaltyCharge (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first)) .uncapped
        (zeroNormalAccounting (I.freshSuffix first)) targetRule penalty (seed, fresh) ∂(input.freshSuffix first).worldLaw := by
  let targetPolicy := replayedSuffixAvailablePolicy input first accounting rule hm startup
  have hbound := availablePenaltyValue_le_policy_any_seed (input.freshSuffix first)
    (currentRelaxedContract (I.freshSuffix first)) (zeroNormalAccounting (I.freshSuffix first))
    startup.availableTools penalty (Measure.dirac seed) targetPolicy
  rw [penaltyObjective_eq_lintegral_runPenaltyCharge _ _ _ _ _ targetPolicy.val.measurable_rule] at hbound
  rw [StatisticalInput.seededWorldLaw, Measure.dirac_prod,
    lintegral_map (measurable_runPenaltyCharge _ _ _ _ _ targetPolicy.val.measurable_rule penalty)
      measurable_prodMk_left] at hbound
  exact hbound

omit [MeasurableSpace Seed] in
theorem historyGate_eq_entryRecordGate (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (next : I.Stage) (n : ℕ) (startup : Startup I) (gate : Set Seed)
    (hentry : ∀ sample ∈ historyGate input C mode accounting rule n startup gate,
      FirstEntryAt input C mode accounting rule next.val n sample) :
    historyGate input C mode accounting rule n startup gate =
      (entrySeedStartupAt input C mode accounting rule next n) ⁻¹' (gate ×ˢ {some startup}) := by
  ext sample
  constructor
  · intro hs
    have he := hentry sample hs
    refine ⟨hs.2, ?_⟩
    change entryStartupAt input C mode accounting rule next n sample = some startup
    exact (entryStartupAt_some_iff input C mode accounting rule next n sample startup).mpr ⟨he, hs.1⟩
  · rintro ⟨hg, hs⟩
    change entryStartupAt input C mode accounting rule next n sample = some startup at hs
    obtain ⟨_, hp⟩ := (entryStartupAt_some_iff input C mode accounting rule next n sample startup).mp hs
    exact ⟨hp, hg⟩

/-- Stronger first-entry mass inequality: genuine entry suffices. The saved
allocation-health condition of the frozen target need not be strengthened,
and no positive-mass, finite-charge or conditional-law premise is required. -/
theorem stageEntryHistoryPenaltyBridge_at (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentAllocation) (accounting : NormalAccounting I)
    (policy : Policy input C .native accounting Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (next : I.Stage) (n : ℕ) (startup : Startup I) (gate : Set Seed) (hgate : MeasurableSet gate)
    (hentry : ∀ sample ∈ historyGate input C .native accounting policy.rule n startup gate,
      FirstEntryAt input C .native accounting policy.rule next.val n sample)
    (penalty : ℝ≥0∞) :
    input.healthyPenalty next.val startup.availableTools penalty *
      input.seededWorldLaw ν (historyGate input C .native accounting policy.rule n startup gate) ≤
      ∫⁻ sample in historyGate input C .native accounting policy.rule n startup gate,
        historyComparisonCharge input C .native accounting policy.rule n penalty sample ∂input.seededWorldLaw ν := by
  let E := historyGate input C .native accounting policy.rule n startup gate
  let μ := input.seededWorldLaw ν
  let record := entrySeedStartupAt input C .native accounting policy.rule next n
  let η := μ.map record
  let A : Set (Seed × Option (Startup I)) := gate ×ˢ {some startup}
  let D : Set ((Seed × Option (Startup I)) × (input.freshSuffix next.val).World) := A ×ˢ Set.univ
  let joint := fun sample : Seed × input.World => (record sample, input.restrictFreshWorld next.val sample.2)
  let targetRule := guardedReplayRule (I := I.freshSuffix next.val) startup.availableTools
    (replayedSuffixCandidate next.val accounting policy.rule startup)
  let F := fun pair : (Seed × Option (Startup I)) × (input.freshSuffix next.val).World =>
    runPenaltyCharge (input.freshSuffix next.val) (currentRelaxedContract (I.freshSuffix next.val)) .uncapped
      (zeroNormalAccounting (I.freshSuffix next.val)) targetRule penalty (pair.1.1, pair.2)
  have hmrecord : Measurable record := measurable_entrySeedStartupAt input C .native accounting policy.rule policy.measurable_rule next n
  have hmA : MeasurableSet A := hgate.prod (measurableSet_singleton _)
  have hmD : MeasurableSet D := hmA.prod MeasurableSet.univ
  have hmE : MeasurableSet E := measurableSet_historyGate input C .native accounting policy.rule policy.measurable_rule n startup gate hgate
  have hmjoint : Measurable joint := hmrecord.prodMk ((input.measurable_restrictFreshWorld next.val).comp measurable_snd)
  have hmTarget : MeasurableRule targetRule := measurable_guardedReplayRule _ _
    (measurable_replayedSuffixCandidate next.val accounting policy.rule policy.measurable_rule startup)
  have hmF : Measurable F := (measurable_runPenaltyCharge _ _ _ _ _ hmTarget penalty).comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hmap : μ.map joint = η.prod (input.freshSuffix next.val).worldLaw :=
    entrySeedStartupAt_jointFreshSuffixLaw input C .native accounting policy ν next n
  have hE : E = record ⁻¹' A := historyGate_eq_entryRecordGate input C .native accounting policy.rule next n startup gate hentry
  have hpre : joint ⁻¹' D = E := by
    rw [hE]
    ext sample
    simp only [joint, D, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
  have hmass : η A = μ E := by rw [Measure.map_apply hmrecord hmA, ← hE]
  have hrow (r : Seed × Option (Startup I)) :
      input.healthyPenalty next.val startup.availableTools penalty ≤ ∫⁻ fresh, F (r, fresh) ∂(input.freshSuffix next.val).worldLaw :=
    healthyPenalty_le_replayedSuffix_dirac input next.val accounting policy.rule policy.measurable_rule startup r.1 penalty
  change input.healthyPenalty next.val startup.availableTools penalty * μ E ≤ _
  calc
    input.healthyPenalty next.val startup.availableTools penalty * μ E =
        input.healthyPenalty next.val startup.availableTools penalty * η A := by rw [hmass]
    _ = ∫⁻ _r in A, input.healthyPenalty next.val startup.availableTools penalty ∂η := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ r in A, ∫⁻ fresh, F (r, fresh) ∂(input.freshSuffix next.val).worldLaw ∂η := lintegral_mono hrow
    _ = ∫⁻ pair in D, F pair ∂η.prod (input.freshSuffix next.val).worldLaw := by
      rw [setLIntegral_prod F hmF.aemeasurable, Measure.restrict_univ]
    _ = ∫⁻ sample in E, F (joint sample) ∂μ := by
      rw [← hmap, setLIntegral_map hmD hmF hmjoint, hpre]
    _ ≤ ∫⁻ sample in E, historyComparisonCharge input C .native accounting policy.rule n penalty sample ∂μ := by
      apply setLIntegral_mono' hmE
      intro sample hs
      have h := replayedSuffix_penaltyCharge_le input C hC.1 hC.2 .native accounting policy.rule policy.legal sample next.val n (hentry sample hs) penalty
      have hstartup : publicStartup (run input C .native accounting policy.rule sample n) = startup := hs.1
      dsimp only at h
      rw [hstartup] at h
      exact h

universe uBridge

/-- The exact formal first-entry B09 target, derived from the actual replay policy,
its pathwise charges/success comparison and first-entry product law. -/
theorem stageEntryHistoryPenaltyBridge (input : StatisticalInput I) :
    StageEntryHistoryPenaltyBridge.{uBridge} input := by
  intro C hC accounting Seed m
  let : MeasurableSpace Seed := m
  intro policy ν hν next n hnext startup gate hgate hhealthy penalty
  let : IsProbabilityMeasure ν := hν
  by_cases hterminal : I.stageCount ≤ next
  · exact history_bridge_terminal input C accounting policy.rule ν next n hterminal startup gate penalty
  · let stage : I.Stage := ⟨next, Nat.lt_of_not_ge hterminal⟩
    exact stageEntryHistoryPenaltyBridge_at input C hC accounting policy ν stage n startup gate hgate
      (fun sample hs => (hhealthy sample hs).1) penalty

theorem healthyStageEntryHistoryPenaltyBridge (input : StatisticalInput I) :
    HealthyStageEntryHistoryPenaltyBridge.{uBridge} input :=
  StageEntryHistoryPenaltyBridge.healthy_projection input (stageEntryHistoryPenaltyBridge input)

end PaperProofs.Common.Native
