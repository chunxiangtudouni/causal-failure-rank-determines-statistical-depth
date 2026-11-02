module

public import PaperProofs.Common.HistorySuffixBridge
import Lean.Elab.Tactic.Omega

/-!
B08 continuation extraction retaining the INITIAL tool restriction R.
The outer guard is globally legal. On real source-entry worlds its rejected
allocation branch is unreachable, as proved from the source UsesOnly R and
permanent occupation of every saved commitment.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance} {Seed : Type*}

/-- An availability guard preserves a particular real run if each reached
allocation uses the indicated set. The condition concerns actual actions,
and the conclusion is equality of complete native states at every clock. -/
theorem run_guardedReplayRule_eq (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hcurrent : C.allocation = .currentWindow)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (available : Finset I.Tool)
    (sample : Seed × input.World)
    (halloc : ∀ n, (run input C .uncapped accounting rule sample n).halted = false →
      ∀ handle tool, rule sample.1 (run input C .uncapped accounting rule sample n).history = .allocate handle tool →
        tool ∈ available) :
    ∀ n, run input C .uncapped accounting (guardedReplayRule available rule) sample n =
      run input C .uncapped accounting rule sample n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hh : (run input C .uncapped accounting rule sample n).halted = true
    · have hg : (run input C .uncapped accounting (guardedReplayRule available rule) sample n).halted = true := by rw [ih]; exact hh
      rw [run_succ_of_halted input C .uncapped accounting _ sample n hg,
        run_succ_of_halted input C .uncapped accounting rule sample n hh, ih]
    · have ha : (run input C .uncapped accounting rule sample n).halted = false := Bool.eq_false_iff.mpr hh
      obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting rule hlegal sample n
      obtain ⟨next, hs⟩ := hlegal sample.1 _ _ m _ hp ha
      have hguard := guardedReplayRule_eq_of_step input C hearly hcurrent .uncapped accounting rule rule
        sample.1 _ _ hp available hs (halloc n ha)
      have hga : (run input C .uncapped accounting (guardedReplayRule available rule) sample n).halted = false := by rw [ih]; exact ha
      have hgs : Step input C .uncapped accounting (worldTapes input sample.2)
          (run input C .uncapped accounting (guardedReplayRule available rule) sample n)
          (guardedReplayRule available rule sample.1
            (run input C .uncapped accounting (guardedReplayRule available rule) sample n).history) next := by
        rw [ih, hguard]
        exact hs
      rw [run_succ_of_step input C .uncapped accounting _ sample n next hga hgs,
        run_succ_of_step input C .uncapped accounting rule sample n next ha hs]

theorem guardedReplayRule_allocate_source (available : Finset I.Tool) (raw : PolicyRule I Seed)
    (seed : Seed) (history : List (VisibleEvent I)) (handle : MismatchHandle I) (tool : I.Tool)
    (h : guardedReplayRule available raw seed history = .allocate handle tool) :
    raw seed history = .allocate handle tool := by
  unfold guardedReplayRule at h
  split at h
  next ha => exact h
  next ha => cases h

/-- Source UsesOnly R and saved commitment freshness give the real target's
allocation membership in R minus EVERY saved commitment, including pending
ones and commitments on paths that already fail. -/
theorem replayedSuffix_allocations_restricted (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentAllocation) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C .uncapped accounting rule)
    (R : Finset I.Tool) (hR : UsesOnly input C accounting rule R)
    (sample : Seed × input.World) (first start : ℕ)
    (hentry : FirstEntryAt input C .uncapped accounting rule first start sample) :
    let startup := publicStartup (run input C .uncapped accounting rule sample start)
    let raw := replayedSuffixCandidate first accounting rule startup
    let targetRule := guardedReplayRule (I := I.freshSuffix first) startup.availableTools raw
    let targetSample := (sample.1, input.restrictFreshWorld first sample.2)
    ∀ k, (run (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first)) .uncapped
        (zeroNormalAccounting (I.freshSuffix first)) targetRule targetSample k).halted = false →
      ∀ handle tool, targetRule sample.1
        (run (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first)) .uncapped
          (zeroNormalAccounting (I.freshSuffix first)) targetRule targetSample k).history = .allocate handle tool →
        tool ∈ R \ startup.committedTools := by
  let startup := publicStartup (run input C .uncapped accounting rule sample start)
  let raw := replayedSuffixCandidate first accounting rule startup
  let targetRule := guardedReplayRule (I := I.freshSuffix first) startup.availableTools raw
  let targetSample := (sample.1, input.restrictFreshWorld first sample.2)
  let sourceAt := fun n => run input C .uncapped accounting rule sample n
  let targetAt := fun k => run (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first)) .uncapped
    (zeroNormalAccounting (I.freshSuffix first)) targetRule targetSample k
  change ∀ k, (targetAt k).halted = false → ∀ handle tool,
    targetRule sample.1 (targetAt k).history = .allocate handle tool → tool ∈ R \ startup.committedTools
  intro k hactive handle tool htargetAlloc
  have hraw := guardedReplayRule_allocate_source (I := I.freshSuffix first) startup.availableTools raw sample.1 (targetAt k).history handle tool htargetAlloc
  let n := replaySourceClock input C .uncapped accounting rule sample first start k
  let result := settleOldExecutions first accounting rule (I.toolCount + 1) sample.1 (publicStartup (sourceAt n))
  obtain ⟨view, hreplay⟩ := replayedSuffix_fullRun input C hC.1 hC.2 .uncapped accounting rule hlegal sample first start hentry k
  change raw sample.1 (targetAt k).history = .allocate handle tool at hraw
  change (match replaySuffixHistory first accounting rule sample.1 startup (targetAt k).history with
    | none => (Action.abandon : Action (I.freshSuffix first))
    | some cache => suffixActionAtPublicCache first accounting rule sample.1 cache (targetAt k).history) = .allocate handle tool at hraw
  rw [hreplay] at hraw
  change (if result.1.halted then .stop else
    (suffixActionOf first (targetAt k).history (rule sample.1 result.1.history)).getD .abandon) = .allocate handle tool at hraw
  have hresultActive : result.1.halted = false := by
    cases hh : result.1.halted with
    | false => rfl
    | true => rw [hh] at hraw; cases hraw
  rw [hresultActive] at hraw
  simp only [Bool.false_eq_true, ↓reduceIte] at hraw
  have hproject : suffixActionOf first (targetAt k).history (rule sample.1 result.1.history) = some (.allocate handle tool) := by
    cases hp : suffixActionOf first (targetAt k).history (rule sample.1 result.1.history) with
    | none => rw [hp] at hraw; cases hraw
    | some action =>
      have he : action = .allocate handle tool := by simpa only [hp, Option.getD_some] using hraw
      exact congrArg some he
  obtain ⟨sourceHandle, hsourceAction⟩ := suffixActionOf_allocate_source first (targetAt k).history _ handle tool hproject
  have hr : result.1 = publicStartup (sourceAt (n + result.2)) :=
    settleOldExecutions_actual input C .uncapped accounting rule hlegal sample first _ n
  rw [hr] at hsourceAction hresultActive
  change rule sample.1 (run input C .uncapped accounting rule sample (n + result.2)).history =
    .allocate sourceHandle tool at hsourceAction
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting rule hlegal sample (n + result.2)
  obtain ⟨next, hs⟩ := hlegal sample.1 _ _ m _ hp hresultActive
  have hinR : tool ∈ R := hR sample.1 _ _ m _ hp hresultActive sourceHandle tool hsourceAction
  rw [hsourceAction] at hs
  have hfree := allocated_tool_available_at_saved_prefix input C .uncapped accounting rule hlegal sample start (n + result.2)
    (by have hn := replaySourceClock_ge_start input C .uncapped accounting rule sample first start k; change start ≤ n at hn; omega)
    sourceHandle tool hs
  exact Finset.mem_sdiff.mpr ⟨hinR, (Finset.mem_sdiff.mp hfree).2⟩

section Measurable

variable [MeasurableSpace Seed]

/-- Globally legal suffix policy using only the original R with all saved
commitments removed. The new guard is allowed to abandon off the selected
entry worlds, and it has no information about the future system world. -/
noncomputable def replayedSuffixRestrictedPolicy (input : StatisticalInput I) (first : ℕ)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hm : MeasurableRule rule)
    (R : Finset I.Tool) (startup : Startup I) :
    AvailablePolicy (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first))
      (zeroNormalAccounting (I.freshSuffix first)) (R \ startup.committedTools) Seed := by
  let base := replayedSuffixAvailablePolicy input first accounting rule hm startup
  let S := R \ startup.committedTools
  exact ⟨{
    rule := guardedReplayRule (I := I.freshSuffix first) S base.val.rule
    measurable_rule := measurable_guardedReplayRule (I := I.freshSuffix first) S base.val.rule base.val.measurable_rule
    legal := guardedReplayRule_legal (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first))
      rfl rfl (zeroNormalAccounting (I.freshSuffix first)) S base.val.rule },
    guardedReplayRule_usesOnly (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first))
      (zeroNormalAccounting (I.freshSuffix first)) S base.val.rule⟩

/-- On each genuine source-entry world the R guard changes no target state,
action, observation, deadline, execution or accounting response. -/
theorem replayedSuffixRestricted_run_eq (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentAllocation) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hm : MeasurableRule rule) (hlegal : LegalRule input C .uncapped accounting rule)
    (R : Finset I.Tool) (hR : UsesOnly input C accounting rule R)
    (sample : Seed × input.World) (first start : ℕ)
    (hentry : FirstEntryAt input C .uncapped accounting rule first start sample) :
    let startup := publicStartup (run input C .uncapped accounting rule sample start)
    ∀ k, run (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first)) .uncapped
        (zeroNormalAccounting (I.freshSuffix first))
        (replayedSuffixRestrictedPolicy input first accounting rule hm R startup).val.rule
        (sample.1, input.restrictFreshWorld first sample.2) k =
      run (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first)) .uncapped
        (zeroNormalAccounting (I.freshSuffix first))
        (replayedSuffixAvailablePolicy input first accounting rule hm startup).val.rule
        (sample.1, input.restrictFreshWorld first sample.2) k := by
  let startup := publicStartup (run input C .uncapped accounting rule sample start)
  let base := replayedSuffixAvailablePolicy input first accounting rule hm startup
  have halloc := replayedSuffix_allocations_restricted input C hC accounting rule hlegal R hR sample first start hentry
  dsimp only [replayedSuffixRestrictedPolicy]
  exact run_guardedReplayRule_eq (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first))
    rfl rfl (zeroNormalAccounting (I.freshSuffix first)) base.val.rule base.val.legal
    (R \ startup.committedTools) (sample.1, input.restrictFreshWorld first sample.2) halloc

theorem replayedSuffixRestricted_penaltyCharge_le (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentAllocation) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hm : MeasurableRule rule) (hlegal : LegalRule input C .uncapped accounting rule)
    (R : Finset I.Tool) (hR : UsesOnly input C accounting rule R)
    (sample : Seed × input.World) (first start : ℕ)
    (hentry : FirstEntryAt input C .uncapped accounting rule first start sample) (penalty : ℝ≥0∞) :
    let startup := publicStartup (run input C .uncapped accounting rule sample start)
    runPenaltyCharge (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first))
      (replayedSuffixRestrictedPolicy input first accounting rule hm R startup).val.rule penalty
      (sample.1, input.restrictFreshWorld first sample.2) ≤
      historyComparisonCharge input C .uncapped accounting rule start penalty sample := by
  classical
  have hrun := replayedSuffixRestricted_run_eq input C hC accounting rule hm hlegal R hR sample first start hentry
  have hbase := replayedSuffix_penaltyCharge_le input C hC.1 hC.2 .uncapped accounting rule hlegal sample first start hentry penalty
  dsimp only
  unfold runPenaltyCharge runObservationBill runSuccess at hbase ⊢
  simp_rw [hrun]
  exact hbase

theorem healthyPenalty_le_restrictedSuffix_dirac (input : StatisticalInput I) (first : ℕ)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hm : MeasurableRule rule)
    (R : Finset I.Tool) (startup : Startup I) (seed : Seed) (penalty : ℝ≥0∞) :
    input.healthyPenalty first (R \ startup.committedTools) penalty ≤
      ∫⁻ fresh, runPenaltyCharge (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first)) .uncapped
        (zeroNormalAccounting (I.freshSuffix first))
        (replayedSuffixRestrictedPolicy input first accounting rule hm R startup).val.rule penalty (seed, fresh)
          ∂(input.freshSuffix first).worldLaw := by
  let targetPolicy := replayedSuffixRestrictedPolicy input first accounting rule hm R startup
  have hbound := availablePenaltyValue_le_policy_any_seed (input.freshSuffix first)
    (currentRelaxedContract (I.freshSuffix first)) (zeroNormalAccounting (I.freshSuffix first))
    (R \ startup.committedTools) penalty (Measure.dirac seed) targetPolicy
  rw [penaltyObjective_eq_lintegral_runPenaltyCharge _ _ _ _ _ targetPolicy.val.measurable_rule] at hbound
  rw [StatisticalInput.seededWorldLaw, Measure.dirac_prod,
    lintegral_map (measurable_runPenaltyCharge _ _ _ _ _ targetPolicy.val.measurable_rule penalty)
      measurable_prodMk_left] at hbound
  exact hbound

/-- Real R-restricted first-entry continuation lower bound. It uses the
unchanged independent healthyPenalty infimum with precisely R minus saved
commitments. Pending corrections, failure paths, arbitrary seeds, null entry
events and infinite charges/penalties remain in the statement. -/
theorem restrictedStageEntryHistoryPenaltyBridge_at (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentAllocation) (accounting : NormalAccounting I) (R : Finset I.Tool)
    (policy : AvailablePolicy input C accounting R Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (next : I.Stage) (n : ℕ) (startup : Startup I) (gate : Set Seed) (hgate : MeasurableSet gate)
    (hentry : ∀ sample ∈ historyGate input C .uncapped accounting policy.val.rule n startup gate,
      FirstEntryAt input C .uncapped accounting policy.val.rule next.val n sample)
    (penalty : ℝ≥0∞) :
    input.healthyPenalty next.val (R \ startup.committedTools) penalty *
      input.seededWorldLaw ν (historyGate input C .uncapped accounting policy.val.rule n startup gate) ≤
      ∫⁻ sample in historyGate input C .uncapped accounting policy.val.rule n startup gate,
        historyComparisonCharge input C .uncapped accounting policy.val.rule n penalty sample ∂input.seededWorldLaw ν := by
  let E := historyGate input C .uncapped accounting policy.val.rule n startup gate
  let μ := input.seededWorldLaw ν
  let record := entrySeedStartupAt input C .uncapped accounting policy.val.rule next n
  let η := μ.map record
  let A : Set (Seed × Option (Startup I)) := gate ×ˢ {some startup}
  let D : Set ((Seed × Option (Startup I)) × (input.freshSuffix next.val).World) := A ×ˢ Set.univ
  let joint := fun sample : Seed × input.World => (record sample, input.restrictFreshWorld next.val sample.2)
  let targetPolicy := replayedSuffixRestrictedPolicy input next.val accounting policy.val.rule policy.val.measurable_rule R startup
  let F := fun pair : (Seed × Option (Startup I)) × (input.freshSuffix next.val).World =>
    runPenaltyCharge (input.freshSuffix next.val) (currentRelaxedContract (I.freshSuffix next.val)) .uncapped
      (zeroNormalAccounting (I.freshSuffix next.val)) targetPolicy.val.rule penalty (pair.1.1, pair.2)
  have hmrecord : Measurable record := measurable_entrySeedStartupAt input C .uncapped accounting policy.val.rule policy.val.measurable_rule next n
  have hmA : MeasurableSet A := hgate.prod (measurableSet_singleton _)
  have hmD : MeasurableSet D := hmA.prod MeasurableSet.univ
  have hmE : MeasurableSet E := measurableSet_historyGate input C .uncapped accounting policy.val.rule policy.val.measurable_rule n startup gate hgate
  have hmjoint : Measurable joint := hmrecord.prodMk ((input.measurable_restrictFreshWorld next.val).comp measurable_snd)
  have hmF : Measurable F := (measurable_runPenaltyCharge _ _ _ _ _ targetPolicy.val.measurable_rule penalty).comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hmap : μ.map joint = η.prod (input.freshSuffix next.val).worldLaw :=
    entrySeedStartupAt_jointFreshSuffixLaw input C .uncapped accounting policy.val ν next n
  have hE : E = record ⁻¹' A := historyGate_eq_entryRecordGate input C .uncapped accounting policy.val.rule next n startup gate hentry
  have hpre : joint ⁻¹' D = E := by
    rw [hE]
    ext sample
    simp only [joint, D, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
  have hmass : η A = μ E := by rw [Measure.map_apply hmrecord hmA, ← hE]
  have hrow (r : Seed × Option (Startup I)) :
      input.healthyPenalty next.val (R \ startup.committedTools) penalty ≤ ∫⁻ fresh, F (r, fresh) ∂(input.freshSuffix next.val).worldLaw :=
    healthyPenalty_le_restrictedSuffix_dirac input next.val accounting policy.val.rule policy.val.measurable_rule R startup r.1 penalty
  change input.healthyPenalty next.val (R \ startup.committedTools) penalty * μ E ≤ _
  calc
    input.healthyPenalty next.val (R \ startup.committedTools) penalty * μ E =
        input.healthyPenalty next.val (R \ startup.committedTools) penalty * η A := by rw [hmass]
    _ = ∫⁻ _r in A, input.healthyPenalty next.val (R \ startup.committedTools) penalty ∂η := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ r in A, ∫⁻ fresh, F (r, fresh) ∂(input.freshSuffix next.val).worldLaw ∂η := lintegral_mono hrow
    _ = ∫⁻ pair in D, F pair ∂η.prod (input.freshSuffix next.val).worldLaw := by
      rw [setLIntegral_prod F hmF.aemeasurable, Measure.restrict_univ]
    _ = ∫⁻ sample in E, F (joint sample) ∂μ := by
      rw [← hmap, setLIntegral_map hmD hmF hmjoint, hpre]
    _ ≤ ∫⁻ sample in E, historyComparisonCharge input C .uncapped accounting policy.val.rule n penalty sample ∂μ := by
      apply setLIntegral_mono' hmE
      intro sample hs
      have h := replayedSuffixRestricted_penaltyCharge_le input C hC accounting policy.val.rule
        policy.val.measurable_rule policy.val.legal R policy.property sample next.val n (hentry sample hs) penalty
      have hstartup : publicStartup (run input C .uncapped accounting policy.val.rule sample n) = startup := hs.1
      dsimp only at h
      rw [hstartup] at h
      exact h

/-- The same actual R-restricted continuation theorem includes terminal and
empty suffixes; no existence of a next stage is assumed by its caller. -/
theorem restrictedStageEntryHistoryPenaltyBridge (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentAllocation) (accounting : NormalAccounting I) (R : Finset I.Tool)
    (policy : AvailablePolicy input C accounting R Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (first n : ℕ) (startup : Startup I) (gate : Set Seed) (hgate : MeasurableSet gate)
    (hentry : ∀ sample ∈ historyGate input C .uncapped accounting policy.val.rule n startup gate,
      FirstEntryAt input C .uncapped accounting policy.val.rule first n sample)
    (penalty : ℝ≥0∞) :
    input.healthyPenalty first (R \ startup.committedTools) penalty *
      input.seededWorldLaw ν (historyGate input C .uncapped accounting policy.val.rule n startup gate) ≤
      ∫⁻ sample in historyGate input C .uncapped accounting policy.val.rule n startup gate,
        historyComparisonCharge input C .uncapped accounting policy.val.rule n penalty sample ∂input.seededWorldLaw ν := by
  by_cases ht : I.stageCount ≤ first
  · rw [input.healthyPenalty_terminal first ht, zero_mul]
    exact bot_le
  · let next : I.Stage := ⟨first, Nat.lt_of_not_ge ht⟩
    exact restrictedStageEntryHistoryPenaltyBridge_at input C hC accounting R policy ν next n startup gate hgate hentry penalty

end Measurable

end PaperProofs.Common.Native
