module

public import PaperProofs.Common.FreshSuffixWorld
public import PaperProofs.Common.HistoryPenaltyBridge

/-!
Exact first-entry public-snapshot/seed-gate law against the RENAMED complete
fresh-suffix world used by healthyPenalty. This composes actual pre-birth
causality with the unchanged original product law; no strategy simulation,
regular conditional probability, success conditioning or positive-mass
assumption is supplied as a premise.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance}

abbrev FutureWorldAt (input : StatisticalInput I) (first : Nat) :=
  ∀ i : {i : I.Stage // first ≤ i.val}, input.StageSample i.val

def renumberFutureWorld (input : StatisticalInput I) :
    (first : Nat) → FutureWorldAt input first → (input.freshSuffix first).World
  | 0 => fun future stage => future ⟨stage, Nat.zero_le _⟩
  | first + 1 => fun future stage => future ⟨I.freshStageLift (first + 1) stage, by
      change first + 1 ≤ first + 1 + stage.val
      omega⟩

theorem measurable_renumberFutureWorld (input : StatisticalInput I) (first : Nat) :
    Measurable (renumberFutureWorld input first) := by
  cases first with
  | zero => exact measurable_pi_iff.mpr (fun stage => measurable_pi_apply (⟨stage, Nat.zero_le _⟩ : {i : I.Stage // 0 ≤ i.val}))
  | succ first => exact measurable_pi_iff.mpr (fun stage => measurable_pi_apply
      (⟨I.freshStageLift (first + 1) stage, by change first + 1 ≤ first + 1 + stage.val; omega⟩ :
        {i : I.Stage // first + 1 ≤ i.val}))

theorem restrictFreshWorld_eq_renumberFutureWorld (input : StatisticalInput I) (first : Nat)
    (world : input.World) :
    input.restrictFreshWorld first world =
      renumberFutureWorld input first (fun i => world i.val) := by cases first <;> rfl

section Entry

variable {Seed : Type*} [MeasurableSpace Seed]

theorem entrySeedStartupAt_independent_freshSuffix (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (next : I.Stage) (n : Nat) :
    IndepFun (entrySeedStartupAt input C mode accounting policy.rule next n)
      (fun sample : Seed × input.World => input.restrictFreshWorld next.val sample.2)
        (input.seededWorldLaw ν) := by
  have h := (entrySeedStartupAt_independent_unborn input C mode accounting policy ν next n).comp
    measurable_id (measurable_renumberFutureWorld input next.val)
  have heq : (fun sample : Seed × input.World => input.restrictFreshWorld next.val sample.2) =
      renumberFutureWorld input next.val ∘ (fun sample : Seed × input.World => unbornView input next sample.2) := by
    funext sample
    exact restrictFreshWorld_eq_renumberFutureWorld input next.val sample.2
  rw [heq]
  exact h

theorem seededWorldLaw_freshSuffixWorld (input : StatisticalInput I) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (first : Nat) :
    (input.seededWorldLaw ν).map (fun sample : Seed × input.World => input.restrictFreshWorld first sample.2) =
      (input.freshSuffix first).worldLaw := by
  change (input.seededWorldLaw ν).map (input.restrictFreshWorld first ∘ Prod.snd) = _
  rw [← Measure.map_map (input.measurable_restrictFreshWorld first) measurable_snd,
    input.seededWorldLaw_world ν, input.restrictFreshWorld_worldLaw]

theorem entrySeedStartupAt_jointFreshSuffixLaw (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (next : I.Stage) (n : Nat) :
    (input.seededWorldLaw ν).map (fun sample =>
        (entrySeedStartupAt input C mode accounting policy.rule next n sample,
          input.restrictFreshWorld next.val sample.2)) =
      ((input.seededWorldLaw ν).map (entrySeedStartupAt input C mode accounting policy.rule next n)).prod
        (input.freshSuffix next.val).worldLaw := by
  have hind := entrySeedStartupAt_independent_freshSuffix input C mode accounting policy ν next n
  have hm := measurable_entrySeedStartupAt input C mode accounting policy.rule policy.measurable_rule next n
  have hf : Measurable (fun sample : Seed × input.World => input.restrictFreshWorld next.val sample.2) :=
    (input.measurable_restrictFreshWorld next.val).comp measurable_snd
  rw [hind.map_prod_eq_prod_map_map hm.aemeasurable hf.aemeasurable, seededWorldLaw_freshSuffixWorld]

/-- Exact integration of any measurable future charge depending on the
entire entry seed/snapshot. Infinite values and zero-mass atoms are retained;
no division by an entry probability or integrability is used. -/
theorem entrySeedStartupAt_freshSuffix_lintegral (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (next : I.Stage) (n : Nat)
    (f : (Seed × Option (Startup I)) × (input.freshSuffix next.val).World → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ sample, f (entrySeedStartupAt input C mode accounting policy.rule next n sample,
        input.restrictFreshWorld next.val sample.2) ∂input.seededWorldLaw ν) =
      ∫⁻ pair, f pair ∂(((input.seededWorldLaw ν).map
          (entrySeedStartupAt input C mode accounting policy.rule next n)).prod
            (input.freshSuffix next.val).worldLaw) := by
  have hm := measurable_entrySeedStartupAt input C mode accounting policy.rule policy.measurable_rule next n
  have hfut : Measurable (fun sample : Seed × input.World => input.restrictFreshWorld next.val sample.2) :=
    (input.measurable_restrictFreshWorld next.val).comp measurable_snd
  rw [← entrySeedStartupAt_jointFreshSuffixLaw input C mode accounting policy ν next n]
  exact (lintegral_map hf (hm.prodMk hfut)).symm

theorem entry_snapshot_seedGate_freshSuffix_mass (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (next : I.Stage) (n : Nat) (startup : Startup I)
    (gate : Set Seed) (hgate : MeasurableSet gate)
    (futureEvent : Set (input.freshSuffix next.val).World) (hfuture : MeasurableSet futureEvent) :
    input.seededWorldLaw ν
        ((entrySeedStartupAt input C mode accounting policy.rule next n) ⁻¹' (gate ×ˢ {some startup}) ∩
          (fun sample : Seed × input.World => input.restrictFreshWorld next.val sample.2) ⁻¹' futureEvent) =
      input.seededWorldLaw ν
          ((entrySeedStartupAt input C mode accounting policy.rule next n) ⁻¹' (gate ×ˢ {some startup})) *
        (input.freshSuffix next.val).worldLaw futureEvent := by
  have hind := entrySeedStartupAt_independent_freshSuffix input C mode accounting policy ν next n
  rw [hind.measure_inter_preimage_eq_mul (gate ×ˢ {some startup}) futureEvent
    (hgate.prod (measurableSet_singleton _)) hfuture]
  congr 1
  have hm : Measurable (fun sample : Seed × input.World => input.restrictFreshWorld next.val sample.2) :=
    (input.measurable_restrictFreshWorld next.val).comp measurable_snd
  rw [← Measure.map_apply hm hfuture, seededWorldLaw_freshSuffixWorld]

/-- Universe-polymorphic joint record. It has the same small-universe
representation as entrySeedHistory, without restricting a comparison seed. -/
noncomputable def entryHistorySeedRecord (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (next : I.Stage) (sample : Seed × input.World) : Seed × EntryHistory I :=
  (sample.1, entryHistory input C mode accounting rule next sample)

theorem measurable_entryHistorySeedRecord (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hm : MeasurableRule rule) (next : I.Stage) :
    Measurable (entryHistorySeedRecord input C mode accounting rule next) :=
  measurable_fst.prodMk (measurable_entryHistory input C mode accounting rule hm next)

theorem entryHistorySeedRecord_independent_freshSuffix (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (next : I.Stage) :
    IndepFun (entryHistorySeedRecord input C mode accounting policy.rule next)
      (fun sample : Seed × input.World => input.restrictFreshWorld next.val sample.2)
        (input.seededWorldLaw ν) := by
  let complete : Seed × input.PastWorld next → Seed × input.World :=
    fun sample => (sample.1, completePastWorld input next sample.2)
  have hc : Measurable complete := measurable_fst.prodMk
    ((measurable_completePastWorld input next).comp measurable_snd)
  let joint : Seed × input.PastWorld next → Seed × EntryHistory I :=
    fun sample => (sample.1, entryHistory input C mode accounting policy.rule next (complete sample))
  have hm : Measurable joint := measurable_fst.prodMk
    ((measurable_entryHistory input C mode accounting policy.rule policy.measurable_rule next).comp hc)
  have heq : entryHistorySeedRecord input C mode accounting policy.rule next =
      fun sample => joint (input.preBirthView next sample) := by
    funext sample
    apply Prod.ext
    · rfl
    · exact (entryHistory_eq_of_past input C mode accounting policy.rule policy.legal sample.1 sample.2
        (completePastWorld input next (fun i => sample.2 i.val)) next
        (fun i hi => completePastWorld_apply_past input next (fun i => sample.2 i.val) i hi)).symm
  have hind := (preBirthView_independent_unborn input ν next).comp hm
    (measurable_renumberFutureWorld input next.val)
  have hf : (fun sample : Seed × input.World => input.restrictFreshWorld next.val sample.2) =
      renumberFutureWorld input next.val ∘ (fun sample : Seed × input.World => unbornView input next sample.2) := by
    funext sample
    exact restrictFreshWorld_eq_renumberFutureWorld input next.val sample.2
  rw [heq, hf]
  exact hind

theorem entryHistorySeedRecord_jointFreshSuffixLaw (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (next : I.Stage) :
    (input.seededWorldLaw ν).map (fun sample =>
        (entryHistorySeedRecord input C mode accounting policy.rule next sample,
          input.restrictFreshWorld next.val sample.2)) =
      ((input.seededWorldLaw ν).map (entryHistorySeedRecord input C mode accounting policy.rule next)).prod
        (input.freshSuffix next.val).worldLaw := by
  have hind := entryHistorySeedRecord_independent_freshSuffix input C mode accounting policy ν next
  have hm := measurable_entryHistorySeedRecord input C mode accounting policy.rule policy.measurable_rule next
  have hf : Measurable (fun sample : Seed × input.World => input.restrictFreshWorld next.val sample.2) :=
    (input.measurable_restrictFreshWorld next.val).comp measurable_snd
  rw [hind.map_prod_eq_prod_map_map hm.aemeasurable hf.aemeasurable, seededWorldLaw_freshSuffixWorld]

end Entry

end PaperProofs.Common.Native
