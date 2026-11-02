module

public import PaperProofs.Common.HistorySuffixWorld

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetPreBirthEntryLaw046

open Common Common.Native MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

/-- The ENTIRE original prebirth view is retained jointly with the actual
fixed-clock public entry snapshot. No success selector is in this record. -/
noncomputable def preBirthStartupAt (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (next : I.Stage) (n : ℕ) (sample : Seed × input.World) :
    (Seed × input.PastWorld next) × Option (Startup I) :=
  (input.preBirthView next sample, entryStartupAt input C mode accounting source next n sample)

theorem measurable_preBirthStartupAt (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hm : MeasurableRule source) (next : I.Stage) (n : ℕ) :
    Measurable (preBirthStartupAt input C mode accounting source next n) :=
  (input.measurable_preBirthView next).prodMk
    (measurable_entryStartupAt input C mode accounting source hm next n)

theorem preBirthStartupAt_independent_freshSuffix (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : Policy input C mode accounting Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (next : I.Stage) (n : ℕ) :
    IndepFun (preBirthStartupAt input C mode accounting source.rule next n)
      (fun sample : Seed × input.World => input.restrictFreshWorld next.val sample.2)
        (input.seededWorldLaw ν) := by
  obtain ⟨record, hmrecord, hrecord⟩ := entryStartupAt_factorization input C mode accounting source next n
  let joinedRecord : Seed × input.PastWorld next → (Seed × input.PastWorld next) × Option (Startup I) :=
    fun past => (past, record past)
  have hm : Measurable joinedRecord := measurable_id.prodMk hmrecord
  have heq : preBirthStartupAt input C mode accounting source.rule next n =
      fun sample => joinedRecord (input.preBirthView next sample) := by
    funext sample
    exact Prod.ext rfl (hrecord sample)
  have hf : (fun sample : Seed × input.World => input.restrictFreshWorld next.val sample.2) =
      renumberFutureWorld input next.val ∘ (fun sample : Seed × input.World => unbornView input next sample.2) := by
    funext sample
    exact restrictFreshWorld_eq_renumberFutureWorld input next.val sample.2
  rw [heq, hf]
  exact (preBirthView_independent_unborn input ν next).comp hm
    (measurable_renumberFutureWorld input next.val)

theorem preBirthStartupAt_jointFreshSuffixLaw (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : Policy input C mode accounting Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (next : I.Stage) (n : ℕ) :
    (input.seededWorldLaw ν).map (fun sample =>
      (preBirthStartupAt input C mode accounting source.rule next n sample,
        input.restrictFreshWorld next.val sample.2)) =
      ((input.seededWorldLaw ν).map (preBirthStartupAt input C mode accounting source.rule next n)).prod
        (input.freshSuffix next.val).worldLaw := by
  have hind := preBirthStartupAt_independent_freshSuffix input C mode accounting source ν next n
  have hm := measurable_preBirthStartupAt input C mode accounting source.rule source.measurable_rule next n
  have hf : Measurable (fun sample : Seed × input.World => input.restrictFreshWorld next.val sample.2) :=
    (input.measurable_restrictFreshWorld next.val).comp measurable_snd
  rw [hind.map_prod_eq_prod_map_map hm.aemeasurable hf.aemeasurable, seededWorldLaw_freshSuffixWorld]

/-- Exact prebirth-gated entry-product integration. No regular conditional
kernel, positive event mass, division, finite cost or integrability is used. -/
theorem preBirthStartupAt_gate_lintegral (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : Policy input C mode accounting Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (next : I.Stage) (n : ℕ) (startup : Startup I)
    (A : Set (Seed × input.PastWorld next)) (hmA : MeasurableSet A)
    (f : (((Seed × input.PastWorld next) × Option (Startup I)) × (input.freshSuffix next.val).World) → ℝ≥0∞)
    (hmf : Measurable f) :
    (∫⁻ sample in {sample | input.preBirthView next sample ∈ A ∧
        entryStartupAt input C mode accounting source.rule next n sample = some startup},
      f (preBirthStartupAt input C mode accounting source.rule next n sample,
        input.restrictFreshWorld next.val sample.2) ∂input.seededWorldLaw ν) =
      ∫⁻ r in A ×ˢ {some startup}, ∫⁻ fresh, f (r, fresh) ∂(input.freshSuffix next.val).worldLaw
        ∂((input.seededWorldLaw ν).map (preBirthStartupAt input C mode accounting source.rule next n)) := by
  let E := {sample : Seed × input.World | input.preBirthView next sample ∈ A ∧
    entryStartupAt input C mode accounting source.rule next n sample = some startup}
  let B := A ×ˢ ({some startup} : Set (Option (Startup I)))
  let D := B ×ˢ (Set.univ : Set (input.freshSuffix next.val).World)
  let joint := fun sample : Seed × input.World =>
    (preBirthStartupAt input C mode accounting source.rule next n sample, input.restrictFreshWorld next.val sample.2)
  have hmB : MeasurableSet B := hmA.prod (measurableSet_singleton _)
  have hmD : MeasurableSet D := hmB.prod MeasurableSet.univ
  have hmjoint : Measurable joint :=
    (measurable_preBirthStartupAt input C mode accounting source.rule source.measurable_rule next n).prodMk
      ((input.measurable_restrictFreshWorld next.val).comp measurable_snd)
  have hpre : joint ⁻¹' D = E := by
    ext sample
    simp only [joint, D, B, E, preBirthStartupAt, Set.mem_preimage, Set.mem_prod,
      Set.mem_singleton_iff, Set.mem_univ, and_true, Set.mem_ofPred_eq]
  have hmap := preBirthStartupAt_jointFreshSuffixLaw input C mode accounting source ν next n
  change (∫⁻ sample in E, f (joint sample) ∂input.seededWorldLaw ν) = _
  calc
    _ = ∫⁻ pair in D, f pair ∂((input.seededWorldLaw ν).map joint) := by
      rw [setLIntegral_map hmD hmf hmjoint, hpre]
    _ = ∫⁻ pair in D, f pair ∂(((input.seededWorldLaw ν).map
        (preBirthStartupAt input C mode accounting source.rule next n)).prod (input.freshSuffix next.val).worldLaw) := by
      rw [hmap]
    _ = _ := by rw [setLIntegral_prod f hmf.aemeasurable, Measure.restrict_univ]

end PaperProofs.Retained.PRetPreBirthEntryLaw046
