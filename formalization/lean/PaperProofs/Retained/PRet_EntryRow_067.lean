module

public import PaperProofs.Retained.PRet_PreBirthEntryLaw_046
public import PaperProofs.Retained.PRet_EntryPenalty_066

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetEntryRow067

open Common Common.Native MeasureTheory PRetPreBirthEntryLaw046 PRetFreshCharge065 PRetEntryPenalty066
open scoped ENNReal

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

/-- The exact full-prebirth row inequality for an actual fixed-clock entry
snapshot. It retains the entire old H and all tools, without a conditional
kernel, positive gate mass, or finite-bill assumption. -/
theorem entry_row_lower (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : Policy input C mode accounting Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (stage : I.Stage) (n : ℕ) (startup : Startup I) (old : Finset I.Stage)
    (A : Set (Seed × input.PastWorld stage)) (hmA : MeasurableSet A)
    (hold : ∀ sample, input.preBirthView stage sample ∈ A →
      entryStartupAt input C mode accounting source.rule stage n sample = some startup →
        reportedErrors I (run input C mode accounting source.rule sample n).history stage.val = old)
    (penalty : ℝ≥0∞) :
    input.seededWorldLaw ν {sample | input.preBirthView stage sample ∈ A ∧
      entryStartupAt input C mode accounting source.rule stage n sample = some startup} * freshPenalty input stage.val old penalty ≤
      ∫⁻ sample in {sample | input.preBirthView stage sample ∈ A ∧
        entryStartupAt input C mode accounting source.rule stage n sample = some startup},
        fullCharge input C mode accounting source.rule stage.val penalty sample ∂input.seededWorldLaw ν := by
  let μ := input.seededWorldLaw ν
  let record := preBirthStartupAt input C mode accounting source.rule stage n
  let η := μ.map record
  let E := {sample : Seed × input.World | input.preBirthView stage sample ∈ A ∧
    entryStartupAt input C mode accounting source.rule stage n sample = some startup}
  let B := A ×ˢ ({some startup} : Set (Option (Startup I)))
  let targetRule := PRetFreshExtractionPolicy047.rule stage.val accounting source.rule startup
  let F := fun pair : (((Seed × input.PastWorld stage) × Option (Startup I)) × (input.freshSuffix stage.val).World) =>
    freshCharge input stage.val old targetRule penalty (pair.1.1.1, pair.2)
  have hmRecord : Measurable record := measurable_preBirthStartupAt input C mode accounting source.rule source.measurable_rule stage n
  have hmB : MeasurableSet B := hmA.prod (measurableSet_singleton _)
  have hmE : MeasurableSet E := ((input.measurable_preBirthView stage) hmA).inter
    ((measurable_entryStartupAt input C mode accounting source.rule source.measurable_rule stage n) (measurableSet_singleton _))
  have hpre : record ⁻¹' B = E := by
    ext sample
    rfl
  have hmass : η B = μ E := by rw [Measure.map_apply hmRecord hmB, hpre]
  have hmF : Measurable F := (measurable_freshCharge input stage.val old targetRule
    (PRetFreshExtractionPolicy047.measurable_rule stage.val accounting source.rule source.measurable_rule startup) penalty).comp
      ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
  have hrow (r : (Seed × input.PastWorld stage) × Option (Startup I)) :
      freshPenalty input stage.val old penalty ≤ ∫⁻ fresh, F (r, fresh) ∂(input.freshSuffix stage.val).worldLaw :=
    freshPenalty_le_extraction_dirac input stage.val old accounting source.rule source.measurable_rule startup r.1.1 penalty
  change μ E * freshPenalty input stage.val old penalty ≤ _
  calc
    _ = freshPenalty input stage.val old penalty * η B := by rw [hmass, mul_comm]
    _ = ∫⁻ _r in B, freshPenalty input stage.val old penalty ∂η := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ r in B, ∫⁻ fresh, F (r, fresh) ∂(input.freshSuffix stage.val).worldLaw ∂η := lintegral_mono hrow
    _ = ∫⁻ sample in E, F (record sample, input.restrictFreshWorld stage.val sample.2) ∂μ :=
      (preBirthStartupAt_gate_lintegral input C mode accounting source ν stage n startup A hmA F hmF).symm
    _ ≤ ∫⁻ sample in E, fullCharge input C mode accounting source.rule stage.val penalty sample ∂μ := by
      apply setLIntegral_mono' hmE
      intro sample hs
      obtain ⟨hentry, hstartup⟩ := (entryStartupAt_some_iff input C mode accounting source.rule stage n sample startup).mp hs.2
      have h := extraction_charge_le input C hearly mode accounting source.rule source.measurable_rule source.legal sample
        stage.val n hentry old (hold sample hs.1 hs.2) penalty
      rw [hstartup] at h
      exact h

end PaperProofs.Retained.PRetEntryRow067
