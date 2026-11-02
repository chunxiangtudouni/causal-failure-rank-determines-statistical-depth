module

public import PaperProofs.Retained.PRet_JointExtraction_076
public import PaperProofs.Retained.PRet_PreBirthEntryLaw_046
public import PaperProofs.Retained.PRet_ActualReportedErrors_048

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetNestedEntryRow081

open Common Common.Native MeasureTheory PRetPreBirthEntryLaw046 PRetActualReportedErrors048
open PRetAmbientComparator073 PRetJointCharges075 PRetJointExtraction076
open scoped ENNReal

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

/-- Exact fresh-to-fresh continuation lower row. The scalar is the
ORIGINAL ambient freshPenalty; the source is an arbitrary ACTUAL full fresh
Policy with old H in its joint success predicate. Source native success and
an old fixed matching are unnecessary. Public old-H inclusion is discharged
by its actual early reported-errors interpretation. -/
theorem nested_entry_row_lower (input : StatisticalInput I) (first : ℕ)
    (base old : Finset I.Stage)
    (source : Policy (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : (I.freshSuffix first).Stage)
    (n : ℕ) (startup : Startup (I.freshSuffix first))
    (hOld : old ⊆ base ∪ (reportedErrors (I.freshSuffix first) startup.history stage.val).image (I.freshStageLift first))
    (A : Set (Seed × (input.freshSuffix first).PastWorld stage)) (hmA : MeasurableSet A) (penalty : ℝ≥0∞) :
    (input.freshSuffix first).seededWorldLaw ν {sample |
      (input.freshSuffix first).preBirthView stage sample ∈ A ∧
      entryStartupAt (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
        (zeroNormalAccounting (I.freshSuffix first)) source.rule stage n sample = some startup} *
      freshPenalty input (first + stage.val) old penalty ≤
    ∫⁻ sample in {sample | (input.freshSuffix first).preBirthView stage sample ∈ A ∧
      entryStartupAt (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
        (zeroNormalAccounting (I.freshSuffix first)) source.rule stage n sample = some startup},
      futureJointCharge (input.freshSuffix first) (I.freshStageLift first) base source.rule stage.val penalty sample
        ∂(input.freshSuffix first).seededWorldLaw ν := by
  let J := I.freshSuffix first
  let localInput := input.freshSuffix first
  let μ := localInput.seededWorldLaw ν
  let record := preBirthStartupAt localInput (freshContract J) .uncapped (zeroNormalAccounting J) source.rule stage n
  let η := μ.map record
  let E := {sample : Seed × localInput.World | localInput.preBirthView stage sample ∈ A ∧
    entryStartupAt localInput (freshContract J) .uncapped (zeroNormalAccounting J) source.rule stage n sample = some startup}
  let B := A ×ˢ ({some startup} : Set (Option (Startup J)))
  let targetRule := PRetFreshExtractionPolicy047.rule stage.val (zeroNormalAccounting J) source.rule startup
  let embed := fun child => I.freshStageLift first (J.freshStageLift stage.val child)
  let F := fun pair : (((Seed × localInput.PastWorld stage) × Option (Startup J)) × (localInput.freshSuffix stage.val).World) =>
    jointCharge (localInput.freshSuffix stage.val) embed old targetRule penalty (pair.1.1.1, pair.2)
  have hmRecord : Measurable record := measurable_preBirthStartupAt localInput (freshContract J) .uncapped
    (zeroNormalAccounting J) source.rule source.measurable_rule stage n
  have hmB : MeasurableSet B := hmA.prod (measurableSet_singleton _)
  have hmE : MeasurableSet E := ((localInput.measurable_preBirthView stage) hmA).inter
    ((measurable_entryStartupAt localInput (freshContract J) .uncapped (zeroNormalAccounting J)
      source.rule source.measurable_rule stage n) (measurableSet_singleton _))
  have hpre : record ⁻¹' B = E := by ext sample; rfl
  have hmass : η B = μ E := by rw [Measure.map_apply hmRecord hmB, hpre]
  have hmF : Measurable F := (measurable_jointCharge (localInput.freshSuffix stage.val) embed old targetRule
    (PRetFreshExtractionPolicy047.measurable_rule stage.val (zeroNormalAccounting J) source.rule source.measurable_rule startup) penalty).comp
      ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
  have hrow (r : (Seed × localInput.PastWorld stage) × Option (Startup J)) :
      freshPenalty input (first + stage.val) old penalty ≤ ∫⁻ world, F (r, world) ∂(localInput.freshSuffix stage.val).worldLaw :=
    freshPenalty_le_nested_extraction_dirac input first stage.val old (zeroNormalAccounting J) source.rule
      source.measurable_rule startup r.1.1 penalty
  change μ E * freshPenalty input (first + stage.val) old penalty ≤ _
  calc
    _ = freshPenalty input (first + stage.val) old penalty * η B := by rw [hmass, mul_comm]
    _ = ∫⁻ _r in B, freshPenalty input (first + stage.val) old penalty ∂η := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ r in B, ∫⁻ world, F (r, world) ∂(localInput.freshSuffix stage.val).worldLaw ∂η := lintegral_mono hrow
    _ = ∫⁻ sample in E, F (record sample, localInput.restrictFreshWorld stage.val sample.2) ∂μ :=
      (preBirthStartupAt_gate_lintegral localInput (freshContract J) .uncapped (zeroNormalAccounting J)
        source ν stage n startup A hmA F hmF).symm
    _ ≤ ∫⁻ sample in E, futureJointCharge localInput (I.freshStageLift first) base source.rule stage.val penalty sample ∂μ := by
      apply setLIntegral_mono' hmE
      intro sample hs
      obtain ⟨hentry, hstartup⟩ := (entryStartupAt_some_iff localInput (freshContract J) .uncapped
        (zeroNormalAccounting J) source.rule stage n sample startup).mp hs.2
      obtain ⟨_, _, hp⟩ := run_has_prefix localInput (freshContract J) .uncapped (zeroNormalAccounting J) source.rule source.legal sample n
      have herr := prefix_reportedErrors localInput (freshContract J) rfl .uncapped (zeroNormalAccounting J)
        source.rule sample.1 _ _ hp stage.val
      change reportedErrors J (publicStartup (run localInput (freshContract J) .uncapped (zeroNormalAccounting J)
        source.rule sample n)).history stage.val = _ at herr
      rw [hstartup] at herr
      have herrors : reportedErrors J startup.history stage.val ⊆
          ordinaryMismatches (run localInput (freshContract J) .uncapped (zeroNormalAccounting J) source.rule sample n).ledger := by
        rw [herr]
        exact Finset.inter_subset_left
      have hold := hOld.trans (Finset.union_subset_union_right (Finset.image_subset_image herrors))
      have h := jointCharge_le_future localInput source sample stage.val n hentry (I.freshStageLift first) base old hold penalty
      rw [hstartup] at h
      exact h

end PaperProofs.Retained.PRetNestedEntryRow081
