module

public import PaperProofs.Retained.PRet_RiskMassFlow_Events_008

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics MeasureTheory
open scoped ENNReal

namespace PRetRiskMassFlow

variable {I : Instance}

theorem writeError_on_entry_subset (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2)
    (stage : I.Stage) (history : List (VisibleEvent I)) (p : ℚ)
    (target : entryTarget I budget stage history = some p) :
    writeError input C accounting budget stage ∩ entryEvent input C accounting budget stage history ⊆
      (fun sample : Unit × input.World =>
        (entrySeedHistory input C .uncapped accounting (retainedRule input budget none) stage sample,sample.2 stage)) ⁻¹'
        ({((),some history)} ×ˢ fixedPosteriorError input stage p) := by
  rintro ⟨⟨⟩,world⟩ ⟨⟨n,written⟩,entered⟩
  have legal := retainedRule_uncapped_legal input C hretained accounting budget none
  obtain ⟨_,_,path⟩ := run_has_prefix input C .uncapped accounting (retainedRule input budget none) legal ((),world) n
  obtain ⟨m,old,_earlier,oldPath,active,selected⟩ := prefix_written_has_write input C .uncapped accounting
    (retainedRule input budget none) () (input.truthAt world) (worldTapes input world) path stage _ written
  have realization := prefix_posteriorWrite_realization input C hretained accounting budget positive small
    ((),world) oldPath active stage _ selected history p entered target
  refine ⟨?_,?_⟩
  · change ((),entryHistory input C .uncapped accounting (retainedRule input budget none) stage ((),world)) ∈ {((),some history)}
    change entryHistory input C .uncapped accounting (retainedRule input budget none) stage ((),world) = some history at entered
    rw [entered]
    exact Set.mem_singleton _
  · change ((input.experiment stage).posteriorSPRT p).rule.decision () (world stage).2 ≠ (world stage).1
    rw [← realization.2]
    have truth := congrFun (run_truth input C .uncapped accounting (retainedRule input budget none) legal ((),world) n) stage
    rw [truth]
    exact Bool.not_ne_self _

theorem writeError_on_entry_le (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2)
    (stage : I.Stage) (history : List (VisibleEvent I)) (p : ℚ)
    (target : entryTarget I budget stage history = some p) :
    input.seededWorldLaw (Measure.dirac ())
      (writeError input C accounting budget stage ∩ entryEvent input C accounting budget stage history) ≤
      ENNReal.ofReal (p : ℝ) * input.seededWorldLaw (Measure.dirac ()) (entryEvent input C accounting budget stage history) := by
  let policy := idealPolicy input C hretained accounting budget
  let μ := input.seededWorldLaw (Measure.dirac ())
  let record := entrySeedHistory input C .uncapped accounting policy.rule stage
  let joint := fun sample : Unit × input.World => (record sample,sample.2 stage)
  let rectangle : Set ((Unit × EntryHistory I) × input.StageSample stage) :=
    {((),some history)} ×ˢ fixedPosteriorError input stage p
  have hrecord : Measurable record := measurable_entrySeedHistory input C .uncapped accounting policy.rule policy.measurable_rule stage
  have hjoint : Measurable joint := hrecord.prodMk ((measurable_pi_apply stage).comp measurable_snd)
  have hrectangle : MeasurableSet rectangle := (measurableSet_singleton _).prod (measurableSet_fixedPosteriorError input stage p)
  have subset : writeError input C accounting budget stage ∩ entryEvent input C accounting budget stage history ⊆
      joint ⁻¹' rectangle := writeError_on_entry_subset input C hretained accounting budget positive small stage history p target
  have mass : (μ.map record) {((),some history)} = μ (entryEvent input C accounting budget stage history) := by
    rw [Measure.map_apply hrecord (measurableSet_singleton _)]
    congr 1
    ext sample
    change (sample.1,entryHistory input C .uncapped accounting policy.rule stage sample) = ((),some history) ↔ _
    cases sample.1
    simp only [Prod.mk.injEq,true_and,entryEvent,Set.mem_ofPred_eq]
    rfl
  have valid := entryTarget_valid budget stage history p target
  calc
    μ (writeError input C accounting budget stage ∩ entryEvent input C accounting budget stage history)
        ≤ μ (joint ⁻¹' rectangle) := measure_mono subset
    _ = (μ.map joint) rectangle := (Measure.map_apply hjoint hrectangle).symm
    _ = ((μ.map record).prod (input.stageLaw stage)) rectangle := by
      rw [entrySeedHistory_jointLaw input C .uncapped accounting policy (Measure.dirac ()) stage]
    _ = (μ.map record) {((),some history)} * input.stageLaw stage (fixedPosteriorError input stage p) := Measure.prod_prod _ _
    _ ≤ (μ.map record) {((),some history)} * ENNReal.ofReal (p : ℝ) :=
      mul_le_mul_right (stageLaw_fixedPosteriorError_le input stage p valid.1 valid.2) _
    _ = ENNReal.ofReal (p : ℝ) * μ (entryEvent input C accounting budget stage history) := by rw [mass,mul_comm]

theorem fatal_entry_empty (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (budget : ℚ) (stage : I.Stage) (history : List (VisibleEvent I))
    (notFatal : entryKind I budget stage history ≠ some .noTool) :
    fatal input C accounting budget stage ∩ entryEvent input C accounting budget stage history = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro sample ⟨failed,entered⟩
  have kind := failed.2
  change (entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample).bind
    (entryKind I budget stage) = some .noTool at kind
  change entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample = some history at entered
  rw [entered] at kind
  exact notFatal kind

end PRetRiskMassFlow
