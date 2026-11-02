module
public import PaperProofs.Paid.PDROC_RecordCoupling_002
public import PaperProofs.Common.NativeHeadTest
public import PaperProofs.Common.NativeHeadContinuation
public import PaperProofs.Common.FreshSuffixComposition

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native
open PaperProofs.Paid

namespace PDROC
universe u
instance localRecordOptionMeasurable : MeasurableSpace (Option AuxiliaryRecord) := ⊤
instance localRecordOptionSingleton : MeasurableSingletonClass (Option AuxiliaryRecord) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
local instance : MeasurableSpace (List (Fin 2)) := ⊤
local instance : MeasurableSingletonClass (List (Fin 2)) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
local instance : MeasurableSpace (Option Bool) := ⊤
local instance : MeasurableSingletonClass (Option Bool) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
section
variable {Seed : Type u} [MeasurableSpace Seed]

/-- The public entry cache is kept with the original private seed. All old
deferred executions are replayed by the existing controller, rather than
being mistaken for abandonment at the first non-review action. -/
noncomputable def sourceEntryReplayRule (P : Parameters) (first : P.sharedInstance.Stage)
    (accounting : NormalAccounting P.sharedInstance) (rule : PolicyRule P.sharedInstance Seed) :
    PolicyRule (P.sharedInstance.freshSuffix first.val) (Seed × Startup P.sharedInstance) :=
  fun source history => guardedReplayRule source.2.availableTools
    (replayedSuffixCandidate first.val accounting rule source.2) source.1 history

theorem measurable_sourceEntryReplayRule (P : Parameters) (first : P.sharedInstance.Stage)
    (accounting : NormalAccounting P.sharedInstance) (rule : PolicyRule P.sharedInstance Seed)
    (hm : MeasurableRule rule) : MeasurableRule (sourceEntryReplayRule P first accounting rule) := by
  apply measurable_from_prod_countable_left
  intro history
  apply measurable_from_prod_countable_left
  intro startup
  exact (measurable_guardedReplayRule (I := P.sharedInstance.freshSuffix first.val) startup.availableTools
    (replayedSuffixCandidate first.val accounting rule startup)
    (measurable_replayedSuffixCandidate first.val accounting rule hm startup)).comp
      (measurable_id.prodMk measurable_const)

/-- An actual causal local BSC test, extracted from the original policy and
its public virtual entry cache. No termination, MAP, or performance field is
supplied to its construction. -/
noncomputable def sourceEntryTest (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (first : P.sharedInstance.Stage) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule) :
    P.binarySymmetric.experiment.AdmissibleRule (Seed × Startup P.sharedInstance) := by
  have hE : ((P.input fee hfee).freshSuffix first.val).experiment (P.sharedInstance.freshHead first) =
      P.binarySymmetric.experiment := by
    rw [StatisticalInput.freshSuffix_experiment]
    exact P.experiment_eq_binarySymmetric
  exact hE ▸ nativeHeadTest ((P.input fee hfee).freshSuffix first.val) (P.sharedInstance.freshHead first)
    (sourceEntryReplayRule P first accounting rule) (measurable_sourceEntryReplayRule P first accounting rule hm)

def optionWriteBit {I : Instance} : Action I → Option Bool
  | .write _ bit => some bit
  | _ => none

/-- Decoder retains the entire finite prewrite observation word and the
original non-MAP write bit. Stop and abandon retain decision=none. -/
noncomputable def sourceEntryRecordDecoder (P : Parameters) (_fee : ℚ) (_hfee : 0 ≤ _fee)
    (first : P.sharedInstance.Stage) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed)
    (record : (Seed × Startup P.sharedInstance) × P.binarySymmetric.experiment.StoppedWord) : AuxiliaryRecord :=
  { observations := List.ofFn record.2.2
    decision := optionWriteBit (sourceEntryReplayRule P first accounting rule record.1
      (List.ofFn (fun k : Fin record.2.1 =>
        VisibleEvent.observation (P.sharedInstance.freshHead first) (record.2.2 k).val))) }

theorem measurable_sourceEntryRecordDecoder (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (first : P.sharedInstance.Stage) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule) :
    Measurable (sourceEntryRecordDecoder P fee hfee first accounting rule) := by
  have hh : Measurable (fun word : P.binarySymmetric.experiment.StoppedWord =>
      List.ofFn (fun k : Fin word.1 =>
        VisibleEvent.observation (P.sharedInstance.freshHead first) (word.2 k).val)) := measurable_of_countable _
  have ha := (measurable_sourceEntryReplayRule P first accounting rule hm).comp
    (measurable_fst.prodMk (hh.comp measurable_snd))
  have hd := (measurable_of_countable (optionWriteBit (I := P.sharedInstance.freshSuffix first.val))).comp ha
  have ho : Measurable (fun record : (Seed × Startup P.sharedInstance) × P.binarySymmetric.experiment.StoppedWord =>
      (List.ofFn record.2.2 : List (Fin 2))) := (measurable_of_countable (fun word : P.binarySymmetric.experiment.StoppedWord => (List.ofFn word.2 : List (Fin 2)))).comp measurable_snd
  exact (measurable_of_countable (fun pair : List (Fin 2) × Option Bool =>
    ({observations := pair.1, decision := pair.2} : AuxiliaryRecord))).comp (ho.prodMk hd)

/-- Genuine nonreturn is a separate outer none, not an empty record or a
zero-bill abandonment. No future truth occurs in this sampling map. -/
noncomputable def sampleSourceEntryRecord (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (first : P.sharedInstance.Stage) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule)
    (sample : (Seed × Startup P.sharedInstance) × P.binarySymmetric.experiment.Tape) : Option AuxiliaryRecord :=
  if (sourceEntryTest P fee hfee first accounting rule hm).rule.stop sample.1 sample.2 = ⊤ then none
  else some (sourceEntryRecordDecoder P fee hfee first accounting rule
    (P.binarySymmetric.experiment.stoppedTranscript (sourceEntryTest P fee hfee first accounting rule hm) sample))

theorem measurable_sampleSourceEntryRecord (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (first : P.sharedInstance.Stage) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule) :
    Measurable (sampleSourceEntryRecord P fee hfee first accounting rule hm) := by
  let htest := sourceEntryTest P fee hfee first accounting rule hm
  have hd := (measurable_sourceEntryRecordDecoder P fee hfee first accounting rule hm).comp
    (P.binarySymmetric.experiment.measurable_stoppedTranscript htest)
  have hsome := (measurable_of_countable (some : AuxiliaryRecord → Option AuxiliaryRecord)).comp hd
  have hstopset : MeasurableSet {sample : (Seed × Startup P.sharedInstance) × P.binarySymmetric.experiment.Tape |
      (sourceEntryTest P fee hfee first accounting rule hm).rule.stop sample.1 sample.2 = ⊤} :=
    (sourceEntryTest P fee hfee first accounting rule hm).measurable_stop (measurableSet_singleton (⊤ : ℕ∞))
  exact measurable_const.ite hstopset hsome

theorem sampleSourceEntryRecord_none_iff (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (first : P.sharedInstance.Stage) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule)
    (sample : (Seed × Startup P.sharedInstance) × P.binarySymmetric.experiment.Tape) :
    sampleSourceEntryRecord P fee hfee first accounting rule hm sample = none ↔
      (sourceEntryTest P fee hfee first accounting rule hm).rule.stop sample.1 sample.2 = ⊤ := by
  unfold sampleSourceEntryRecord
  split_ifs <;> simp_all

/-- Finite stopping is derived from the actual local observation charge;
it is never required when defining the source policy's record sampler. -/
theorem sampleSourceEntryRecord_finite_of_charge (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (first : P.sharedInstance.Stage) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule)
    (ν : Measure (Seed × Startup P.sharedInstance)) [IsProbabilityMeasure ν]
    (hfinite : P.binarySymmetric.experiment.bayesObservationCharge ν
      (sourceEntryTest P fee hfee first accounting rule hm) ≠ ⊤) (truth : Bool) :
    ∀ᵐ sample ∂P.binarySymmetric.experiment.conditionalLaw ν truth,
      sampleSourceEntryRecord P fee hfee first accounting rule hm sample ≠ none := by
  have hf : P.binarySymmetric.experiment.bayesObjective ν
      (sourceEntryTest P fee hfee first accounting rule hm) 0 ≠ ⊤ := by
    simpa only [PaperProofs.Statistics.BinaryExperiment.bayesObjective, zero_mul, add_zero] using hfinite
  have hstop := P.binarySymmetric.experiment.expectedSamples_finite_stop ν
    (sourceEntryTest P fee hfee first accounting rule hm) truth
    (P.binarySymmetric.experiment.bayesObjective_finite_expectedSamples ν _ 0 hf truth)
  filter_upwards [hstop] with sample hs
  intro hnone
  exact hs ((sampleSourceEntryRecord_none_iff P fee hfee first accounting rule hm sample).mp hnone)

end
end PDROC



