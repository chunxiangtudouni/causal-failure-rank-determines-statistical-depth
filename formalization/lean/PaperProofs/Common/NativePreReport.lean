module

public import PaperProofs.Common.NativeHorizon

/-!
An actual finite pre-report record for native returned-action histories.
The original quotas imply the logical action horizon; this does not require
private host computation to return. Event-level truncation keeps the final
ordinary write in a late response packet and removes its first truth report
and all later repair/abandonment outcomes. Only the original private seed and
this public prefix enter the record, never a State containing hidden truth.
-/

@[expose] public section

open MeasureTheory

namespace PaperProofs.Common.Native

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

def beforeTruthReport : VisibleEvent I → Bool
  | .report _ _ _ => false
  | _ => true

noncomputable def preReportPublicHistory (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (sample : Seed × input.World) :
    List (VisibleEvent I) :=
  (run input C .native accounting rule sample (nativeActionBound C + 1)).history.takeWhile beforeTruthReport

noncomputable def preReportRecord (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (sample : Seed × input.World) :
    Seed × List (VisibleEvent I) :=
  (sample.1, preReportPublicHistory input C accounting rule sample)

theorem measurable_preReportPublicHistory (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hm : MeasurableRule rule) :
    Measurable (preReportPublicHistory input C accounting rule) :=
  (measurable_of_countable (fun state : State I => state.history.takeWhile beforeTruthReport)).comp
    (measurable_run input C .native accounting rule hm (nativeActionBound C + 1))

theorem measurable_preReportRecord (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hm : MeasurableRule rule) :
    Measurable (preReportRecord input C accounting rule) :=
  measurable_fst.prodMk (measurable_preReportPublicHistory input C accounting rule hm)

noncomputable def preReportLaw (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (ν : Measure Seed) :
    Measure (Seed × List (VisibleEvent I)) :=
  (input.seededWorldLaw ν).map (preReportRecord input C accounting rule)

end PaperProofs.Common.Native
