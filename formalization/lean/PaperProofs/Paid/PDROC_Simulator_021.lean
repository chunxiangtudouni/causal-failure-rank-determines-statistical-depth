module

public import PaperProofs.Paid.PDROC_Simulator_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

def simulatorReportStage : VisibleEvent I → Option I.Stage
  | .report stage _ _ => some stage
  | _ => none

def simulatorReportStages (history : List (VisibleEvent I)) : List I.Stage :=
  history.filterMap simulatorReportStage

theorem simulatorReportStages_append (before after : List (VisibleEvent I)) :
    simulatorReportStages (before ++ after) = simulatorReportStages before ++ simulatorReportStages after :=
  List.filterMap_append

theorem simulatorReportStages_reviews (stage : I.Stage) (record : AuxiliaryRecord) :
    simulatorReportStages (simulatorReviewPacket stage record) = [] := by
  simp [simulatorReportStages, simulatorReviewPacket, List.filterMap_map, simulatorReportStage, Function.comp_def]

theorem historyReport_none_iff_reportStage_not_mem (history : List (VisibleEvent I)) (stage : I.Stage) :
    historyReport history stage = none ↔ stage ∉ simulatorReportStages history := by
  constructor
  · intro hn hm
    have hnil : history.filterMap (eventReport stage) = [] := List.getLast?_eq_none_iff.mp hn
    have hno := List.filterMap_eq_nil_iff.mp hnil
    obtain ⟨event, he, hs⟩ := List.mem_filterMap.mp hm
    cases event with
    | report other truth serial =>
      have hstage : other = stage := Option.some.inj hs
      subst other
      have hbad := hno (.report stage truth serial) he
      simp only [eventReport, ↓reduceIte, reduceCtorEq] at hbad
    | observation | wrote | committed | executed | advanced | stopped | abandoned => cases hs
  · intro hn
    apply List.getLast?_eq_none_iff.mpr
    apply List.filterMap_eq_nil_iff.mpr
    intro event he
    cases event with
    | report other truth serial =>
      have hne : other ≠ stage := by
        intro h
        subst other
        exact hn (List.mem_filterMap.mpr ⟨.report stage truth serial, he, rfl⟩)
      simp only [eventReport, hne, ↓reduceIte]
    | observation | wrote | committed | executed | advanced | stopped | abandoned => rfl

universe u
variable {SimSeed : Type u}

theorem simulatorStep_reportStages (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (cache : SimulatorCache I) (event : VisibleEvent I) :
    simulatorReportStages (simulatorStep draw seed cache event).shadow =
      simulatorReportStages cache.shadow ++ simulatorReportStages [event] := by
  cases event <;> simp only [simulatorStep, simulatorAppend]
  all_goals (try split_ifs)
  all_goals simp only [simulatorReportStages_append, simulatorReportStages_reviews]
  all_goals rfl

theorem simulatorReplay_reportStages (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (history : List (VisibleEvent I)) :
    simulatorReportStages (simulatorReplay draw seed history).shadow = simulatorReportStages history := by
  have hfold (history : List (VisibleEvent I)) (cache : SimulatorCache I) :
      simulatorReportStages (history.foldl (simulatorStep draw seed) cache).shadow =
        simulatorReportStages cache.shadow ++ simulatorReportStages history := by
    induction history generalizing cache with
    | nil => simp only [List.foldl_nil, simulatorReportStages, List.filterMap_nil, List.append_nil]
    | cons event rest ih =>
      simp only [List.foldl_cons, ih, simulatorStep_reportStages, List.append_assoc]
      exact congrArg (List.append (simulatorReportStages cache.shadow))
        (simulatorReportStages_append [event] rest).symm
  exact hfold history (simulatorInitialCache I)

theorem simulatorReplay_report_none (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (stage : I.Stage)
    (hn : historyReport history stage = none) :
    historyReport (simulatorReplay draw seed history).shadow stage = none := by
  apply (historyReport_none_iff_reportStage_not_mem _ stage).mpr
  rw [simulatorReplay_reportStages]
  exact (historyReport_none_iff_reportStage_not_mem history stage).mp hn

end PDROC
