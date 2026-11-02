module

public import PaperProofs.Paid.PDROC_OverlaySimulator_002
public import PaperProofs.Paid.PDROC_SimulatorProjection_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {I : Instance} {SimSeed : Type u}

/-- Replacing one mark row cannot affect an event that is not its real report.
The draw and ghost assumptions will be discharged from the unchanged auxiliary
tapes and old seed, respectively. -/
theorem overlayStep_eq_off_target
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seedA seedB : SimSeed) (target : I.Stage) (cache : SimulatorCache I) (event : VisibleEvent I)
    (hdraw : ∀ stage entry, draw seedA stage entry = draw seedB stage entry)
    (hmark : ∀ stage, stage ≠ target → ∀ record, mark seedA stage record = mark seedB stage record)
    (hghost : ∀ cache, ghost seedA cache = ghost seedB cache)
    (hreport : eventReport target event = none) :
    overlayStep draw mark ghost seedA cache event = overlayStep draw mark ghost seedB cache event := by
  cases event with
  | report stage truth serial =>
    have hne : stage ≠ target := by
      intro h
      subst stage
      simp [eventReport] at hreport
    simp only [overlayStep, hmark stage hne]
  | observation | wrote | committed | executed | advanced | stopped | abandoned =>
    simp only [overlayStep, simulatorStep, hdraw, hghost]

/-- Full replay invariance before the target's first real report, including
all historical auxiliary words, ghost calls, chosen records, and serials. -/
theorem overlayReplay_eq_off_target
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seedA seedB : SimSeed) (target : I.Stage) (history : List (VisibleEvent I))
    (hdraw : ∀ stage entry, draw seedA stage entry = draw seedB stage entry)
    (hmark : ∀ stage, stage ≠ target → ∀ record, mark seedA stage record = mark seedB stage record)
    (hghost : ∀ cache, ghost seedA cache = ghost seedB cache)
    (hreport : historyReport history target = none) :
    overlayReplay draw mark ghost seedA history = overlayReplay draw mark ghost seedB history := by
  have hfold (events : List (VisibleEvent I)) (cache : SimulatorCache I)
      (hn : events.filterMap (eventReport target) = []) :
      events.foldl (overlayStep draw mark ghost seedA) cache =
        events.foldl (overlayStep draw mark ghost seedB) cache := by
    induction events generalizing cache with
    | nil => rfl
    | cons event rest ih =>
      have he : eventReport target event = none :=
        List.filterMap_eq_nil_iff.mp hn event (by simp)
      have hr : rest.filterMap (eventReport target) = [] := by
        apply List.filterMap_eq_nil_iff.mpr
        intro e hm
        exact List.filterMap_eq_nil_iff.mp hn e (by simp [hm])
      simp only [List.foldl_cons]
      rw [overlayStep_eq_off_target draw mark ghost seedA seedB target cache event hdraw hmark hghost he]
      exact ih _ hr
  exact hfold history (simulatorInitialCache I) (List.getLast?_eq_none_iff.mp hreport)

theorem overlay_historyReport_none_append (before after : List (VisibleEvent I)) (target : I.Stage) :
    historyReport (before ++ after) target = none ↔
      historyReport before target = none ∧ historyReport after target = none := by
  simp [historyReport, List.filterMap_append, and_comm]

/-- Before the current stage has been written, its auxiliary tape has not
been queried either. Actual prefix invariants discharge all three absences. -/
theorem overlayStep_eq_before_target
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seedA seedB : SimSeed) (target : I.Stage) (cache : SimulatorCache I) (event : VisibleEvent I)
    (hdraw : ∀ stage, stage ≠ target → ∀ entry, draw seedA stage entry = draw seedB stage entry)
    (hmark : ∀ stage, stage ≠ target → ∀ record, mark seedA stage record = mark seedB stage record)
    (hghost : ∀ cache, ghost seedA cache = ghost seedB cache)
    (hwrite : historyWritten [event] target = none)
    (hreport : eventReport target event = none) (hhalt : historyHalted [event] = false) :
    overlayStep draw mark ghost seedA cache event = overlayStep draw mark ghost seedB cache event := by
  cases event with
  | wrote stage bit serial =>
    have hne : stage ≠ target := by
      intro h
      subst stage
      simp [historyWritten, historyWrite, eventWrite] at hwrite
    simp only [overlayStep, simulatorStep, hdraw stage hne cache.shadow]
  | report stage truth serial =>
    have hne : stage ≠ target := by
      intro h
      subst stage
      simp [eventReport] at hreport
    simp only [overlayStep, hmark stage hne]
  | stopped => simp [historyHalted, historyActions, eventAction] at hhalt
  | abandoned => simp [historyHalted, historyActions, eventAction] at hhalt
  | advanced => simp only [overlayStep, hghost]
  | observation | committed | executed => rfl

/-- Complete before-birth replay invariance when both current auxiliary tape
and current mark row vary. No source-law or finite-cost premise is used. -/
theorem overlayReplay_eq_before_target
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seedA seedB : SimSeed) (target : I.Stage) (history : List (VisibleEvent I))
    (hdraw : ∀ stage, stage ≠ target → ∀ entry, draw seedA stage entry = draw seedB stage entry)
    (hmark : ∀ stage, stage ≠ target → ∀ record, mark seedA stage record = mark seedB stage record)
    (hghost : ∀ cache, ghost seedA cache = ghost seedB cache)
    (hwrite : historyWritten history target = none)
    (hreport : historyReport history target = none) (hhalt : historyHalted history = false) :
    overlayReplay draw mark ghost seedA history = overlayReplay draw mark ghost seedB history := by
  induction history using List.reverseRecOn with
  | nil => rfl
  | @append_singleton history event ih =>
    have hw := (historyWritten_none_append history [event] target).mp hwrite
    have hr := (overlay_historyReport_none_append history [event] target).mp hreport
    have hh : historyHalted history = false ∧ historyHalted [event] = false := by
      simpa only [historyHalted_append, Bool.or_eq_false_eq_eq_false_and_eq_false] using hhalt
    have hi := ih hw.1 hr.1 hh.1
    have hre : eventReport target event = none := by
      have hn : [event].filterMap (eventReport target) = [] := List.getLast?_eq_none_iff.mp hr.2
      exact List.filterMap_eq_nil_iff.mp hn event (by simp)
    simp only [overlayReplay, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change overlayStep draw mark ghost seedA (overlayReplay draw mark ghost seedA history) event =
      overlayStep draw mark ghost seedB (overlayReplay draw mark ghost seedB history) event
    rw [hi]
    exact overlayStep_eq_before_target draw mark ghost seedA seedB target _ event hdraw hmark hghost hw.2 hre hh.2

end PDROC
