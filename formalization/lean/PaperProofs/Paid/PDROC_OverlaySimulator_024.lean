module

public import PaperProofs.Paid.PDROC_OverlaySimulator_005
public import PaperProofs.Paid.PDROC_OverlaySimulator_021
public import PaperProofs.Paid.PDROC_SimulatorProjection_003
public import PaperProofs.Common.NativeHeadContinuation

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

theorem overlayGhostEvents_filterMap_nil {α : Type*} (f : VisibleEvent I → Option α)
    (hc : ∀ handle tool, f (.committed handle tool) = none)
    (he : ∀ handle tool, f (.executed handle tool) = none)
    (calls : List (OverlayGhostCall I)) : (overlayGhostEvents calls).filterMap f = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro event hm
  obtain ⟨call, _, rfl⟩ := List.mem_map.mp hm
  rcases call with ⟨reserve, handle, tool⟩
  cases reserve
  · exact he handle tool
  · exact hc handle tool

theorem overlayGhostEvents_no_observation (calls : List (OverlayGhostCall I)) (stage : I.Stage) :
    (overlayGhostEvents calls).filterMap (eventObservation stage) = [] :=
  overlayGhostEvents_filterMap_nil _ (fun _ _ => rfl) (fun _ _ => rfl) calls

theorem overlayGhostEvents_no_write (calls : List (OverlayGhostCall I)) (stage : I.Stage) :
    (overlayGhostEvents calls).filterMap (eventWrite stage) = [] :=
  overlayGhostEvents_filterMap_nil _ (fun _ _ => rfl) (fun _ _ => rfl) calls


def overlayPortView (history : List (VisibleEvent I)) (stage : I.Stage) : List ℕ × Option Bool :=
  (historyObservations history stage, historyWritten history stage)

theorem overlayStep_written_port_frame {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (cache : SimulatorCache I) (event : VisibleEvent I) (stage : I.Stage)
    (hw : historyWritten cache.seen stage ≠ none) (he : eventWrite stage event = none) :
    overlayPortView (overlayStep draw mark ghost seed cache event).shadow stage =
      overlayPortView cache.shadow stage := by
  cases event with
  | observation | report | committed | executed | advanced =>
    simp [overlayPortView, overlayStep, simulatorStep, simulatorAppend, historyObservations, historyWritten,
      historyWrite, List.filterMap_append, overlayGhostEvents_no_observation, overlayGhostEvents_no_write, eventObservation, eventWrite]
  | wrote current bit serial =>
    have hne : current ≠ stage := by intro h; subst current; simp [eventWrite] at he
    simp [overlayPortView, overlayStep, simulatorStep, simulatorAppend, simulatorReviewPacket,
      historyObservations, historyWritten, historyWrite, List.filterMap_append,
      List.filterMap_map, Function.comp_def, eventObservation, eventWrite, hne]
  | stopped | abandoned =>
    dsimp only [overlayStep, simulatorStep]
    split_ifs with hc hn
    · have hne : (⟨historyCursor cache.seen, hc⟩ : I.Stage) ≠ stage := by
        intro h
        exact hw (h ▸ hn)
      simp [overlayPortView, simulatorAppend, simulatorReviewPacket, historyObservations,
        historyWritten, historyWrite, List.filterMap_append, overlayGhostEvents_no_observation, overlayGhostEvents_no_write, List.filterMap_map,
        Function.comp_def, eventObservation, eventWrite, hne]
    all_goals simp [overlayPortView, simulatorAppend, historyObservations, historyWritten,
      historyWrite, List.filterMap_append, overlayGhostEvents_no_observation, overlayGhostEvents_no_write, eventObservation, eventWrite]

theorem step_overlay_written_port_frame (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {SourceSeed SimSeed : Type*} (rule : PolicyRule I SourceSeed) (sourceSeed : SourceSeed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s next : State I}
    (hp : Prefix input C mode accounting rule sourceSeed truth tapes n s) {action : Action I}
    (hs : Step input C mode accounting tapes s action next)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (stage : I.Stage) (hw : s.ledger.written stage ≠ none) :
    overlayPortView (overlayReplay draw mark ghost seed next.history).shadow stage =
      overlayPortView (overlayReplay draw mark ghost seed s.history).shadow stage := by
  have hwh : historyWritten (overlayReplay draw mark ghost seed s.history).seen stage ≠ none := by
    rw [overlayReplay_seen, prefix_historyWritten input C mode accounting rule sourceSeed truth tapes hp]
    exact hw
  have hone (event : VisibleEvent I) (he : eventWrite stage event = none) :=
    overlayStep_written_port_frame draw mark ghost seed (overlayReplay draw mark ghost seed s.history) event stage hwh he
  cases hs with
  | write current bit live port resources =>
    have hne : current ≠ stage := by intro h; subst current; exact hw port
    have hfirst := hone (.wrote current bit s.clock) (by simp [eventWrite, hne])
    have hstill : historyWritten (overlayStep draw mark ghost seed (overlayReplay draw mark ghost seed s.history)
        (.wrote current bit s.clock)).seen stage ≠ none := by
      rw [overlayStep_seen, overlayReplay_seen]
      simpa [historyWritten, historyWrite, List.filterMap_append, overlayGhostEvents_no_observation, overlayGhostEvents_no_write, eventWrite, hne, overlayReplay_seen] using hwh
    have hsecond := overlayStep_written_port_frame draw mark ghost seed
      (overlayStep draw mark ghost seed (overlayReplay draw mark ghost seed s.history) (.wrote current bit s.clock))
      (.report current (s.ledger.truth current) s.clock) stage hstill rfl
    simpa only [record, writeResponses, hearly, ↓reduceIte, writeLedger,
      List.singleton_append, List.append_assoc, overlayReplay, List.foldl_append, List.foldl_cons, List.foldl_nil] using hsecond.trans hfirst
  | review current live port resources =>
    simpa only [record, overlayReplay_append_event] using hone (.observation current (tapes current (s.ledger.reviews current).toNat).val) rfl
  | allocate handle tool active valid compatible unused unallocated window resources =>
    simpa only [record, overlayReplay_append_event] using hone (.committed handle tool) rfl
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    simpa only [record, overlayReplay_append_event] using hone (.executed handle tool) rfl
  | advance current live written resources =>
    simpa only [record, overlayReplay_append_event] using hone (.advanced current) rfl
  | stop active =>
    simpa only [stopState, Bool.false_eq_true, ↓reduceIte, overlayReplay_append_event] using hone .stopped rfl
  | abandon active =>
    simpa only [stopState, ↓reduceIte, overlayReplay_append_event] using hone .abandoned rfl

theorem run_overlay_written_port_frame (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {SourceSeed SimSeed : Type*} (rule : PolicyRule I SourceSeed)
    (hl : LegalRule input C mode accounting rule) (sample : SourceSeed × input.World)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (start extra : ℕ) (stage : I.Stage) (bit : Bool)
    (hw : (run input C mode accounting rule sample start).ledger.written stage = some bit) :
    overlayPortView (overlayReplay draw mark ghost seed (run input C mode accounting rule sample (start + extra)).history).shadow stage =
      overlayPortView (overlayReplay draw mark ghost seed (run input C mode accounting rule sample start).history).shadow stage := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
    by_cases hh : (run input C mode accounting rule sample (start + extra)).halted = true
    · rw [Nat.add_succ, run_succ_of_halted input C mode accounting rule sample (start + extra) hh]
      exact ih
    · have ha := Bool.eq_false_iff.mpr hh
      obtain ⟨k, _, hp⟩ := run_has_prefix input C mode accounting rule hl sample (start + extra)
      obtain ⟨next, hs⟩ := hl sample.1 _ _ k _ hp ha
      have hstill := run_written_some_after input C mode accounting rule hl sample start extra stage bit hw
      rw [Nat.add_succ, run_succ_of_step input C mode accounting rule sample (start + extra) next ha hs]
      exact (step_overlay_written_port_frame input C hearly mode accounting rule sample.1 _ _ hp hs
        draw mark ghost seed stage (by rw [hstill]; exact Option.some_ne_none bit)).trans ih


/-- Synthetic observations are not exposed in a live unwritten port. This
is a property of the concrete fold, with no source-law or legality premise. -/
theorem overlayReplay_unwritten_observations_nil {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (stage : I.Stage)
    (hnone : historyWritten history stage = none) (hhalt : historyHalted history = false) :
    historyObservations (overlayReplay draw mark ghost seed history).shadow stage = [] := by
  induction history using List.reverseRecOn with
  | nil => rfl
  | append_singleton history event ih =>
    have hn := (historyWritten_none_append history [event] stage).mp hnone
    have hh : historyHalted history = false ∧ historyHalted [event] = false := by
      simpa only [historyHalted_append, Bool.or_eq_false_eq_eq_false_and_eq_false] using hhalt
    have hprev := ih hn.1 hh.1
    rw [overlayReplay_append_event]
    cases event with
    | observation => simpa only [overlayStep, simulatorStep, simulatorAppend, List.append_nil] using hprev
    | wrote current bit serial =>
      have hne : current ≠ stage := by
        intro he
        subst current
        have h := hn.2
        simp [historyWritten, historyWrite, eventWrite] at h
      simpa [overlayStep, simulatorStep, simulatorAppend, historyObservations, simulatorReviewPacket,
        List.filterMap_append, overlayGhostEvents_no_observation, overlayGhostEvents_no_write, List.filterMap_map, Function.comp_def, eventObservation, hne] using hprev
    | report | committed | executed | advanced =>
      simpa [overlayStep, simulatorStep, simulatorAppend, historyObservations, List.filterMap_append, overlayGhostEvents_no_observation, overlayGhostEvents_no_write, eventObservation] using hprev
    | stopped =>
      have h := hh.2
      simp [historyHalted, historyActions, eventAction] at h
    | abandoned =>
      have h := hh.2
      simp [historyHalted, historyActions, eventAction] at h

theorem prefix_overlay_unwritten_port_fresh (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed SimSeed : Type*}
    (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (ha : s.halted = false) (stage : I.Stage) (hw : s.ledger.written stage = none)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I)) (simseed : SimSeed) :
    historyObservations (overlayReplay draw mark ghost simseed s.history).shadow stage = [] ∧
      historyWrite (overlayReplay draw mark ghost simseed s.history).shadow stage = none := by
  have hnone : historyWritten s.history stage = none :=
    (prefix_historyWritten input C mode accounting rule seed truth tapes hp stage).trans hw
  have hhalt : historyHalted s.history = false :=
    (prefix_historyHalted input C mode accounting rule seed truth tapes hp).trans ha
  refine ⟨overlayReplay_unwritten_observations_nil draw mark ghost simseed s.history stage hnone hhalt, ?_⟩
  have hs := ((overlayReplay_historyProjection draw mark ghost simseed s.history).2.1 stage).mp hnone
  cases he : historyWrite (overlayReplay draw mark ghost simseed s.history).shadow stage with
  | none => rfl
  | some pair => simp only [historyWritten, he, Option.map_some, reduceCtorEq] at hs

end PDROC
