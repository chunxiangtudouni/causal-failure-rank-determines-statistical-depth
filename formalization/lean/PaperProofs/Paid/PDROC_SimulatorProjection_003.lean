module

public import PaperProofs.Paid.PDROC_SimulatorProjection_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

theorem simulatorReplay_append_event {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (event : VisibleEvent I) :
    simulatorReplay draw seed (history ++ [event]) =
      simulatorStep draw seed (simulatorReplay draw seed history) event := by
  simp only [simulatorReplay, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Synthetic observations are not exposed in a live unwritten port. This
is a property of the concrete fold, with no source-law or legality premise. -/
theorem simulatorReplay_unwritten_observations_nil {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (stage : I.Stage)
    (hnone : historyWritten history stage = none) (hhalt : historyHalted history = false) :
    historyObservations (simulatorReplay draw seed history).shadow stage = [] := by
  induction history using List.reverseRecOn with
  | nil => rfl
  | append_singleton history event ih =>
    have hn := (historyWritten_none_append history [event] stage).mp hnone
    have hh : historyHalted history = false ∧ historyHalted [event] = false := by
      simpa only [historyHalted_append, Bool.or_eq_false_eq_eq_false_and_eq_false] using hhalt
    have hprev := ih hn.1 hh.1
    rw [simulatorReplay_append_event]
    cases event with
    | observation => simpa only [simulatorStep, simulatorAppend, List.append_nil] using hprev
    | wrote current bit serial =>
      have hne : current ≠ stage := by
        intro he
        subst current
        have h := hn.2
        simp [historyWritten, historyWrite, eventWrite] at h
      simpa [simulatorStep, simulatorAppend, historyObservations, simulatorReviewPacket,
        List.filterMap_append, List.filterMap_map, Function.comp_def, eventObservation, hne] using hprev
    | report | committed | executed | advanced =>
      simpa [simulatorStep, simulatorAppend, historyObservations, List.filterMap_append, eventObservation] using hprev
    | stopped =>
      have h := hh.2
      simp [historyHalted, historyActions, eventAction] at h
    | abandoned =>
      have h := hh.2
      simp [historyHalted, historyActions, eventAction] at h

theorem prefix_simulator_unwritten_port_fresh (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed SimSeed : Type*}
    (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (ha : s.halted = false) (stage : I.Stage) (hw : s.ledger.written stage = none)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I)) (simseed : SimSeed) :
    historyObservations (simulatorReplay draw simseed s.history).shadow stage = [] ∧
      historyWrite (simulatorReplay draw simseed s.history).shadow stage = none := by
  have hnone : historyWritten s.history stage = none :=
    (prefix_historyWritten input C mode accounting rule seed truth tapes hp stage).trans hw
  have hhalt : historyHalted s.history = false :=
    (prefix_historyHalted input C mode accounting rule seed truth tapes hp).trans ha
  refine ⟨simulatorReplay_unwritten_observations_nil draw simseed s.history stage hnone hhalt, ?_⟩
  have hs := ((simulatorReplay_sameProjection draw simseed s.history).2.2.2.1 stage).mp hnone
  cases he : historyWrite (simulatorReplay draw simseed s.history).shadow stage with
  | none => rfl
  | some pair => simp only [historyWritten, he, Option.map_some, reduceCtorEq] at hs

end PDROC
