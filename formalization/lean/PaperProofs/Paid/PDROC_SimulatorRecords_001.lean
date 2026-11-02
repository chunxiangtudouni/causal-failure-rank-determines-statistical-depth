module

public import PaperProofs.Paid.PDROC_SimulatorProjection_003
public import PaperProofs.Paid.PDROC_Simulator_017

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

def simulatorPortView (history : List (VisibleEvent I)) (stage : I.Stage) : List ℕ × Option Bool :=
  (historyObservations history stage, historyWritten history stage)

theorem simulatorStep_written_port_frame {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (cache : SimulatorCache I) (event : VisibleEvent I) (stage : I.Stage)
    (hw : historyWritten cache.seen stage ≠ none) (he : eventWrite stage event = none) :
    simulatorPortView (simulatorStep draw seed cache event).shadow stage =
      simulatorPortView cache.shadow stage := by
  cases event with
  | observation | report | committed | executed | advanced =>
    simp [simulatorPortView, simulatorStep, simulatorAppend, historyObservations, historyWritten,
      historyWrite, List.filterMap_append, eventObservation, eventWrite]
  | wrote current bit serial =>
    have hne : current ≠ stage := by intro h; subst current; simp [eventWrite] at he
    simp [simulatorPortView, simulatorStep, simulatorAppend, simulatorReviewPacket,
      historyObservations, historyWritten, historyWrite, List.filterMap_append,
      List.filterMap_map, Function.comp_def, eventObservation, eventWrite, hne]
  | stopped | abandoned =>
    dsimp only [simulatorStep]
    split_ifs with hc hn
    · have hne : (⟨historyCursor cache.seen, hc⟩ : I.Stage) ≠ stage := by
        intro h
        exact hw (h ▸ hn)
      simp [simulatorPortView, simulatorAppend, simulatorReviewPacket, historyObservations,
        historyWritten, historyWrite, List.filterMap_append, List.filterMap_map,
        Function.comp_def, eventObservation, eventWrite, hne]
    all_goals simp [simulatorPortView, simulatorAppend, historyObservations, historyWritten,
      historyWrite, List.filterMap_append, eventObservation, eventWrite]

theorem step_simulator_written_port_frame (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {SourceSeed SimSeed : Type*} (rule : PolicyRule I SourceSeed) (sourceSeed : SourceSeed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s next : State I}
    (hp : Prefix input C mode accounting rule sourceSeed truth tapes n s) {action : Action I}
    (hs : Step input C mode accounting tapes s action next)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (stage : I.Stage) (hw : s.ledger.written stage ≠ none) :
    simulatorPortView (simulatorReplay draw seed next.history).shadow stage =
      simulatorPortView (simulatorReplay draw seed s.history).shadow stage := by
  have hwh : historyWritten (simulatorReplay draw seed s.history).seen stage ≠ none := by
    rw [simulatorReplay_seen, prefix_historyWritten input C mode accounting rule sourceSeed truth tapes hp]
    exact hw
  have hone (event : VisibleEvent I) (he : eventWrite stage event = none) :=
    simulatorStep_written_port_frame draw seed (simulatorReplay draw seed s.history) event stage hwh he
  cases hs with
  | write current bit live port resources =>
    have hne : current ≠ stage := by intro h; subst current; exact hw port
    have hfirst := hone (.wrote current bit s.clock) (by simp [eventWrite, hne])
    have hstill : historyWritten (simulatorStep draw seed (simulatorReplay draw seed s.history)
        (.wrote current bit s.clock)).seen stage ≠ none := by
      rw [simulatorStep_seen, simulatorReplay_seen]
      simpa [historyWritten, historyWrite, List.filterMap_append, eventWrite, hne, simulatorReplay_seen] using hwh
    have hsecond := simulatorStep_written_port_frame draw seed
      (simulatorStep draw seed (simulatorReplay draw seed s.history) (.wrote current bit s.clock))
      (.report current (s.ledger.truth current) s.clock) stage hstill rfl
    simpa only [record, writeResponses, hearly, ↓reduceIte, writeLedger,
      List.singleton_append, List.append_assoc, simulatorReplay, List.foldl_append, List.foldl_cons, List.foldl_nil] using hsecond.trans hfirst
  | review current live port resources =>
    simpa only [record, simulatorReplay_append_event] using hone (.observation current (tapes current (s.ledger.reviews current).toNat).val) rfl
  | allocate handle tool active valid compatible unused unallocated window resources =>
    simpa only [record, simulatorReplay_append_event] using hone (.committed handle tool) rfl
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    simpa only [record, simulatorReplay_append_event] using hone (.executed handle tool) rfl
  | advance current live written resources =>
    simpa only [record, simulatorReplay_append_event] using hone (.advanced current) rfl
  | stop active =>
    simpa only [stopState, Bool.false_eq_true, ↓reduceIte, simulatorReplay_append_event] using hone .stopped rfl
  | abandon active =>
    simpa only [stopState, ↓reduceIte, simulatorReplay_append_event] using hone .abandoned rfl

theorem run_simulator_written_port_frame (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {SourceSeed SimSeed : Type*} (rule : PolicyRule I SourceSeed)
    (hl : LegalRule input C mode accounting rule) (sample : SourceSeed × input.World)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (start extra : ℕ) (stage : I.Stage) (bit : Bool)
    (hw : (run input C mode accounting rule sample start).ledger.written stage = some bit) :
    simulatorPortView (simulatorReplay draw seed (run input C mode accounting rule sample (start + extra)).history).shadow stage =
      simulatorPortView (simulatorReplay draw seed (run input C mode accounting rule sample start).history).shadow stage := by
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
      exact (step_simulator_written_port_frame input C hearly mode accounting rule sample.1 _ _ hp hs
        draw seed stage (by rw [hstill]; exact Option.some_ne_none bit)).trans ih

end PDROC

