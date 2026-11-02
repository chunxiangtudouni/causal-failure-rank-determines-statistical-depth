module

public import PaperProofs.Paid.PDROC_Simulator_025
public import PaperProofs.Paid.PDROC_SimulatorRecords_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

theorem simulatorStep_report_frame {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (cache : SimulatorCache I) (event : VisibleEvent I) (stage : I.Stage)
    (he : eventReport stage event = none) :
    historyReport (simulatorStep draw seed cache event).shadow stage = historyReport cache.shadow stage := by
  cases event with
  | observation | wrote | committed | executed | advanced | stopped | abandoned =>
    simp only [simulatorStep, simulatorAppend]
    all_goals (try split_ifs)
    all_goals simp [historyReport, simulatorReviewPacket, List.filterMap_append,
      List.filterMap_map, Function.comp_def, eventReport]
  | report current truth serial =>
    have hne : current ≠ stage := by intro h; subst current; simp [eventReport] at he
    simp [simulatorStep, simulatorAppend, historyReport, List.filterMap_append, eventReport, hne]

theorem step_simulator_written_report_frame (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {SourceSeed SimSeed : Type*} (rule : PolicyRule I SourceSeed) (sourceSeed : SourceSeed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s next : State I}
    (_hp : Prefix input C mode accounting rule sourceSeed truth tapes n s) {action : Action I}
    (hs : Step input C mode accounting tapes s action next)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (stage : I.Stage) (hw : s.ledger.written stage ≠ none) :
    historyReport (simulatorReplay draw seed next.history).shadow stage =
      historyReport (simulatorReplay draw seed s.history).shadow stage := by
  have hone (event : VisibleEvent I) (he : eventReport stage event = none) :=
    simulatorStep_report_frame draw seed (simulatorReplay draw seed s.history) event stage he
  cases hs with
  | write current bit live port resources =>
    have hne : current ≠ stage := by intro h; subst current; exact hw port
    have hfirst := hone (.wrote current bit s.clock) rfl
    have hsecond := simulatorStep_report_frame draw seed
      (simulatorStep draw seed (simulatorReplay draw seed s.history) (.wrote current bit s.clock))
      (.report current (s.ledger.truth current) s.clock) stage (by simp [eventReport, hne])
    simpa only [record, writeResponses, hearly, ↓reduceIte, writeLedger,
      List.singleton_append, List.append_assoc, simulatorReplay, List.foldl_append,
      List.foldl_cons, List.foldl_nil] using hsecond.trans hfirst
  | review current live port resources =>
    simpa only [record, simulatorReplay_append_event] using hone
      (.observation current (tapes current (s.ledger.reviews current).toNat).val) rfl
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

theorem run_simulator_written_report_frame (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {SourceSeed SimSeed : Type*} (rule : PolicyRule I SourceSeed)
    (hl : LegalRule input C mode accounting rule) (sample : SourceSeed × input.World)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (start extra : ℕ) (stage : I.Stage) (bit : Bool)
    (hw : (run input C mode accounting rule sample start).ledger.written stage = some bit) :
    historyReport (simulatorReplay draw seed (run input C mode accounting rule sample (start + extra)).history).shadow stage =
      historyReport (simulatorReplay draw seed (run input C mode accounting rule sample start).history).shadow stage := by
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
      exact (step_simulator_written_report_frame input C hearly mode accounting rule sample.1 _ _ hp hs
        draw seed stage (by rw [hstill]; exact Option.some_ne_none bit)).trans ih

theorem completed_simulator_written_report_frame (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {SourceSeed SimSeed : Type*} (rule : PolicyRule I SourceSeed)
    (hl : LegalRule input C mode accounting rule) (sample : SourceSeed × input.World)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (history : List (VisibleEvent I))
    (hh : completedHistory input C mode accounting rule sample = some history)
    (start : ℕ) (stage : I.Stage) (bit : Bool)
    (hw : (run input C mode accounting rule sample start).ledger.written stage = some bit) :
    historyReport (simulatorReplay draw seed history).shadow stage =
      historyReport (simulatorReplay draw seed (run input C mode accounting rule sample start).history).shadow stage := by
  obtain ⟨finish, hf, _, he⟩ := (completedHistory_some_iff input C mode accounting rule sample history).mp hh
  rw [← he]
  rcases le_total start finish with h | h
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le h
    exact run_simulator_written_report_frame input C hearly mode accounting rule hl sample draw seed start extra stage bit hw
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [run_after_halt input C mode accounting rule sample finish hf extra]

end PDROC
