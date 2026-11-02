module

public import PaperProofs.Paid.PDROC_OverlaySimulator_005
public import PaperProofs.Paid.PDROC_OverlaySimulator_024
public import PaperProofs.Common.NativeHeadContinuation

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

theorem overlayStep_write_frame {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (cache : SimulatorCache I) (event : VisibleEvent I) (stage : I.Stage)
    (he : eventWrite stage event = none) :
    historyWrite (overlayStep draw mark ghost seed cache event).shadow stage = historyWrite cache.shadow stage := by
  cases event with
  | observation | report | committed | executed | advanced | stopped | abandoned =>
    simp only [overlayStep, simulatorStep, simulatorAppend]
    all_goals (try split_ifs)
    all_goals simp [historyWrite, simulatorReviewPacket, List.filterMap_append,
      overlayGhostEvents_no_write, List.filterMap_map, Function.comp_def, eventWrite]
  | wrote current bit serial =>
    have hne : current ≠ stage := by intro h; subst current; simp [eventWrite] at he
    simp [overlayStep, simulatorStep, simulatorAppend, historyWrite, simulatorReviewPacket,
      List.filterMap_append, List.filterMap_map, Function.comp_def, eventWrite, hne]

theorem step_overlay_written_report_frame (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {SourceSeed SimSeed : Type*} (rule : PolicyRule I SourceSeed) (sourceSeed : SourceSeed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s next : State I}
    (_hp : Prefix input C mode accounting rule sourceSeed truth tapes n s) {action : Action I}
    (hs : Step input C mode accounting tapes s action next)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (stage : I.Stage) (hw : s.ledger.written stage ≠ none) :
    historyReport (overlayReplay draw mark ghost seed next.history).shadow stage =
      historyReport (overlayReplay draw mark ghost seed s.history).shadow stage := by
  have hone (event : VisibleEvent I) (he : eventReport stage event = none) :=
    overlayStep_report_frame draw mark ghost seed (overlayReplay draw mark ghost seed s.history) event stage he
  cases hs with
  | write current bit live port resources =>
    have hne : current ≠ stage := by intro h; subst current; exact hw port
    have hfirst := hone (.wrote current bit s.clock) rfl
    have hsecond := overlayStep_report_frame draw mark ghost seed
      (overlayStep draw mark ghost seed (overlayReplay draw mark ghost seed s.history) (.wrote current bit s.clock))
      (.report current (s.ledger.truth current) s.clock) stage (by simp [eventReport, hne])
    simpa only [record, writeResponses, hearly, ↓reduceIte, writeLedger,
      List.singleton_append, List.append_assoc, overlayReplay, List.foldl_append,
      List.foldl_cons, List.foldl_nil] using hsecond.trans hfirst
  | review current live port resources =>
    simpa only [record, overlayReplay_append_event] using hone
      (.observation current (tapes current (s.ledger.reviews current).toNat).val) rfl
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

theorem run_overlay_written_report_frame (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {SourceSeed SimSeed : Type*} (rule : PolicyRule I SourceSeed)
    (hl : LegalRule input C mode accounting rule) (sample : SourceSeed × input.World)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (start extra : ℕ) (stage : I.Stage) (bit : Bool)
    (hw : (run input C mode accounting rule sample start).ledger.written stage = some bit) :
    historyReport (overlayReplay draw mark ghost seed (run input C mode accounting rule sample (start + extra)).history).shadow stage =
      historyReport (overlayReplay draw mark ghost seed (run input C mode accounting rule sample start).history).shadow stage := by
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
      exact (step_overlay_written_report_frame input C hearly mode accounting rule sample.1 _ _ hp hs
        draw mark ghost seed stage (by rw [hstill]; exact Option.some_ne_none bit)).trans ih

theorem completed_overlay_written_report_frame (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {SourceSeed SimSeed : Type*} (rule : PolicyRule I SourceSeed)
    (hl : LegalRule input C mode accounting rule) (sample : SourceSeed × input.World)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (history : List (VisibleEvent I))
    (hh : completedHistory input C mode accounting rule sample = some history)
    (start : ℕ) (stage : I.Stage) (bit : Bool)
    (hw : (run input C mode accounting rule sample start).ledger.written stage = some bit) :
    historyReport (overlayReplay draw mark ghost seed history).shadow stage =
      historyReport (overlayReplay draw mark ghost seed (run input C mode accounting rule sample start).history).shadow stage := by
  obtain ⟨finish, hf, _, he⟩ := (completedHistory_some_iff input C mode accounting rule sample history).mp hh
  rw [← he]
  rcases le_total start finish with h | h
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le h
    exact run_overlay_written_report_frame input C hearly mode accounting rule hl sample draw mark ghost seed start extra stage bit hw
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [run_after_halt input C mode accounting rule sample finish hf extra]


theorem step_overlay_written_write_frame (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {SourceSeed SimSeed : Type*} (rule : PolicyRule I SourceSeed) (sourceSeed : SourceSeed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s next : State I}
    (_hp : Prefix input C mode accounting rule sourceSeed truth tapes n s) {action : Action I}
    (hs : Step input C mode accounting tapes s action next)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (stage : I.Stage) (hw : s.ledger.written stage ≠ none) :
    historyWrite (overlayReplay draw mark ghost seed next.history).shadow stage =
      historyWrite (overlayReplay draw mark ghost seed s.history).shadow stage := by
  have hone (event : VisibleEvent I) (he : eventWrite stage event = none) :=
    overlayStep_write_frame draw mark ghost seed (overlayReplay draw mark ghost seed s.history) event stage he
  cases hs with
  | write current bit live port resources =>
    have hne : current ≠ stage := by intro h; subst current; exact hw port
    have hfirst := hone (.wrote current bit s.clock) (by simp [eventWrite, hne])
    have hsecond := overlayStep_write_frame draw mark ghost seed
      (overlayStep draw mark ghost seed (overlayReplay draw mark ghost seed s.history) (.wrote current bit s.clock))
      (.report current (s.ledger.truth current) s.clock) stage rfl
    simpa only [record, writeResponses, hearly, ↓reduceIte, writeLedger,
      List.singleton_append, List.append_assoc, overlayReplay, List.foldl_append,
      List.foldl_cons, List.foldl_nil] using hsecond.trans hfirst
  | review current live port resources =>
    simpa only [record, overlayReplay_append_event] using hone
      (.observation current (tapes current (s.ledger.reviews current).toNat).val) rfl
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

theorem run_overlay_written_write_frame (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {SourceSeed SimSeed : Type*} (rule : PolicyRule I SourceSeed)
    (hl : LegalRule input C mode accounting rule) (sample : SourceSeed × input.World)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (start extra : ℕ) (stage : I.Stage) (bit : Bool)
    (hw : (run input C mode accounting rule sample start).ledger.written stage = some bit) :
    historyWrite (overlayReplay draw mark ghost seed (run input C mode accounting rule sample (start + extra)).history).shadow stage =
      historyWrite (overlayReplay draw mark ghost seed (run input C mode accounting rule sample start).history).shadow stage := by
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
      exact (step_overlay_written_write_frame input C hearly mode accounting rule sample.1 _ _ hp hs
        draw mark ghost seed stage (by rw [hstill]; exact Option.some_ne_none bit)).trans ih

theorem completed_overlay_written_write_frame (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {SourceSeed SimSeed : Type*} (rule : PolicyRule I SourceSeed)
    (hl : LegalRule input C mode accounting rule) (sample : SourceSeed × input.World)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (history : List (VisibleEvent I))
    (hh : completedHistory input C mode accounting rule sample = some history)
    (start : ℕ) (stage : I.Stage) (bit : Bool)
    (hw : (run input C mode accounting rule sample start).ledger.written stage = some bit) :
    historyWrite (overlayReplay draw mark ghost seed history).shadow stage =
      historyWrite (overlayReplay draw mark ghost seed (run input C mode accounting rule sample start).history).shadow stage := by
  obtain ⟨finish, hf, _, he⟩ := (completedHistory_some_iff input C mode accounting rule sample history).mp hh
  rw [← he]
  rcases le_total start finish with h | h
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le h
    exact run_overlay_written_write_frame input C hearly mode accounting rule hl sample draw mark ghost seed start extra stage bit hw
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [run_after_halt input C mode accounting rule sample finish hf extra]


theorem run_overlay_reportedWriteError_frame (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {SourceSeed SimSeed : Type*} (rule : PolicyRule I SourceSeed) (hl : LegalRule input C mode accounting rule)
    (sample : SourceSeed × input.World)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (start extra : ℕ) (stage : I.Stage) (bit : Bool)
    (hw : (run input C mode accounting rule sample start).ledger.written stage = some bit) :
    reportedWriteError (overlayReplay draw mark ghost seed (run input C mode accounting rule sample (start + extra)).history).shadow stage =
      reportedWriteError (overlayReplay draw mark ghost seed (run input C mode accounting rule sample start).history).shadow stage := by
  unfold reportedWriteError
  rw [run_overlay_written_write_frame input C hearly mode accounting rule hl sample draw mark ghost seed start extra stage bit hw,
    run_overlay_written_report_frame input C hearly mode accounting rule hl sample draw mark ghost seed start extra stage bit hw]

end PDROC
