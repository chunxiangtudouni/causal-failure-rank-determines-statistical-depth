module

public import PaperProofs.Paid.PDROC_SimulatorRecords_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

theorem completedHistory_eq_history_of_halted {SourceSeed : Type*}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I SourceSeed)
    (sample : SourceSeed × input.World) (history : List (VisibleEvent I))
    (hh : completedHistory input C mode accounting rule sample = some history)
    (n : ℕ) (hn : (run input C mode accounting rule sample n).halted = true) :
    history = (run input C mode accounting rule sample n).history := by
  obtain ⟨finish, hf, _, he⟩ := (completedHistory_some_iff input C mode accounting rule sample history).mp hh
  rcases le_total finish n with h | h
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [run_after_halt input C mode accounting rule sample finish hf extra]
    exact he.symm
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [run_after_halt input C mode accounting rule sample n hn extra] at he
    exact he.symm

theorem completed_simulator_written_port_frame (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {SourceSeed SimSeed : Type*} (rule : PolicyRule I SourceSeed)
    (hl : LegalRule input C mode accounting rule) (sample : SourceSeed × input.World)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (history : List (VisibleEvent I))
    (hh : completedHistory input C mode accounting rule sample = some history)
    (start : ℕ) (stage : I.Stage) (bit : Bool)
    (hw : (run input C mode accounting rule sample start).ledger.written stage = some bit) :
    simulatorPortView (simulatorReplay draw seed history).shadow stage =
      simulatorPortView (simulatorReplay draw seed (run input C mode accounting rule sample start).history).shadow stage := by
  obtain ⟨finish, hf, _, he⟩ := (completedHistory_some_iff input C mode accounting rule sample history).mp hh
  rw [← he]
  rcases le_total start finish with h | h
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le h
    exact run_simulator_written_port_frame input C hearly mode accounting rule hl sample draw seed start extra stage bit hw
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [run_after_halt input C mode accounting rule sample finish hf extra]

theorem simulatorReplay_writeReport_port {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (stage : I.Stage)
    (bit truth : Bool) (serial : ℕ)
    (ho : historyObservations (simulatorReplay draw seed history).shadow stage = [])
    (decision : Bool)
    (hd : (simulatorDrawRecord (draw seed stage (simulatorReplay draw seed history).shadow)).decision = some decision) :
    simulatorPortView (simulatorReplay draw seed
      (history ++ [.wrote stage bit serial, .report stage truth serial])).shadow stage =
      ((simulatorDrawRecord (draw seed stage (simulatorReplay draw seed history).shadow)).observations.map Fin.val,
        some decision) := by
  rw [show history ++ [.wrote stage bit serial, .report stage truth serial] =
    (history ++ [.wrote stage bit serial]) ++ [.report stage truth serial] by simp]
  rw [simulatorReplay_append_event, simulatorReplay_append_event]
  simp only [simulatorStep, simulatorAppend]
  rw [hd]
  simp only [Option.getD_some]
  change List.filterMap (eventObservation stage) (simulatorReplay draw seed history).shadow = [] at ho
  simp [simulatorPortView, historyObservations, historyWritten, historyWrite, simulatorReviewPacket,
    List.filterMap_append, List.filterMap_map, List.filterMap_cons, List.filterMap_nil, Function.comp_def, eventObservation, eventWrite, ho]
theorem simulatorReplay_terminal_port {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (stage : I.Stage) (abandon : Bool)
    (hc : historyCursor history = stage.val) (hw : historyWritten history stage = none)
    (ho : historyObservations (simulatorReplay draw seed history).shadow stage = [])
    (hvw : historyWritten (simulatorReplay draw seed history).shadow stage = none) :
    simulatorPortView (simulatorReplay draw seed
      (history ++ [if abandon then .abandoned else .stopped])).shadow stage =
      ((simulatorDrawRecord (draw seed stage (simulatorReplay draw seed history).shadow)).observations.map Fin.val, none) := by
  have hc' : historyCursor (simulatorReplay draw seed history).seen < I.stageCount := by
    rw [simulatorReplay_seen, hc]
    exact stage.isLt
  have he : (⟨historyCursor (simulatorReplay draw seed history).seen, hc'⟩ : I.Stage) = stage := by
    apply Fin.ext
    simpa only [simulatorReplay_seen] using hc
  have hw' : historyWritten (simulatorReplay draw seed history).seen
      ⟨historyCursor (simulatorReplay draw seed history).seen, hc'⟩ = none := by
    rw [he, simulatorReplay_seen, hw]
  have hw'' : historyWritten (simulatorReplay draw seed history).seen stage = none := by
    simpa only [he] using hw'
  change List.filterMap (eventObservation stage) (simulatorReplay draw seed history).shadow = [] at ho
  change (List.filterMap (eventWrite stage) (simulatorReplay draw seed history).shadow).getLast?.map Prod.fst = none at hvw
  cases abandon <;>
    simp only [Bool.false_eq_true, ↓reduceIte, simulatorReplay_append_event, simulatorStep,
      hc', ↓reduceDIte, he, hw'', simulatorAppend] <;>
    simp [simulatorPortView, historyObservations, historyWritten, historyWrite, simulatorReviewPacket,
      List.filterMap_append, List.filterMap_map, Function.comp_def, eventObservation, eventWrite, ho] <;> simpa [eventWrite] using hvw

universe u
variable {Seed : Type u}

theorem simulator_entry_shadow_fresh (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (sample : SimulatorSeed P Seed × (P.input fee hfee).World)
    (stage : P.sharedInstance.Stage) (entry : List (VisibleEvent P.sharedInstance))
    (he : entryHistory (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) stage sample = some entry) :
    historyCursor (simulatorShadow P fee hfee source sample.1 entry) = stage.val ∧
      historyObservations (simulatorShadow P fee hfee source sample.1 entry) stage = [] ∧
      historyWrite (simulatorShadow P fee hfee source sample.1 entry) stage = none := by
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  have hl := simulatorRule_legal P fee hfee C accounting source
  obtain ⟨start, hc, hbefore, hh⟩ := (entryHistory_some_iff input C.val .uncapped accounting actual stage sample entry).mp he
  have he' : FirstEntryAt input C.val .uncapped accounting actual stage.val start sample := ⟨hc, hbefore⟩
  obtain ⟨ha, hunborn⟩ := firstEntryAt_unborn input C.val .uncapped accounting actual hl sample stage.val start he'
  obtain ⟨hw, _⟩ := hunborn stage le_rfl
  obtain ⟨k, _, hp⟩ := run_has_prefix input C.val .uncapped accounting actual hl sample start
  rw [← hh]
  have hf := prefix_simulator_unwritten_port_fresh input C.val .uncapped accounting actual sample.1 _ _ hp ha stage hw
    (simulatorSeedDraw P fee hfee source) sample.1
  refine ⟨?_, hf⟩
  exact (simulatorReplay_sameProjection (simulatorSeedDraw P fee hfee source) sample.1 _).1.symm.trans
    ((prefix_historyCursor input C.val .uncapped accounting actual sample.1 _ _ hp).trans hc)

end PDROC


