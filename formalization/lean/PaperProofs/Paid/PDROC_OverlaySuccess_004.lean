module

public import PaperProofs.Paid.PDROC_OverlaySuccess_002
public import PaperProofs.Paid.PDROC_OverlaySimulator_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance} {SimSeed Seed : Type*}

theorem overlaySuccess_ghostEvents_no_stop (calls : List (OverlayGhostCall I)) :
    VisibleEvent.stopped ∉ overlayGhostEvents calls := by
  induction calls with
  | nil => simp [overlayGhostEvents]
  | cons call rest ih =>
    rcases call with ⟨reserve, handle, tool⟩
    cases reserve <;> simp [overlayGhostEvents]

theorem overlaySuccess_step_stop
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (cache : SimulatorCache I) (event : VisibleEvent I) :
    VisibleEvent.stopped ∈ (overlayStep draw mark ghost seed cache event).shadow ↔
      VisibleEvent.stopped ∈ cache.shadow ∨ event = .stopped := by
  have hg := overlaySuccess_ghostEvents_no_stop (ghost seed cache)
  cases event <;> simp only [overlayStep, simulatorStep, simulatorAppend]
  all_goals (try split_ifs)
  all_goals simp [simulatorReviewPacket, hg]

theorem overlaySuccess_replay_stop
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (history : List (VisibleEvent I)) :
    VisibleEvent.stopped ∈ (overlayReplay draw mark ghost seed history).shadow ↔
      VisibleEvent.stopped ∈ history := by
  have hfold (history : List (VisibleEvent I)) (cache : SimulatorCache I) :
      VisibleEvent.stopped ∈ (history.foldl (overlayStep draw mark ghost seed) cache).shadow ↔
        VisibleEvent.stopped ∈ cache.shadow ∨ VisibleEvent.stopped ∈ history := by
    induction history generalizing cache with
    | nil => simp
    | cons event rest ih =>
      rw [List.foldl_cons, ih, overlaySuccess_step_stop]
      simp only [List.mem_cons]
      tauto
  simpa only [overlayReplay, simulatorInitialCache, List.not_mem_nil, false_or] using
    hfold history (simulatorInitialCache I)

theorem overlaySuccess_historyHalted_of_stop (history : List (VisibleEvent I))
    (hm : VisibleEvent.stopped ∈ history) : historyHalted history = true := by
  apply List.any_eq_true.mpr
  exact ⟨Action.stop, List.mem_filterMap.mpr ⟨VisibleEvent.stopped, hm, rfl⟩, rfl⟩

theorem overlaySuccess_step_active (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I} (hs : Step input C mode accounting tapes s action next) :
    s.halted = false := by
  cases hs with
  | review _ live | write _ _ live | advance _ live => exact live.1
  | allocate _ _ active | execute _ _ active | stop active | abandon active => exact active

theorem overlaySuccess_prefix_stop_last (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (hm : VisibleEvent.stopped ∈ s.history) :
    s.history.getLast? = some .stopped ∧ s.halted = true := by
  cases hp with
  | initial => cases hm
  | @next n s next hp hs =>
    have hn : VisibleEvent.stopped ∉ s.history := by
      intro hm
      have hh := overlaySuccess_historyHalted_of_stop s.history hm
      rw [prefix_historyHalted input C mode accounting rule seed truth tapes hp,
        overlaySuccess_step_active input C mode accounting tapes hs] at hh
      cases hh
    generalize ha : rule seed s.history = action at hs
    cases hs <;> simp_all [record, stopState, writeResponses, writeLedger]

theorem overlaySuccess_resolved_written (history : List (VisibleEvent I)) (stage : I.Stage)
    (hr : PaperProofs.Paid.Parameters.historyStageResolved I history stage = true) :
    historyWritten history stage ≠ none := by
  unfold PaperProofs.Paid.Parameters.historyStageResolved at hr
  cases hw : historyWrite history stage with
  | none => simp [hw] at hr
  | some entry => simp [historyWritten, hw]

theorem overlaySuccess_resolved_error_exec (history : List (VisibleEvent I)) (stage : I.Stage)
    (hr : PaperProofs.Paid.Parameters.historyStageResolved I history stage = true)
    (he : reportedWriteError history stage = some true) :
    ∃ tool, (stage, tool) ∈ executedPairs history := by
  unfold reportedWriteError at he
  cases hw : historyWrite history stage with
  | none => simp [hw] at he
  | some written =>
    cases ht : historyReport history stage with
    | none => simp [hw, ht] at he
    | some reported =>
      simp only [hw, ht] at he
      change (if written.2 = reported.2 then some (written.1 != reported.1) else none) = some true at he
      split_ifs at he with hserial
      · have hbits : written.1 ≠ reported.1 := by simpa using he
        have hh : (historyExecutions history).any (fun e =>
            (e.1.stage == stage) && (e.1.writeSerial == written.2)) = true := by
          simpa [PaperProofs.Paid.Parameters.historyStageResolved, hw, ht, hserial, hbits] using hr
        obtain ⟨e, hem, htest⟩ := List.any_eq_true.mp hh
        have hes : e.1.stage = stage := by
          have hboth : e.1.stage = stage ∧ e.1.writeSerial = written.2 := by
            simpa only [Bool.and_eq_true_eq_eq_true_and_eq_true, beq_iff_eq] using htest
          exact hboth.1
        exact ⟨e.2, List.mem_map.mpr ⟨e, hem, by rw [hes]⟩⟩

end PDROC
