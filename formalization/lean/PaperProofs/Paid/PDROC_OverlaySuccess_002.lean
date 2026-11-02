module

public import PaperProofs.Paid.PDROC_OverlaySuccess_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance} {SimSeed : Type*}

def overlaySuccess_eventGhost (event : VisibleEvent I) (calls : List (OverlayGhostCall I)) :
    List (OverlayGhostCall I) :=
  match event with
  | .advanced _ | .stopped | .abandoned => calls
  | _ => []

theorem overlaySuccess_execStep
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (cache : SimulatorCache I) (event : VisibleEvent I) :
    executedPairs (overlayStep draw mark ghost seed cache event).shadow =
      executedPairs cache.shadow ++ executedPairs [event] ++
        executedPairs (overlayGhostEvents (overlaySuccess_eventGhost event (ghost seed cache))) := by
  cases event <;> simp only [overlayStep, simulatorStep, simulatorAppend]
  all_goals (try split_ifs)
  all_goals simp [overlaySuccess_eventGhost, executedPairs, historyExecutions,
    simulatorReviewPacket, eventExecution, reserialHandle, overlayGhostEvents,
    List.filterMap_append, List.filterMap_map, List.filterMap_cons, List.filterMap_nil, Function.comp_def]

theorem overlaySuccess_execGhost_all (calls : List (OverlayGhostCall I))
    (good : I.Stage × I.Tool → Prop)
    (hgood : ∀ call ∈ calls, good (call.2.1.stage, call.2.2)) :
    ∀ pair ∈ executedPairs (overlayGhostEvents calls), good pair := by
  intro pair hm
  obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hm
  obtain ⟨event, hmem, hv⟩ := List.mem_filterMap.mp he
  obtain ⟨call, hc, rfl⟩ := List.mem_map.mp hmem
  cases hr : call.1
  · simp only [hr, Bool.false_eq_true, ite_false, eventExecution, Option.some.injEq] at hv
    subst entry
    exact hgood call hc
  · simp only [hr, ite_true, eventExecution] at hv
    cases hv

theorem overlaySuccess_step_history_prefix (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I} (hs : Step input C mode accounting tapes s action next) :
    s.history.IsPrefix next.history := by
  cases hs <;> exact List.prefix_append _ _

theorem overlaySuccess_exec_prefix {before after : List (VisibleEvent I)}
    (hp : before.IsPrefix after) : executedPairs before ⊆ executedPairs after := by
  obtain ⟨rest, rfl⟩ := hp
  rw [executedPairs_append]
  exact List.subset_append_left _ _

theorem overlaySuccess_correct_step (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I} (hs : Step input C mode accounting tapes s action next)
    (stage : I.Stage) (hc : s.ledger.written stage = some (s.ledger.truth stage)) :
    next.ledger.written stage = some (next.ledger.truth stage) := by
  rw [step_truth_unchanged input C mode accounting tapes hs]
  exact step_written_some input C mode accounting tapes hs stage _ hc

end PDROC
