module

public import PaperProofs.Paid.PDROC_OverlaySuccess_002
public import PaperProofs.Paid.PDROC_OverlaySimulator_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance} {Actual Source SimSeed : Type*}

theorem overlaySuccess_exec_singleton (event : VisibleEvent I) :
    executedPairs [event] = match event with
      | .executed handle tool => [(handle.stage, tool)]
      | _ => [] := by
  cases event <;> rfl

theorem overlaySuccess_execGhost_nil : executedPairs (overlayGhostEvents ([] : List (OverlayGhostCall I))) = [] := rfl

/-- Every extra virtual execution lies at an actually correct stage. -/
theorem overlaySuccess_prefix_exec_covered
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Actual) (seed : Actual) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    (source : PolicyRule I Source) (oldSeed : Source)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool) (simSeed : SimSeed)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s) :
    ∀ pair ∈ executedPairs (overlayReplay draw mark (fun _ => overlayGhostAtCache source oldSeed) simSeed s.history).shadow,
      s.ledger.written pair.1 = some (s.ledger.truth pair.1) ∨ pair ∈ executedPairs s.history := by
  induction hp with
  | initial => simp [initial, overlayReplay, simulatorInitialCache, executedPairs, historyExecutions]
  | @next n s next hp hs ih =>
    let ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I) := fun _ => overlayGhostAtCache source oldSeed
    let cache := overlayReplay draw mark ghost simSeed s.history
    have hseen : cache.seen = s.history := overlayReplay_seen draw mark ghost simSeed s.history
    have hproj := overlayReplay_historyProjection draw mark ghost simSeed s.history
    have hold (pair : I.Stage × I.Tool) (hm : pair ∈ executedPairs cache.shadow) :
        next.ledger.written pair.1 = some (next.ledger.truth pair.1) ∨ pair ∈ executedPairs next.history := by
      rcases ih pair hm with hc | he
      · exact Or.inl (overlaySuccess_correct_step input C mode accounting tapes hs pair.1 hc)
      · exact Or.inr (overlaySuccess_exec_prefix (overlaySuccess_step_history_prefix input C mode accounting tapes hs) he)
    have hghost : ∀ pair ∈ executedPairs (overlayGhostEvents (ghost simSeed cache)),
        next.ledger.written pair.1 = some (next.ledger.truth pair.1) ∨ pair ∈ executedPairs next.history := by
      apply overlaySuccess_execGhost_all
      intro call hm
      exact Or.inl (overlaySuccess_correct_step input C mode accounting tapes hs _
        (overlaySuccess_ghost_member_correct input C hearly mode accounting rule seed truth tapes hp
          source oldSeed cache hseen hproj call hm))
    intro pair hm
    change pair ∈ executedPairs (overlayReplay draw mark ghost simSeed next.history).shadow at hm
    generalize ha : rule seed s.history = action at hs
    cases hs with
    | write current bit live port resources =>
      simp only [record, writeResponses, hearly, ↓reduceIte, writeLedger,
        List.singleton_append, overlayReplay, List.foldl_append,
        List.foldl_cons, List.foldl_nil] at hm
      change pair ∈ executedPairs (overlayStep draw mark ghost simSeed
        (overlayStep draw mark ghost simSeed cache (.wrote current bit s.clock))
        (.report current (s.ledger.truth current) s.clock)).shadow at hm
      rw [overlaySuccess_execStep, overlaySuccess_execStep] at hm
      simp only [overlaySuccess_eventGhost, overlaySuccess_exec_singleton, overlaySuccess_execGhost_nil, List.append_nil] at hm
      exact hold pair hm
    | review current live port resources =>
      simp only [record, overlayReplay_append_event] at hm
      rw [overlaySuccess_execStep] at hm
      simp only [overlaySuccess_eventGhost, overlaySuccess_exec_singleton, overlaySuccess_execGhost_nil, List.append_nil] at hm
      exact hold pair hm
    | allocate handle tool active valid compatible unused unallocated window resources =>
      simp only [record, overlayReplay_append_event] at hm
      rw [overlaySuccess_execStep] at hm
      simp only [overlaySuccess_eventGhost, overlaySuccess_exec_singleton, overlaySuccess_execGhost_nil, List.append_nil] at hm
      exact hold pair hm
    | execute handle tool active valid compatible committed unused uncorrected window resources =>
      simp only [record, overlayReplay_append_event] at hm
      rw [overlaySuccess_execStep] at hm
      simp only [overlaySuccess_eventGhost, overlaySuccess_exec_singleton, overlaySuccess_execGhost_nil, List.append_nil, List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact hold pair hm
      · apply Or.inr
        simp [record, executedPairs, historyExecutions, eventExecution]
    | advance current live written resources =>
      simp only [record, overlayReplay_append_event] at hm
      rw [overlaySuccess_execStep] at hm
      simp only [overlaySuccess_eventGhost, overlaySuccess_exec_singleton, List.append_nil, List.mem_append] at hm
      exact hm.elim (hold pair) (hghost pair)
    | stop active =>
      simp only [stopState, Bool.false_eq_true, ↓reduceIte, overlayReplay_append_event] at hm
      rw [overlaySuccess_execStep] at hm
      simp only [overlaySuccess_eventGhost, overlaySuccess_exec_singleton, List.append_nil, List.mem_append] at hm
      exact hm.elim (hold pair) (hghost pair)
    | abandon active =>
      simp only [stopState, ↓reduceIte, overlayReplay_append_event] at hm
      rw [overlaySuccess_execStep] at hm
      simp only [overlaySuccess_eventGhost, overlaySuccess_exec_singleton, List.append_nil, List.mem_append] at hm
      exact hm.elim (hold pair) (hghost pair)

/-- On every actually wrong stage, a virtual execution must be physical. -/
theorem overlaySuccess_prefix_wrong_exec_physical
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Actual) (seed : Actual) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    (source : PolicyRule I Source) (oldSeed : Source)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool) (simSeed : SimSeed)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (stage : I.Stage) (tool : I.Tool)
    (hw : s.ledger.written stage = some (!s.ledger.truth stage))
    (he : (stage, tool) ∈ executedPairs (overlayReplay draw mark
      (fun _ => overlayGhostAtCache source oldSeed) simSeed s.history).shadow) :
    (stage, tool) ∈ executedPairs s.history := by
  rcases overlaySuccess_prefix_exec_covered input C hearly mode accounting rule seed truth tapes source oldSeed draw mark simSeed hp (stage, tool) he with hc | he
  · rw [hw] at hc
    cases ht : s.ledger.truth stage <;> simp [ht] at hc
  · exact he

end PDROC
