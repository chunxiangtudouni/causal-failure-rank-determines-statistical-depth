module

public import PaperProofs.Paid.PDROC_OverlaySuccess_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance} {Actual Source SimSeed : Type*}

theorem overlaySuccess_reserveStep
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (cache : SimulatorCache I) (event : VisibleEvent I) :
    reservedPairs (overlayStep draw mark ghost seed cache event).shadow =
      reservedPairs cache.shadow ++ reservedPairs [event] ++
        reservedPairs (overlayGhostEvents (overlaySuccess_eventGhost event (ghost seed cache))) := by
  cases event <;> simp only [overlayStep, simulatorStep, simulatorAppend]
  all_goals (try split_ifs)
  all_goals simp [overlaySuccess_eventGhost, reservedPairs, historyCommitments,
    simulatorReviewPacket, eventCommitment, reserialHandle, overlayGhostEvents,
    List.filterMap_append, List.filterMap_map, List.filterMap_cons, List.filterMap_nil, Function.comp_def]

theorem overlaySuccess_reserveGhost_all (calls : List (OverlayGhostCall I))
    (good : I.Stage × I.Tool → Prop)
    (hgood : ∀ call ∈ calls, good (call.2.1.stage, call.2.2)) :
    ∀ pair ∈ reservedPairs (overlayGhostEvents calls), good pair := by
  intro pair hm
  obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hm
  obtain ⟨event, hmem, hv⟩ := List.mem_filterMap.mp he
  obtain ⟨call, hc, rfl⟩ := List.mem_map.mp hmem
  cases hr : call.1
  · simp only [hr, Bool.false_eq_true, ite_false, eventCommitment] at hv
    cases hv
  · simp only [hr, ite_true, eventCommitment, Option.some.injEq] at hv
    subst entry
    exact hgood call hc

theorem overlaySuccess_reserve_prefix {before after : List (VisibleEvent I)}
    (hp : before.IsPrefix after) : reservedPairs before ⊆ reservedPairs after := by
  obtain ⟨rest, rfl⟩ := hp
  rw [reservedPairs_append]
  exact List.subset_append_left _ _

theorem overlaySuccess_reserve_singleton (event : VisibleEvent I) :
    reservedPairs [event] = match event with
      | .committed handle tool => [(handle.stage, tool)]
      | _ => [] := by
  cases event <;> rfl

theorem overlaySuccess_reserveGhost_nil : reservedPairs (overlayGhostEvents ([] : List (OverlayGhostCall I))) = [] := rfl

/-- Every extra virtual reservation lies at an actually correct stage. -/
theorem overlaySuccess_prefix_reserve_covered
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Actual) (seed : Actual) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    (source : PolicyRule I Source) (oldSeed : Source)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool) (simSeed : SimSeed)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s) :
    ∀ pair ∈ reservedPairs (overlayReplay draw mark (fun _ => overlayGhostAtCache source oldSeed) simSeed s.history).shadow,
      s.ledger.written pair.1 = some (s.ledger.truth pair.1) ∨ pair ∈ reservedPairs s.history := by
  induction hp with
  | initial => simp [initial, overlayReplay, simulatorInitialCache, reservedPairs, historyCommitments]
  | @next n s next hp hs ih =>
    let ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I) := fun _ => overlayGhostAtCache source oldSeed
    let cache := overlayReplay draw mark ghost simSeed s.history
    have hseen : cache.seen = s.history := overlayReplay_seen draw mark ghost simSeed s.history
    have hproj := overlayReplay_historyProjection draw mark ghost simSeed s.history
    have hold (pair : I.Stage × I.Tool) (hm : pair ∈ reservedPairs cache.shadow) :
        next.ledger.written pair.1 = some (next.ledger.truth pair.1) ∨ pair ∈ reservedPairs next.history := by
      rcases ih pair hm with hc | he
      · exact Or.inl (overlaySuccess_correct_step input C mode accounting tapes hs pair.1 hc)
      · exact Or.inr (overlaySuccess_reserve_prefix (overlaySuccess_step_history_prefix input C mode accounting tapes hs) he)
    have hghost : ∀ pair ∈ reservedPairs (overlayGhostEvents (ghost simSeed cache)),
        next.ledger.written pair.1 = some (next.ledger.truth pair.1) ∨ pair ∈ reservedPairs next.history := by
      apply overlaySuccess_reserveGhost_all
      intro call hm
      exact Or.inl (overlaySuccess_correct_step input C mode accounting tapes hs _
        (overlaySuccess_ghost_member_correct input C hearly mode accounting rule seed truth tapes hp
          source oldSeed cache hseen hproj call hm))
    intro pair hm
    change pair ∈ reservedPairs (overlayReplay draw mark ghost simSeed next.history).shadow at hm
    generalize ha : rule seed s.history = action at hs
    cases hs with
    | write current bit live port resources =>
      simp only [record, writeResponses, hearly, ↓reduceIte, writeLedger,
        List.singleton_append, overlayReplay, List.foldl_append,
        List.foldl_cons, List.foldl_nil] at hm
      change pair ∈ reservedPairs (overlayStep draw mark ghost simSeed
        (overlayStep draw mark ghost simSeed cache (.wrote current bit s.clock))
        (.report current (s.ledger.truth current) s.clock)).shadow at hm
      rw [overlaySuccess_reserveStep, overlaySuccess_reserveStep] at hm
      simp only [overlaySuccess_eventGhost, overlaySuccess_reserve_singleton, overlaySuccess_reserveGhost_nil, List.append_nil] at hm
      exact hold pair hm
    | review current live port resources =>
      simp only [record, overlayReplay_append_event] at hm
      rw [overlaySuccess_reserveStep] at hm
      simp only [overlaySuccess_eventGhost, overlaySuccess_reserve_singleton, overlaySuccess_reserveGhost_nil, List.append_nil] at hm
      exact hold pair hm
    | allocate handle tool active valid compatible unused unallocated window resources =>
      simp only [record, overlayReplay_append_event] at hm
      rw [overlaySuccess_reserveStep] at hm
      simp only [overlaySuccess_eventGhost, overlaySuccess_reserve_singleton, overlaySuccess_reserveGhost_nil, List.append_nil, List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact hold pair hm
      · apply Or.inr
        simp [record, reservedPairs, historyCommitments, eventCommitment]
    | execute handle tool active valid compatible committed unused uncorrected window resources =>
      simp only [record, overlayReplay_append_event] at hm
      rw [overlaySuccess_reserveStep] at hm
      simp only [overlaySuccess_eventGhost, overlaySuccess_reserve_singleton, overlaySuccess_reserveGhost_nil, List.append_nil] at hm
      exact hold pair hm
    | advance current live written resources =>
      simp only [record, overlayReplay_append_event] at hm
      rw [overlaySuccess_reserveStep] at hm
      simp only [overlaySuccess_eventGhost, overlaySuccess_reserve_singleton, List.append_nil, List.mem_append] at hm
      exact hm.elim (hold pair) (hghost pair)
    | stop active =>
      simp only [stopState, Bool.false_eq_true, ↓reduceIte, overlayReplay_append_event] at hm
      rw [overlaySuccess_reserveStep] at hm
      simp only [overlaySuccess_eventGhost, overlaySuccess_reserve_singleton, List.append_nil, List.mem_append] at hm
      exact hm.elim (hold pair) (hghost pair)
    | abandon active =>
      simp only [stopState, ↓reduceIte, overlayReplay_append_event] at hm
      rw [overlaySuccess_reserveStep] at hm
      simp only [overlaySuccess_eventGhost, overlaySuccess_reserve_singleton, List.append_nil, List.mem_append] at hm
      exact hm.elim (hold pair) (hghost pair)

/-- On every actually wrong stage, a virtual reservation must be physical. -/
theorem overlaySuccess_prefix_wrong_reserve_physical
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Actual) (seed : Actual) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    (source : PolicyRule I Source) (oldSeed : Source)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool) (simSeed : SimSeed)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (stage : I.Stage) (tool : I.Tool)
    (hw : s.ledger.written stage = some (!s.ledger.truth stage))
    (he : (stage, tool) ∈ reservedPairs (overlayReplay draw mark
      (fun _ => overlayGhostAtCache source oldSeed) simSeed s.history).shadow) :
    (stage, tool) ∈ reservedPairs s.history := by
  rcases overlaySuccess_prefix_reserve_covered input C hearly mode accounting rule seed truth tapes source oldSeed draw mark simSeed hp (stage, tool) he with hc | he
  · rw [hw] at hc
    cases ht : s.ledger.truth stage <;> simp [ht] at hc
  · exact he

end PDROC
