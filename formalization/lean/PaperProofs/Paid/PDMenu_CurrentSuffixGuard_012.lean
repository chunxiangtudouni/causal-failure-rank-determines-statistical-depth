module

public import PaperProofs.Paid.PDMenu_CurrentHeadKernel_006
public import PaperProofs.Common.NativeBellmanGuardLift

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native

theorem replayAllows_of_paidAllows {I : Instance} (available : Finset I.Tool)
    (history : List (VisibleEvent I)) (action : Action I)
    (hallow : historyAllowsAction history action) (halloc : paidAllocationAllowed available action) :
    replayAllowsAction available history action := by
  cases action with
  | review stage => exact hallow
  | write stage bit => exact hallow
  | advance stage => exact hallow
  | allocate handle tool => exact ⟨halloc, hallow⟩
  | execute handle tool => exact hallow.2
  | stop => trivial
  | abandon => trivial

/-- The existing exact public suffix/serial lift also preserves the stricter
CURRENT execution window. Old occupied tools remain excluded by the actual
Base facts and the original remaining-tool set. -/
theorem paidAllows_referenceSuffixJoin (I : Instance) (first : ℕ)
    (before : List (VisibleEvent I)) (after : List (VisibleEvent (I.freshSuffix first)))
    (available childAvailable : Finset I.Tool)
    (base : GuardLift.Base I first before available childAvailable)
    (hused : historyUsed after ⊆ childAvailable)
    (action : Action (I.freshSuffix first))
    (hallow : historyAllowsAction after action)
    (halloc : paidAllocationAllowed (I := I.freshSuffix first) childAvailable action) :
    historyAllowsAction (referenceSuffixHistoryJoin I first before after)
      (referenceSuffixActionLift I first (historyActions before).length action) ∧
    paidAllocationAllowed available (referenceSuffixActionLift I first (historyActions before).length action) := by
  have hr := GuardLift.replayAllowsAction_referenceSuffixJoin I first before after available childAvailable base hused
    action (replayAllows_of_paidAllows (I := I.freshSuffix first) childAvailable after action hallow halloc)
  cases action with
  | review stage => exact ⟨hr, True.intro⟩
  | write stage bit => exact ⟨hr, True.intro⟩
  | advance stage => exact ⟨hr, True.intro⟩
  | allocate handle tool => exact ⟨hr.2, hr.1⟩
  | execute handle tool =>
    refine ⟨⟨?_, hr⟩, True.intro⟩
    rw [historyCursor_referenceSuffixJoin, base.cursor, hallow.1]
    rfl
  | stop => exact ⟨True.intro, True.intro⟩
  | abandon => exact ⟨True.intro, True.intro⟩

theorem paidAllows_of_childPrefix {I : Instance} {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (first : ℕ)
    (before : List (VisibleEvent I)) (available childAvailable : Finset I.Tool)
    (base : GuardLift.Base I first before available childAvailable)
    (childC : Contract (I.freshSuffix first)) (hchildC : childC.IsCurrentPayment)
    (childAccounting : NormalAccounting (I.freshSuffix first))
    (child : AvailablePolicy (input.freshSuffix first) childC childAccounting childAvailable Seed)
    (seed : Seed) (truth : (I.freshSuffix first).Stage → Bool)
    (tapes : ReviewTapes (input.freshSuffix first)) {n : ℕ} {state : State (I.freshSuffix first)}
    (hp : Prefix (input.freshSuffix first) childC .uncapped childAccounting child.val.rule seed truth tapes n state)
    (ha : state.halted = false) :
    historyAllowsAction (referenceSuffixHistoryJoin I first before state.history)
      (referenceSuffixActionLift I first (historyActions before).length (child.val.rule seed state.history)) ∧
    paidAllocationAllowed available
      (referenceSuffixActionLift I first (historyActions before).length (child.val.rule seed state.history)) := by
  obtain ⟨next, hs⟩ := child.val.legal seed truth tapes n state hp ha
  have hallow := historyAllowsAction_of_current_step (input.freshSuffix first) childC hchildC childAccounting
    child.val.rule seed truth tapes hp hs
  have halloc : paidAllocationAllowed (I := I.freshSuffix first) childAvailable
      (child.val.rule seed state.history) := by
    generalize he : child.val.rule seed state.history = action
    cases action <;> try trivial
    exact child.property seed truth tapes n state hp ha _ _ he
  exact paidAllows_referenceSuffixJoin I first before state.history available childAvailable base
    (GuardLift.prefix_historyUsed_subset (input.freshSuffix first) childC childAccounting child.val.rule
      childAvailable child.property seed truth tapes hp) _ hallow halloc

theorem paidGuarded_liftedAfter_join {I : Instance} {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (first : ℕ)
    (before : List (VisibleEvent I)) (available childAvailable : Finset I.Tool)
    (base : GuardLift.Base I first before available childAvailable)
    (childC : Contract (I.freshSuffix first)) (hchildC : childC.IsCurrentPayment)
    (childAccounting : NormalAccounting (I.freshSuffix first))
    (child : AvailablePolicy (input.freshSuffix first) childC childAccounting childAvailable Seed)
    (seed : Seed) (truth : (I.freshSuffix first).Stage → Bool)
    (tapes : ReviewTapes (input.freshSuffix first)) {n : ℕ} {state : State (I.freshSuffix first)}
    (hp : Prefix (input.freshSuffix first) childC .uncapped childAccounting child.val.rule seed truth tapes n state)
    (ha : state.halted = false) :
    paidGuardedRule available (bellmanLiftedAfter first before child.val.rule) seed
      (referenceSuffixHistoryJoin I first before state.history) =
      referenceSuffixActionLift I first (historyActions before).length (child.val.rule seed state.history) := by
  have hh := paidAllows_of_childPrefix input first before available childAvailable base childC hchildC
    childAccounting child seed truth tapes hp ha
  simp only [paidGuardedRule, bellmanLiftedAfter_join, hh.1, hh.2, and_self, ite_true]

end PDMenu
