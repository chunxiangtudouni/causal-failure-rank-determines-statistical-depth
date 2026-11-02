module

public import PaperProofs.Paid.PenaltyProgram
public import PaperProofs.Common.NativeBellmanUpper
public import PaperProofs.Common.ReferenceController

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {I : Instance}

theorem exists_paidPenaltyObjective_near (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (penalty : ℝ≥0∞) (hp : penalty ≠ ⊤)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ (Seed : Type) (m : MeasurableSpace Seed),
      letI : MeasurableSpace Seed := m
      ∃ (ν : Measure Seed) (_hν : IsProbabilityMeasure ν)
        (policy : Policy input C .uncapped accounting Seed),
        paidPenaltyObjective input C accounting policy.rule ν penalty <
          paidPenaltyValue input C accounting penalty + ENNReal.ofReal epsilon := by
  have hfinite := ne_top_of_le_ne_top hp (paidPenaltyValue_le_penalty input C accounting penalty)
  have hnear := ENNReal.lt_add_right hfinite (ENNReal.ofReal_pos.mpr hepsilon).ne'
  conv_lhs at hnear => unfold paidPenaltyValue
  simpa only [iInf_lt_iff] using hnear

def paidAllocationAllowed (available : Finset I.Tool) : Action I → Prop
  | .allocate _ tool => tool ∈ available
  | _ => True

instance paidAllocationAllowed_decidable (available : Finset I.Tool) (action : Action I) :
    Decidable (paidAllocationAllowed available action) := by
  cases action <;> dsimp only [paidAllocationAllowed] <;> infer_instance

/-- A current-window-compatible replacement for the old deferred-only replay
guard. Its data are only the public history and fixed original available set. -/
def paidGuardedRule {Seed : Type*} (available : Finset I.Tool) (raw : PolicyRule I Seed) : PolicyRule I Seed :=
  fun seed history => if historyAllowsAction history (raw seed history) ∧
    paidAllocationAllowed available (raw seed history) then raw seed history else .abandon

theorem measurable_paidGuardedRule {Seed : Type*} [MeasurableSpace Seed]
    (available : Finset I.Tool) (raw : PolicyRule I Seed) (hm : MeasurableRule raw) :
    MeasurableRule (paidGuardedRule available raw) := by
  apply measurable_from_prod_countable_left
  intro history
  exact (measurable_of_countable (fun action : Action I =>
      if historyAllowsAction history action ∧ paidAllocationAllowed available action then action else .abandon)).comp
    (hm.comp (measurable_id.prodMk measurable_const))

theorem paidGuardedRule_legal {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (raw : PolicyRule I Seed) :
    LegalRule input C .uncapped accounting (paidGuardedRule available raw) := by
  intro seed truth tapes n state hp hactive
  by_cases allowed : historyAllowsAction state.history (raw seed state.history) ∧
      paidAllocationAllowed available (raw seed state.history)
  · obtain ⟨next, hs⟩ := historyAllowsAction_sound input C hearly accounting
      (paidGuardedRule available raw) seed truth tapes hp hactive (raw seed state.history) allowed.1
    exact ⟨next, by simpa only [paidGuardedRule, allowed, and_self, ite_true] using hs⟩
  · exact ⟨stopState state true, by
      simpa only [paidGuardedRule, allowed, ite_false] using (Step.abandon (input := input) (C := C)
        (mode := ResourceMode.uncapped) (accounting := accounting) (tapes := tapes) state hactive)⟩

theorem paidGuardedRule_usesOnly {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (raw : PolicyRule I Seed) :
    UsesOnly input C accounting (paidGuardedRule available raw) available := by
  intro seed truth tapes n state _hp _ha handle tool haction
  by_cases allowed : historyAllowsAction state.history (raw seed state.history) ∧
      paidAllocationAllowed available (raw seed state.history)
  · have heq : raw seed state.history = .allocate handle tool := by
      simpa only [paidGuardedRule, allowed, and_self, ite_true] using haction
    simpa only [heq, paidAllocationAllowed] using allowed.2
  · simp only [paidGuardedRule, allowed, ite_false] at haction
    cases haction

theorem historyAllowsAction_of_current_step {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentPayment) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {state next : State I} (hp : Prefix input C .uncapped accounting rule seed truth tapes n state)
    {action : Action I} (hs : Step input C .uncapped accounting tapes state action next) :
    historyAllowsAction state.history action := by
  have hr := replayAllowsAction_complete input C hC.1.1 hC.1.2 .uncapped accounting
    rule seed truth tapes hp Finset.univ hs (by intro _ tool _; exact Finset.mem_univ tool)
  cases action with
  | review stage => exact hr
  | write stage bit => exact hr
  | advance stage => exact hr
  | stop => trivial
  | abandon => trivial
  | allocate handle tool => exact hr.2
  | execute handle tool =>
    refine ⟨?_, hr⟩
    rw [prefix_historyCursor input C .uncapped accounting rule seed truth tapes hp]
    cases hs with
    | execute _handle _tool _active _valid _compatible _committed _unused _uncorrected window _resources =>
      exact window hC.2

theorem paidGuardedRule_eq_of_step {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentPayment) (accounting : NormalAccounting I) (rule raw : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {state next : State I} (hp : Prefix input C .uncapped accounting rule seed truth tapes n state)
    (available : Finset I.Tool) (hs : Step input C .uncapped accounting tapes state (raw seed state.history) next)
    (havailable : ∀ handle tool, raw seed state.history = .allocate handle tool → tool ∈ available) :
    paidGuardedRule available raw seed state.history = raw seed state.history := by
  have hallow := historyAllowsAction_of_current_step input C hC accounting rule seed truth tapes hp hs
  have halloc : paidAllocationAllowed available (raw seed state.history) := by
    generalize he : raw seed state.history = action
    cases action <;> try trivial
    exact havailable _ _ he
  simp only [paidGuardedRule, hallow, halloc, and_self, ite_true]

noncomputable def paidHeadThenRule {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (head : I.Stage) (test : (input.experiment head).AdmissibleRule Seed)
    (available : Finset I.Tool) (after : PolicyRule I Seed) : PolicyRule I Seed :=
  paidGuardedRule available (bellmanHeadThenRaw input head test after)

noncomputable def paidHeadThenPolicy {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hC : C.IsCurrentPayment) (accounting : NormalAccounting I)
    (head : I.Stage) (test : (input.experiment head).AdmissibleRule Seed)
    (available : Finset I.Tool) (after : PolicyRule I Seed) (hafter : MeasurableRule after) :
    AvailablePolicy input C accounting available Seed :=
  ⟨{rule := paidHeadThenRule input head test available after
    measurable_rule := measurable_paidGuardedRule available _ (by
      apply measurable_from_prod_countable_left
      intro history
      dsimp only [bellmanHeadThenRaw]
      split_ifs
      · exact (measurable_bellmanHeadNext input head test).comp (measurable_id.prodMk measurable_const)
      · exact hafter.comp (measurable_id.prodMk measurable_const))
    legal := paidGuardedRule_legal input C hC.1.1 accounting available _},
    paidGuardedRule_usesOnly input C accounting available _⟩

end PDMenu
