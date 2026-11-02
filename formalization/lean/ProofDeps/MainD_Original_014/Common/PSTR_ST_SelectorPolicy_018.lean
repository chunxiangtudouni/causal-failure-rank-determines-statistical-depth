module

public import Common.PSTR_ST_SelectorRule_015

/-! Proof-only certified selector policy for uniform variable-fee induction.
The certification contains legal maximum-rank selection, never performance.
The original physical/runtime input is not extended by this auxiliary bundle. -/

@[expose] public section

open MeasureTheory

namespace PaperProofs.Common.Native.PSTRStatistics.MaxSelector

open PaperProofs.Structure.LaminarTree CompactPrice

variable {I : Instance}

structure Certified (I : Instance) (available : Finset I.Tool) where
  choose : Selector I
  spec : Spec I available choose

def Certified.table (I : Instance) (hlaminar : LaminarSchedule I.compatibility)
    (available : Finset I.Tool) : Certified I available :=
  ⟨MaxSelector.table I available, table_spec I hlaminar available⟩

def Certified.restrict {I : Instance} {available : Finset I.Tool}
    (selector : Certified I available) (first : ℕ) (pastUsed : Finset I.Tool) :
    Certified (I.freshSuffix first) (available \ pastUsed) :=
  ⟨MaxSelector.restrict I selector.choose first pastUsed, Spec.restrict selector.spec first pastUsed⟩

theorem rule_uncapped_legal (choose : Selector I) (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (limit : ReferenceObservationLimit I) :
    LegalRule input C .uncapped accounting (rule choose input available budget limit) := by
  intro seed truth tapes n s hp hactive
  let action := candidate choose input available budget limit s.history
  by_cases allow : historyAllowsAction s.history action
  · have next := historyAllowsAction_sound input C hearly accounting
      (rule choose input available budget limit) seed truth tapes hp hactive action allow
    simpa only [rule, action, ite_eq_left allow] using next
  · have next : Step input C .uncapped accounting tapes s .abandon (stopState s true) := .abandon s hactive
    exact ⟨_, by simpa only [rule, action, ite_eq_right allow] using next⟩

def policy (choose : Selector I) (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (limit : ReferenceObservationLimit I) : Policy input C .uncapped accounting Unit where
  rule := rule choose input available budget limit
  measurable_rule :=
    (measurable_of_countable (fun history => rule choose input available budget limit () history)).comp measurable_snd
  legal := rule_uncapped_legal choose input C hearly accounting available budget limit

theorem candidate_allocate_mem (choose : Selector I) (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (spec : Spec I initialAvailable choose)
    (risk : ℚ) (limit : ReferenceObservationLimit I) (history : List (VisibleEvent I))
    (handle : MismatchHandle I) (tool : I.Tool)
    (haction : candidate choose input initialAvailable risk limit history = .allocate handle tool) :
    tool ∈ initialAvailable := by
  cases hp : replay choose input initialAvailable risk history with
  | none => simp only [candidate, hp] at haction; cases haction
  | some cache =>
    cases hh : cache.halted with
    | true => simp only [candidate, hp, hh, ite_true] at haction; cases haction
    | false =>
      simp only [candidate, hp, hh, Bool.false_eq_true, ite_false] at haction
      cases hs : referenceReplayStage I cache with
      | none =>
        rw [hs] at haction
        split_ifs at haction
      | some stage =>
        rw [hs] at haction
        cases hphase : cache.phase with
        | testing =>
          simp only [hphase] at haction
          exact (referenceTestingAction_ne_allocate input initialAvailable risk limit cache stage handle tool haction).elim
        | written => simp only [hphase] at haction; cases haction
        | executed old => simp only [hphase] at haction; cases haction
        | allocated old =>
          simp only [hphase] at haction
          cases hv : referenceVisibleHandle history stage <;> simp only [hv] at haction <;> cases haction
        | reported =>
          simp only [hphase] at haction
          cases hc : referenceReplayCorrect cache stage with
          | true => simp only [hc, ite_true] at haction; cases haction
          | false =>
            simp only [hc, Bool.false_eq_true, ite_false] at haction
            cases hr : referenceReplayRisk risk cache <;> simp only [hr] at haction
            · cases haction
            · cases hv : referenceVisibleHandle history stage <;> simp only [hv] at haction
              · cases haction
              · cases ht : choose stage (historyUsed cache.entryHistory) with
                | none => simp only [ht] at haction; cases haction
                | some selected =>
                  simp only [ht] at haction
                  have heq := Action.allocate.inj haction
                  have hmem := (spec.some stage (historyUsed cache.entryHistory) selected ht).1
                  exact heq.2 ▸ (Finset.mem_sdiff.mp (Finset.mem_inter.mp hmem).2).1

theorem rule_allocate_mem {available : Finset I.Tool} (selector : Certified I available) (input : StatisticalInput I)
    (budget : ℚ) (limit : ReferenceObservationLimit I) (seed : Unit) (history : List (VisibleEvent I))
    (handle : MismatchHandle I) (tool : I.Tool)
    (haction : rule selector.choose input available budget limit seed history = .allocate handle tool) :
    tool ∈ available := by
  let action := candidate selector.choose input available budget limit history
  change (if historyAllowsAction history action then action else .abandon) = .allocate handle tool at haction
  by_cases allow : historyAllowsAction history action
  · rw [ite_eq_left allow] at haction
    exact candidate_allocate_mem selector.choose input available selector.spec budget limit history handle tool haction
  · rw [ite_eq_right allow] at haction
    cases haction

theorem rule_usesOnly {available : Finset I.Tool} (selector : Certified I available) (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (budget : ℚ) (limit : ReferenceObservationLimit I) :
    UsesOnly input C accounting (rule selector.choose input available budget limit) available := by
  intro seed _ _ _ s _ _ handle tool haction
  exact rule_allocate_mem selector input budget limit seed s.history handle tool haction

def Certified.availablePolicy {available : Finset I.Tool} (selector : Certified I available)
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (budget : ℚ) (limit : ReferenceObservationLimit I) :
    AvailablePolicy input C accounting available Unit :=
  ⟨policy selector.choose input C hearly accounting available budget limit,
    rule_usesOnly selector input C accounting budget limit⟩

theorem Certified.table_rule (I : Instance) (hlaminar : LaminarSchedule I.compatibility)
    (available : Finset I.Tool) (input : StatisticalInput I) (budget : ℚ)
    (limit : ReferenceObservationLimit I) :
    rule (Certified.table I hlaminar available).choose input available budget limit =
      tableRule input available budget limit :=
  MaxSelector.rule_table input hlaminar available budget limit

end PaperProofs.Common.Native.PSTRStatistics.MaxSelector
