module

public import PaperProofs.Common.NativeSeed

/-!
A private computation can fail to return its next native action, after finitely
many paid observations. Such a nonreturn is failure and incurs no invented
infinite observation charge. Its totalization is the native abandon action,
which preserves the full preceding ledger. This is a separate transition
semantics, related to the total-rule interpreter below.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance} {Seed : Type*}

abbrev PartialRule (I : Instance) (Seed : Type*) :=
  Seed → List (VisibleEvent I) → Option (Action I)

def totalizeRule (policy : PartialRule I Seed) : PolicyRule I Seed :=
  fun seed history => (policy seed history).getD .abandon

inductive PartialStep (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input) :
    State I → Option (Action I) → State I → Prop where
  | nonreturn (s : State I) (active : s.halted = false) :
      PartialStep input C mode accounting tapes s none (stopState s true)
  | perform {s s' : State I} {action : Action I}
      (hstep : Step input C mode accounting tapes s action s') :
      PartialStep input C mode accounting tapes s (some action) s'

theorem partialStep_iff_totalized (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    (s s' : State I) (action : Option (Action I)) :
    PartialStep input C mode accounting tapes s action s' ↔
      Step input C mode accounting tapes s (action.getD .abandon) s' := by
  constructor
  · intro h
    cases h with
    | nonreturn active => exact .abandon _ active
    | perform hstep => exact hstep
  · cases action with
    | none => intro h; cases h; exact .nonreturn _ (by assumption)
    | some action => exact PartialStep.perform

inductive PartialPrefix (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : PartialRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input) :
    ℕ → State I → Prop where
  | initial : PartialPrefix input C mode accounting policy seed truth tapes 0 (initial truth)
  | next {n : ℕ} {s s' : State I}
      (earlier : PartialPrefix input C mode accounting policy seed truth tapes n s)
      (step : PartialStep input C mode accounting tapes s (policy seed s.history) s') :
      PartialPrefix input C mode accounting policy seed truth tapes (n + 1) s'

theorem partialPrefix_iff_totalized (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PartialRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input) (n : ℕ) (s : State I) :
    PartialPrefix input C mode accounting policy seed truth tapes n s ↔
      Prefix input C mode accounting (totalizeRule policy) seed truth tapes n s := by
  constructor
  · intro hp
    induction hp with
    | initial => exact .initial
    | next _ step ih =>
      exact .next ih ((partialStep_iff_totalized input C mode accounting tapes _ _ _).mp step)
  · intro hp
    induction hp with
    | initial => exact .initial
    | next _ step ih =>
      exact .next ih ((partialStep_iff_totalized input C mode accounting tapes _ _ _).mpr step)

def PartialLegalRule (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : PartialRule I Seed) : Prop :=
  ∀ (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input) (n : ℕ) (s : State I),
    PartialPrefix input C mode accounting policy seed truth tapes n s → s.halted = false →
      ∃ s', PartialStep input C mode accounting tapes s (policy seed s.history) s'

theorem partialLegalRule_iff_totalized (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PartialRule I Seed) :
    PartialLegalRule input C mode accounting policy ↔
      LegalRule input C mode accounting (totalizeRule policy) := by
  constructor <;> intro h seed truth tapes n s hp ha
  · obtain ⟨s', hs'⟩ := h seed truth tapes n s
      ((partialPrefix_iff_totalized input C mode accounting policy seed truth tapes n s).mpr hp) ha
    exact ⟨s', (partialStep_iff_totalized input C mode accounting tapes _ _ _).mp hs'⟩
  · obtain ⟨s', hs'⟩ := h seed truth tapes n s
      ((partialPrefix_iff_totalized input C mode accounting policy seed truth tapes n s).mp hp) ha
    exact ⟨s', (partialStep_iff_totalized input C mode accounting tapes _ _ _).mpr hs'⟩

noncomputable def partialNext (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (s : State I)
    (action : Option (Action I)) (frontier : Frontier input) : State I :=
  if s.halted then s else
    match action with
    | none => stopState s true
    | some action => nextFromFrontier input C mode accounting s action frontier

theorem partialNext_eq_totalized (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (s : State I)
    (action : Option (Action I)) (frontier : Frontier input) :
    partialNext input C mode accounting s action frontier =
      nextFromFrontier input C mode accounting s (action.getD .abandon) frontier := by
  cases hhalt : s.halted with
  | true => simp [partialNext, nextFromFrontier, hhalt]
  | false =>
    cases action with
    | some action => simp [partialNext, hhalt]
    | none =>
      simp only [partialNext, hhalt, Bool.false_eq_true, ↓reduceIte, Option.getD_none]
      exact (nextFromFrontier_eq_of_step input C mode accounting s (stopState s true)
        .abandon frontier hhalt (.abandon s hhalt)).symm

noncomputable def partialRun (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PartialRule I Seed)
    (sample : Seed × input.World) : ℕ → State I
  | 0 => initial (input.truthAt sample.2)
  | n + 1 =>
    let s := partialRun input C mode accounting policy sample n
    partialNext input C mode accounting s (policy sample.1 s.history) (frontierOf input s sample.2)

theorem partialRun_eq_totalized (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PartialRule I Seed)
    (sample : Seed × input.World) (n : ℕ) :
    partialRun input C mode accounting policy sample n =
      run input C mode accounting (totalizeRule policy) sample n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [partialRun, run, ih, totalizeRule]
    exact partialNext_eq_totalized input C mode accounting _ _ _

/-- A nonreturn fails even if all ordinary slots had already been written. -/
theorem partialNext_nonreturn_failure (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (s : State I)
    (frontier : Frontier input) (hactive : s.halted = false) :
    ¬ (partialNext input C mode accounting s none frontier).ledger.success C := by
  simp only [partialNext, hactive, Bool.false_eq_true, ↓reduceIte, stopState,
    Ledger.success, Bool.true_eq_false, and_false, false_and, not_false_eq_true]

theorem partialNext_nonreturn_bill (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (s : State I)
    (frontier : Frontier input) (hactive : s.halted = false) :
    (partialNext input C mode accounting s none frontier).ledger.actualBill input.fees =
      s.ledger.actualBill input.fees := by
  simp only [partialNext, hactive, Bool.false_eq_true, ↓reduceIte]
  exact stop_actualBill s true input.fees

def partialRunSuccess (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PartialRule I Seed)
    (sample : Seed × input.World) : Prop :=
  ∃ n, (partialRun input C mode accounting policy sample n).halted = true ∧
    (partialRun input C mode accounting policy sample n).ledger.success C

noncomputable def partialRunBill (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PartialRule I Seed)
    (sample : Seed × input.World) : ℝ≥0∞ :=
  ⨆ n, (partialRun input C mode accounting policy sample n).ledger.actualBill input.fees

theorem partialRunSuccess_iff_totalized (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PartialRule I Seed)
    (sample : Seed × input.World) :
    partialRunSuccess input C mode accounting policy sample ↔
      runSuccess input C mode accounting (totalizeRule policy) sample := by
  simp only [partialRunSuccess, runSuccess, partialRun_eq_totalized]

theorem partialRunBill_eq_totalized (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PartialRule I Seed)
    (sample : Seed × input.World) :
    partialRunBill input C mode accounting policy sample =
      runActualBill input C mode accounting (totalizeRule policy) sample := by
  simp only [partialRunBill, runActualBill, partialRun_eq_totalized]

section Measurable

variable [MeasurableSpace Seed]

instance : MeasurableSpace (Option (Action I)) := ⊤
instance : MeasurableSingletonClass (Option (Action I)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

def MeasurablePartialRule (policy : PartialRule I Seed) : Prop :=
  Measurable (fun sample : Seed × List (VisibleEvent I) => policy sample.1 sample.2)

structure PartialPolicy (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (Seed : Type*) [MeasurableSpace Seed] where
  rule : PartialRule I Seed
  measurable_rule : MeasurablePartialRule rule
  legal : PartialLegalRule input C mode accounting rule

def PartialPolicy.totalize (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : PartialPolicy input C mode accounting Seed) : Policy input C mode accounting Seed where
  rule := totalizeRule policy.rule
  measurable_rule := (measurable_of_countable (fun action : Option (Action I) =>
    action.getD .abandon)).comp policy.measurable_rule
  legal := (partialLegalRule_iff_totalized input C mode accounting policy.rule).mp policy.legal

theorem measurable_partialRun (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : PartialPolicy input C mode accounting Seed) (n : ℕ) :
    Measurable (fun sample => partialRun input C mode accounting policy.rule sample n) := by
  have heq : (fun sample => partialRun input C mode accounting policy.rule sample n) =
      (fun sample => run input C mode accounting (totalizeRule policy.rule) sample n) := by
    funext sample
    exact partialRun_eq_totalized input C mode accounting policy.rule sample n
  rw [heq]
  exact measurable_run input C mode accounting _ (policy.totalize input C mode accounting).measurable_rule n

noncomputable def partialRisk (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PartialRule I Seed)
    (ν : Measure Seed) : ℝ≥0∞ :=
  input.seededWorldLaw ν {sample | ¬partialRunSuccess input C mode accounting policy sample}

noncomputable def partialExpectedBill (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PartialRule I Seed)
    (ν : Measure Seed) : ℝ≥0∞ :=
  ∫⁻ sample, partialRunBill input C mode accounting policy sample ∂input.seededWorldLaw ν

theorem partialRisk_eq_totalized (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PartialRule I Seed)
    (ν : Measure Seed) :
    partialRisk input C mode accounting policy ν =
      risk input C mode accounting (totalizeRule policy) ν := by
  simp only [partialRisk, risk, partialRunSuccess_iff_totalized]

theorem partialExpectedBill_eq_totalized (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PartialRule I Seed)
    (ν : Measure Seed) :
    partialExpectedBill input C mode accounting policy ν =
      expectedBill input C mode accounting (totalizeRule policy) ν := by
  simp only [partialExpectedBill, expectedBill, partialRunBill_eq_totalized]

def Policy.partialize (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) : PartialPolicy input C mode accounting Seed where
  rule seed history := some (policy.rule seed history)
  measurable_rule := (measurable_of_countable (fun action : Action I => some action)).comp
    policy.measurable_rule
  legal := by
    apply (partialLegalRule_iff_totalized input C mode accounting _).mpr
    have heq : totalizeRule (fun seed history => some (policy.rule seed history)) = policy.rule := by
      funext seed history
      rfl
    rw [heq]
    exact policy.legal

@[simp] theorem totalize_partialize_rule (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) :
    totalizeRule (policy.partialize input C mode accounting).rule = policy.rule := rfl

theorem value_le_partialPolicy_any_seed (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : PartialPolicy input C mode accounting Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (δ : ℝ≥0∞) (hrisk : partialRisk input C mode accounting policy.rule ν ≤ δ) :
    value input C mode accounting δ ≤ partialExpectedBill input C mode accounting policy.rule ν := by
  rw [partialExpectedBill_eq_totalized]
  apply value_le_policy_any_seed input C mode accounting
    (policy.totalize input C mode accounting) ν δ
  rwa [partialRisk_eq_totalized] at hrisk

/-- Allowing a nonreturned next action changes neither the comparator value nor
its treatment of infinite bills. The infimum is still over genuine policies. -/
noncomputable def partialValue (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (δ : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (SmallSeed : Type), ⨅ (m : MeasurableSpace SmallSeed),
    letI : MeasurableSpace SmallSeed := m
    ⨅ (ν : Measure SmallSeed) (_h : IsProbabilityMeasure ν),
      ⨅ p : {p : PartialPolicy input C mode accounting SmallSeed //
        partialRisk input C mode accounting p.rule ν ≤ δ},
          partialExpectedBill input C mode accounting p.val.rule ν

theorem partialValue_eq_value (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (δ : ℝ≥0∞) :
    partialValue input C mode accounting δ = value input C mode accounting δ := by
  apply le_antisymm
  · unfold value
    refine le_iInf fun SmallSeed => le_iInf fun m => ?_
    let : MeasurableSpace SmallSeed := m
    refine le_iInf fun ν => le_iInf fun hν => ?_
    let : IsProbabilityMeasure ν := hν
    refine le_iInf fun policy => ?_
    let p := policy.val.partialize input C mode accounting
    have hsafe : partialRisk input C mode accounting p.rule ν ≤ δ := by
      simpa only [p, partialRisk_eq_totalized, totalize_partialize_rule] using policy.property
    calc
      _ ≤ partialExpectedBill input C mode accounting p.rule ν :=
        by
          unfold partialValue
          let contender : {p : PartialPolicy input C mode accounting SmallSeed //
              partialRisk input C mode accounting p.rule ν ≤ δ} := ⟨p, hsafe⟩
          exact iInf_le_of_le SmallSeed (iInf_le_of_le m
            (iInf_le_of_le ν (iInf_le_of_le hν (iInf_le_of_le contender le_rfl))))
      _ = _ := by rw [partialExpectedBill_eq_totalized, totalize_partialize_rule]
  · unfold partialValue
    refine le_iInf fun SmallSeed => le_iInf fun m => ?_
    let : MeasurableSpace SmallSeed := m
    refine le_iInf fun ν => le_iInf fun hν => ?_
    let : IsProbabilityMeasure ν := hν
    exact le_iInf fun policy => value_le_partialPolicy_any_seed input C mode accounting
      policy.val ν δ policy.property

end Measurable
end PaperProofs.Common.Native
