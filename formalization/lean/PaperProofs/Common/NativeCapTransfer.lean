module

public import PaperProofs.Common.NormalCharges
public import PaperProofs.Common.NativeSeed

/-!
The original sufficient call certificate is checked on a controller that is
already legal without resource caps. It then supplies native legality; that
legality is not an input to the certificate. All reachable prefixes, including
failure and abandonment prefixes, are retained. Contract rights never change.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance} {Seed : Type*}

/-- A hidden world realizing arbitrary truth and tapes, used only in analysis. -/
def replayWorld (input : StatisticalInput I) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) : input.World := fun i => (truth i, tapes i)

theorem prefix_eq_run (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed) (seed : Seed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting policy seed truth tapes n s) :
    run input C mode accounting policy (seed, replayWorld input truth tapes) n = s := by
  induction hp with
  | initial => rfl
  | @next n s next earlier step ih =>
    have ha : (run input C mode accounting policy (seed, replayWorld input truth tapes) n).halted = false := by
      rw [ih]
      exact step_source_active input C mode accounting tapes step
    apply run_succ_of_step input C mode accounting policy (seed, replayWorld input truth tapes) n next ha
    rw [ih]
    exact step

theorem step_uncapped_to_native_of_caps (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I}
    (step : Step input C .uncapped accounting tapes s action next)
    (hcaps : next.ledger.obeysCaps C) :
    Step input C .native accounting tapes s action next := by
  cases step <;> constructor <;> first | assumption | exact Or.inr hcaps

/-- Uniform quota bounds on the actual uncapped interpreter. -/
def ReviewQuotaCertificate (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed) (quota : I.Stage → ℕ) : Prop :=
  ∀ sample n i, (run input C .uncapped accounting policy sample n).ledger.reviews i ≤ (quota i : ℕ∞)

theorem ledger_totalCalls_le_budget (L : Ledger I) (quota : I.Stage → ℕ) (H0 : ℕ)
    (hreviews : ∀ i, L.reviews i ≤ (quota i : ℕ∞)) (hnormal : L.normalCalls ≤ (H0 : ℕ∞))
    (hexecutions : L.executions.length ≤ min I.stageCount I.toolCount) :
    L.totalCalls ≤ ((H0 + ∑ i, quota i + min I.stageCount I.toolCount : ℕ) : ℕ∞) := by
  calc
    L.totalCalls ≤ (H0 : ℕ∞) + ∑ i, (quota i : ℕ∞) + ((min I.stageCount I.toolCount : ℕ) : ℕ∞) :=
      add_le_add (add_le_add hnormal (Finset.sum_le_sum (fun i _ => hreviews i)))
        (ENat.natCast_le_natCast.mpr hexecutions)
    _ = _ := by
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_sum]

theorem legalRule_native_of_prefix_caps (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting policy)
    (hcaps : ∀ (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input) (n : ℕ) (s : State I),
      Prefix input C .uncapped accounting policy seed truth tapes n s → s.ledger.obeysCaps C) :
    LegalRule input C .native accounting policy := by
  intro seed truth tapes n s hp ha
  have hpu := prefix_native_to_uncapped input C accounting policy seed truth tapes hp
  obtain ⟨next, step⟩ := hlegal seed truth tapes n s hpu ha
  exact ⟨next, step_uncapped_to_native_of_caps input C accounting tapes step
    (hcaps seed truth tapes (n + 1) next (.next hpu step))⟩

section Measurable

variable [MeasurableSpace Seed]

/-- The sample-space certificate covers every actual prefix because every
truth/tape pair is realized by a hidden world, without a probability argument. -/
theorem prefix_caps_of_certificates (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : Policy input C .uncapped accounting Seed)
    (quota : I.Stage → ℕ)
    (hreviews : ReviewQuotaCertificate input C accounting policy.rule quota)
    (hnormal : NormalCallCertificate input C .uncapped accounting policy C.normalCallBound)
    (hquota : ∀ i, quota i ≤ C.reviewQuota i)
    (htotal : C.normalCallBound + ∑ i, quota i + min I.stageCount I.toolCount ≤ C.totalCallCap)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting policy.rule seed truth tapes n s) : s.ledger.obeysCaps C := by
  have heq := prefix_eq_run input C .uncapped accounting policy.rule seed truth tapes hp
  let sample := (seed, replayWorld input truth tapes)
  have hr : ∀ i, s.ledger.reviews i ≤ (quota i : ℕ∞) := by
    intro i
    rw [← heq]
    exact hreviews sample n i
  have hn : s.ledger.normalCalls ≤ (C.normalCallBound : ℕ∞) := by
    rw [← heq]
    exact hnormal sample n
  refine ⟨fun i => (hr i).trans (ENat.natCast_le_natCast.mpr (hquota i)), ?_⟩
  exact (ledger_totalCalls_le_budget s.ledger quota C.normalCallBound hr hn
    (Ledger.execution_count_le (prefix_ledgerWellFormed input C .uncapped accounting policy.rule seed truth tapes hp))).trans
      (ENat.natCast_le_natCast.mpr htotal)

def Policy.enforceCaps (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : Policy input C .uncapped accounting Seed)
    (quota : I.Stage → ℕ)
    (hreviews : ReviewQuotaCertificate input C accounting policy.rule quota)
    (hnormal : NormalCallCertificate input C .uncapped accounting policy C.normalCallBound)
    (hquota : ∀ i, quota i ≤ C.reviewQuota i)
    (htotal : C.normalCallBound + ∑ i, quota i + min I.stageCount I.toolCount ≤ C.totalCallCap) :
    Policy input C .native accounting Seed where
  rule := policy.rule
  measurable_rule := policy.measurable_rule
  legal := legalRule_native_of_prefix_caps input C accounting policy.rule policy.legal
    (fun seed truth tapes _ _ hp =>
      prefix_caps_of_certificates input C accounting policy quota hreviews hnormal hquota htotal seed truth tapes hp)

theorem enforceCaps_run_eq (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : Policy input C .uncapped accounting Seed)
    (quota : I.Stage → ℕ)
    (hreviews : ReviewQuotaCertificate input C accounting policy.rule quota)
    (hnormal : NormalCallCertificate input C .uncapped accounting policy C.normalCallBound)
    (hquota : ∀ i, quota i ≤ C.reviewQuota i)
    (htotal : C.normalCallBound + ∑ i, quota i + min I.stageCount I.toolCount ≤ C.totalCallCap)
    (sample : Seed × input.World) (n : ℕ) :
    run input C .native accounting (policy.enforceCaps input C accounting quota hreviews hnormal hquota htotal).rule sample n =
      run input C .uncapped accounting policy.rule sample n :=
  (run_uncapped_eq_native input C accounting policy.rule
    (policy.enforceCaps input C accounting quota hreviews hnormal hquota htotal).legal sample n).symm

theorem enforceCaps_risk_eq (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : Policy input C .uncapped accounting Seed)
    (quota : I.Stage → ℕ)
    (hreviews : ReviewQuotaCertificate input C accounting policy.rule quota)
    (hnormal : NormalCallCertificate input C .uncapped accounting policy C.normalCallBound)
    (hquota : ∀ i, quota i ≤ C.reviewQuota i)
    (htotal : C.normalCallBound + ∑ i, quota i + min I.stageCount I.toolCount ≤ C.totalCallCap)
    (ν : Measure Seed) :
    risk input C .native accounting (policy.enforceCaps input C accounting quota hreviews hnormal hquota htotal).rule ν =
      risk input C .uncapped accounting policy.rule ν :=
  (risk_uncapped_eq_native input C accounting policy.rule
    (policy.enforceCaps input C accounting quota hreviews hnormal hquota htotal).legal ν).symm

theorem enforceCaps_expectedBill_eq (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : Policy input C .uncapped accounting Seed)
    (quota : I.Stage → ℕ)
    (hreviews : ReviewQuotaCertificate input C accounting policy.rule quota)
    (hnormal : NormalCallCertificate input C .uncapped accounting policy C.normalCallBound)
    (hquota : ∀ i, quota i ≤ C.reviewQuota i)
    (htotal : C.normalCallBound + ∑ i, quota i + min I.stageCount I.toolCount ≤ C.totalCallCap)
    (ν : Measure Seed) :
    expectedBill input C .native accounting
      (policy.enforceCaps input C accounting quota hreviews hnormal hquota htotal).rule ν =
      expectedBill input C .uncapped accounting policy.rule ν :=
  (expectedBill_uncapped_eq_native input C accounting policy.rule
    (policy.enforceCaps input C accounting quota hreviews hnormal hquota htotal).legal ν).symm

theorem native_value_le_certified_uncapped (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : Policy input C .uncapped accounting Seed)
    (quota : I.Stage → ℕ)
    (hreviews : ReviewQuotaCertificate input C accounting policy.rule quota)
    (hnormal : NormalCallCertificate input C .uncapped accounting policy C.normalCallBound)
    (hquota : ∀ i, quota i ≤ C.reviewQuota i)
    (htotal : C.normalCallBound + ∑ i, quota i + min I.stageCount I.toolCount ≤ C.totalCallCap)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (δ : ℝ≥0∞)
    (hsafe : risk input C .uncapped accounting policy.rule ν ≤ δ) :
    value input C .native accounting δ ≤ expectedBill input C .uncapped accounting policy.rule ν := by
  let native := policy.enforceCaps input C accounting quota hreviews hnormal hquota htotal
  have hs : risk input C .native accounting native.rule ν ≤ δ := by
    change risk input C .native accounting policy.rule ν ≤ δ
    rw [← risk_uncapped_eq_native input C accounting policy.rule native.legal ν]
    exact hsafe
  have hv := value_le_policy_any_seed input C .native accounting native ν δ hs
  change value input C .native accounting δ ≤ expectedBill input C .native accounting policy.rule ν at hv
  rwa [← expectedBill_uncapped_eq_native input C accounting policy.rule native.legal ν] at hv

end Measurable

end PaperProofs.Common.Native
