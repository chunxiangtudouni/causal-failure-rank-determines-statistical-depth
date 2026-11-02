module

public import PaperProofs.Common.NormalCharges
public import PaperProofs.Common.NativeSeed

/-!
General normal-fee statement of frozen model.tex:51--55 and
price-proofs.tex:302--308.  Fix ONE fee family before taking the full
policy/seed-law/risk infimum in a specified universe u.  No public-trace
factorization, private-seed encoding invariance or finite-cost premise is
required for the original two inequalities.

The family supplies actual measurable normal charges, and the source's C0
bounds are the only normal-fee bounds.  Different seed representations are
not identified by this construction.  It makes no assertion that all
universes are combined into a single infimum, or that a given physical
fee implementation automatically has the original C0 bounds.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.GeneralNormalFees

universe u

variable {I : Instance}

/-- One fixed actual normal-fee family on the ENTIRE same universe-u native
comparator. Charges may depend on the whole actual run; no public-trace
restriction is imposed. The family is not selected inside the infimum. -/
structure FeeFamily (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) where
  charges : (Seed : Type u) → (m : MeasurableSpace Seed) →
    letI : MeasurableSpace Seed := m
    Policy input C mode accounting Seed → NormalCharges input Seed

variable (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
  (accounting : NormalAccounting I)

/-- The full variable-cost comparator at a specified seed universe.
Policies, seed laws and risk constraints are the original ones. -/
noncomputable def universeVariableValue (delta : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (Seed : Type u), ⨅ (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ⨅ (ν : Measure Seed) (_h : IsProbabilityMeasure ν),
      ⨅ policy : {p : Policy input C mode accounting Seed // risk input C mode accounting p.rule ν ≤ delta},
        expectedBill input C mode accounting policy.val.rule ν

noncomputable def FeeFamily.totalValue (family : FeeFamily.{u} input C mode accounting)
    (delta : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (Seed : Type u), ⨅ (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ⨅ (ν : Measure Seed) (_h : IsProbabilityMeasure ν),
      ⨅ policy : {p : Policy input C mode accounting Seed // risk input C mode accounting p.rule ν ≤ delta},
        totalExpectedBill input C mode accounting policy.val (family.charges Seed m policy.val) ν

/-- Exactly the source's successful-run C0 lower bound, uniformly on the
same universe-u comparator. Failed/incomplete runs keep their actual fee. -/
def FeeFamily.SuccessLower (family : FeeFamily.{u} input C mode accounting)
    (C0 : ℝ≥0∞) : Prop :=
  ∀ (Seed : Type u) (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ∀ policy : Policy input C mode accounting Seed,
      SuccessfulNormalChargeLower input C mode accounting policy (family.charges Seed m policy) C0

/-- The already-proved all-seed variable comparison suffices: this lower
direction needs no normal-fee representation theorem. -/
theorem value_le_universeVariableValue (delta : ℝ≥0∞) :
    value input C mode accounting delta ≤ universeVariableValue.{u} input C mode accounting delta := by
  refine le_iInf fun Seed => le_iInf fun m => ?_
  let : MeasurableSpace Seed := m
  refine le_iInf fun ν => le_iInf fun hν => ?_
  let : IsProbabilityMeasure ν := hν
  refine le_iInf fun policy => ?_
  exact value_le_policy_any_seed input C mode accounting policy.val ν delta policy.property

theorem universeVariableValue_le_policy {Seed : Type u} [MeasurableSpace Seed]
    (delta : ℝ≥0∞) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (policy : Policy input C mode accounting Seed) (hsafe : risk input C mode accounting policy.rule ν ≤ delta) :
    universeVariableValue.{u} input C mode accounting delta ≤ expectedBill input C mode accounting policy.rule ν :=
  iInf_le_of_le Seed (iInf_le_of_le ‹MeasurableSpace Seed›
    (iInf_le_of_le ν (iInf_le_of_le ‹IsProbabilityMeasure ν›
      (iInf_le_of_le ⟨policy, hsafe⟩ le_rfl))))

theorem FeeFamily.totalValue_le_policy (family : FeeFamily.{u} input C mode accounting)
    {Seed : Type u} [MeasurableSpace Seed] (delta : ℝ≥0∞)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (policy : Policy input C mode accounting Seed)
    (hsafe : risk input C mode accounting policy.rule ν ≤ delta) :
    family.totalValue input C mode accounting delta ≤
      totalExpectedBill input C mode accounting policy
        (family.charges Seed ‹MeasurableSpace Seed› policy) ν :=
  iInf_le_of_le Seed (iInf_le_of_le ‹MeasurableSpace Seed›
    (iInf_le_of_le ν (iInf_le_of_le ‹IsProbabilityMeasure ν›
      (iInf_le_of_le ⟨policy, hsafe⟩ le_rfl))))

/-- First the stronger bound using the variable infimum of the EXACT SAME
universe-u policy/law/risk class. No seed mapping of actual fees occurs. -/
theorem FeeFamily.totalValue_lower_same_universe
    (family : FeeFamily.{u} input C mode accounting) (delta C0 : ℝ≥0∞)
    (hlower : family.SuccessLower input C mode accounting C0) :
    universeVariableValue.{u} input C mode accounting delta + (1 - delta) * C0 ≤
      family.totalValue input C mode accounting delta := by
  refine le_iInf fun Seed => le_iInf fun m => ?_
  let : MeasurableSpace Seed := m
  refine le_iInf fun ν => le_iInf fun hν => ?_
  let : IsProbabilityMeasure ν := hν
  refine le_iInf fun policy => ?_
  exact (add_le_add (universeVariableValue_le_policy input C mode accounting delta ν policy.val policy.property)
    le_rfl).trans (totalExpectedBill_lower_of_safe input C mode accounting policy.val _ ν delta C0
      policy.property (hlower Seed m policy.val))

theorem FeeFamily.totalValue_lower
    (family : FeeFamily.{u} input C mode accounting) (delta C0 : ℝ≥0∞)
    (hlower : family.SuccessLower input C mode accounting C0) :
    value input C mode accounting delta + (1 - delta) * C0 ≤
      family.totalValue input C mode accounting delta :=
  (add_le_add (value_le_universeVariableValue input C mode accounting delta) le_rfl).trans
    (family.totalValue_lower_same_universe input C mode accounting delta C0 hlower)

/-- The source's C0 upper is needed ONLY on the selected actual safe
controller in the chosen universe. It is not a condition on competitors. -/
theorem FeeFamily.totalValue_upper_of_constructed
    (family : FeeFamily.{u} input C mode accounting) {Seed : Type u} [MeasurableSpace Seed]
    (delta C0 : ℝ≥0∞) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (policy : Policy input C mode accounting Seed) (hsafe : risk input C mode accounting policy.rule ν ≤ delta)
    (hcharge : ConstructedNormalChargeUpper input (family.charges Seed ‹MeasurableSpace Seed› policy) C0) :
    family.totalValue input C mode accounting delta ≤ expectedBill input C mode accounting policy.rule ν + C0 :=
  (family.totalValue_le_policy input C mode accounting delta ν policy hsafe).trans
    (totalExpectedBill_upper_of_constructed input C mode accounting policy _ ν C0 hcharge)

/-- Full original normal-fee sandwich around ANY separately verified fixed
constructed variable-cost bound. No optimal-policy or total-cost conclusion
is hidden in its hypotheses. B22a supplies the reference instance. -/
def NormalFeeClaims : Prop :=
  ∀ (family : FeeFamily.{u} input C mode accounting) (delta C0 : ℝ≥0∞),
    family.SuccessLower input C mode accounting C0 →
      (value input C mode accounting delta + (1 - delta) * C0 ≤
        family.totalValue input C mode accounting delta) ∧
      ∀ (Seed : Type u) (m : MeasurableSpace Seed),
        letI : MeasurableSpace Seed := m
        ∀ (ν : Measure Seed), IsProbabilityMeasure ν →
          ∀ (policy : Policy input C mode accounting Seed) (bound : ℝ≥0∞),
            risk input C mode accounting policy.rule ν ≤ delta →
            expectedBill input C mode accounting policy.rule ν ≤ bound →
            ConstructedNormalChargeUpper input (family.charges Seed m policy) C0 →
              family.totalValue input C mode accounting delta ≤ bound + C0

theorem normalFeeClaims : NormalFeeClaims.{u} input C mode accounting := by
  intro family delta C0 hlower
  refine ⟨family.totalValue_lower input C mode accounting delta C0 hlower, ?_⟩
  intro Seed m
  let : MeasurableSpace Seed := m
  intro ν hν
  let : IsProbabilityMeasure ν := hν
  intro policy bound hsafe hbound hcharge
  exact (family.totalValue_upper_of_constructed input C mode accounting delta C0 ν policy hsafe hcharge).trans
    (add_le_add hbound le_rfl)

end PaperProofs.Common.Native.GeneralNormalFees
