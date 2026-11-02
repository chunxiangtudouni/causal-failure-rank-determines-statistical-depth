module

public import PaperProofs.Common.NativeBellmanChargeUpper
public import PaperProofs.Common.NativeBellmanPrivateSeeds
public import PaperProofs.Common.NativePenaltyHeadLower
public import PaperProofs.Common.NativeBellmanExpectation

/-! Epsilon assembly for the original independent-policy Bellman value.
No infimum is assumed attained. All expectation comparisons retain ENNReal
until the independently defined finite value is converted to a real number. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

open PaperProofs.Statistics BellmanPrivateSeeds

variable {I : Instance}

theorem bellman_le_of_forall_real_epsilon {a b : ℝ≥0∞}
    (h : ∀ epsilon : ℝ, 0 < epsilon → a ≤ b + ENNReal.ofReal epsilon) : a ≤ b := by
  apply ENNReal.le_of_forall_pos_le_add
  intro epsilon hepsilon _
  simpa only [ENNReal.ofReal_coe_nnreal] using h (epsilon : ℝ) (NNReal.coe_pos.mpr hepsilon)

theorem bellman_le_of_forall_two_epsilon {a b : ℝ≥0∞}
    (h : ∀ epsilon : ℝ, 0 < epsilon → a ≤ b + ENNReal.ofReal epsilon + ENNReal.ofReal epsilon) : a ≤ b := by
  apply bellman_le_of_forall_real_epsilon
  intro epsilon hepsilon
  have hh := h (epsilon / 2) (by positivity)
  have heq : ENNReal.ofReal (epsilon / 2) + ENNReal.ofReal (epsilon / 2) = ENNReal.ofReal epsilon := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  simpa only [add_assoc, heq] using hh

theorem bellman_mixture_le_of_near {observation goodCost badCost correct wrong : ℝ≥0∞}
    {good bad epsilon : ℝ} (hgood : 0 ≤ good) (horder : good ≤ bad) (hepsilon : 0 ≤ epsilon)
    (hweights : correct + wrong = 1)
    (hgoodCost : goodCost ≤ ENNReal.ofReal (good + epsilon))
    (hbadCost : badCost ≤ ENNReal.ofReal (bad + epsilon)) :
    observation + correct * goodCost + wrong * badCost ≤
      ENNReal.ofReal good + (observation + ENNReal.ofReal (bad - good) * wrong) + ENNReal.ofReal epsilon := by
  have hbad : 0 ≤ bad := hgood.trans horder
  have hsplit : ENNReal.ofReal bad = ENNReal.ofReal good + ENNReal.ofReal (bad - good) := by
    rw [← ENNReal.ofReal_add hgood (sub_nonneg.mpr horder)]
    congr 1
    ring
  calc
    _ ≤ observation + correct * ENNReal.ofReal (good + epsilon) + wrong * ENNReal.ofReal (bad + epsilon) :=
      add_le_add (add_le_add le_rfl (mul_le_mul_right hgoodCost correct))
        (mul_le_mul_right hbadCost wrong)
    _ = observation + (correct + wrong) * ENNReal.ofReal good + ENNReal.ofReal (bad - good) * wrong +
        (correct + wrong) * ENNReal.ofReal epsilon := by
      rw [ENNReal.ofReal_add hgood hepsilon, ENNReal.ofReal_add hbad hepsilon, hsplit]
      ring
    _ = _ := by
      rw [hweights, one_mul, one_mul]
      ac_rfl

theorem bellman_mixture_le_shifted_bayes {Seed : Type*} [MeasurableSpace Seed]
    (E : BinaryExperiment) (ν : Measure Seed) (test : E.AdmissibleRule Seed)
    {goodCost badCost correct : ℝ≥0∞} {good bad epsilon : ℝ}
    (hgood : 0 ≤ good) (horder : good ≤ bad) (hepsilon : 0 ≤ epsilon)
    (hweights : correct + E.bayesError ν test = 1)
    (hgoodCost : goodCost ≤ ENNReal.ofReal (good + epsilon))
    (hbadCost : badCost ≤ ENNReal.ofReal (bad + epsilon)) :
    E.bayesObservationCharge ν test + correct * goodCost + E.bayesError ν test * badCost ≤
      ENNReal.ofReal good + E.bayesObjective ν test (ENNReal.ofReal (bad - good)) + ENNReal.ofReal epsilon := by
  exact bellman_mixture_le_of_near hgood horder hepsilon hweights hgoodCost hbadCost

noncomputable def bellmanIndependentPolicy {Local Good Bad : Type*}
    [MeasurableSpace Local] [MeasurableSpace Good] [MeasurableSpace Bad]
    (input : StatisticalInput I) (head : I.Stage) (available : Finset I.Tool) (repair : Option I.Tool)
    (test : (input.experiment head).AdmissibleRule Local)
    (good : AvailablePolicy (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) available Good)
    (badAvailable : Finset I.Tool)
    (bad : AvailablePolicy (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) badAvailable Bad) :
    AvailablePolicy input (currentRelaxedContract I) (zeroNormalAccounting I) available
      (CombinedSeed Local Good Bad) := by
  let test' : (input.experiment head).AdmissibleRule (CombinedSeed Local Good Bad) :=
    pullbackTest (input.experiment head) test localSeed measurable_localSeed
  let good' : AvailablePolicy (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) available (CombinedSeed Local Good Bad) :=
    pullbackAvailable (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
    (zeroNormalAccounting (I.freshSuffix 1)) available good goodSeed measurable_goodSeed
  let bad' : AvailablePolicy (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) badAvailable (CombinedSeed Local Good Bad) :=
    pullbackAvailable (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
    (zeroNormalAccounting (I.freshSuffix 1)) badAvailable bad badSeed measurable_badSeed
  exact bellmanHeadThenPolicy input (currentRelaxedContract I) rfl rfl (zeroNormalAccounting I)
    head test' available (bellmanPostHeadRaw input head repair good'.val.rule bad'.val.rule)
    (measurable_bellmanPostHeadRaw input head repair good'.val.rule bad'.val.rule
      good'.val.measurable_rule bad'.val.measurable_rule)

set_option maxHeartbeats 1600000 in
theorem healthyPenalty_head_upper (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (available : Finset I.Tool) (price : ℝ) (hprice : 0 ≤ price) :
    input.healthyPenalty 0 available (ENNReal.ofReal price) ≤
      ENNReal.ofReal (input.goodPenaltyReal head available price + (input.experiment head).localValueReal
        (input.badPenaltyReal head available price - input.goodPenaltyReal head available price)) := by
  classical
  let E := input.experiment head
  let g := input.goodPenaltyReal head available price
  let b := input.badPenaltyReal head available price
  have ho := input.penalty_successor_order head available price hprice
  have hj : ENNReal.ofReal (E.localValueReal (b - g)) = E.localValue (ENNReal.ofReal (b - g)) :=
    ENNReal.ofReal_toReal (E.localValue_ofReal_ne_top (b - g))
  change input.healthyPenalty 0 available (ENNReal.ofReal price) ≤ ENNReal.ofReal (g + E.localValueReal (b - g))
  rw [ENNReal.ofReal_add ho.1 (E.localValueReal_nonneg (b - g)), hj]
  apply bellman_le_of_forall_two_epsilon
  intro epsilon hepsilon
  obtain ⟨Local, mLocal, localRest⟩ := exists_localObjective_near E (ENNReal.ofReal (b - g))
    ENNReal.ofReal_ne_top epsilon hepsilon
  let : MeasurableSpace Local := mLocal
  obtain ⟨localLaw, hLocal, test, htest⟩ := localRest
  let : IsProbabilityMeasure localLaw := hLocal
  obtain ⟨Good, mGood, goodRest⟩ := exists_availablePenaltyObjective_near (input.freshSuffix 1)
    (currentRelaxedContract (I.freshSuffix 1)) (zeroNormalAccounting (I.freshSuffix 1)) available
    (ENNReal.ofReal price) ENNReal.ofReal_ne_top epsilon hepsilon
  let : MeasurableSpace Good := mGood
  obtain ⟨goodLaw, hGood, good, hgoodNear⟩ := goodRest
  let : IsProbabilityMeasure goodLaw := hGood
  have hgoodValue : availablePenaltyValue (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) available (ENNReal.ofReal price) = ENNReal.ofReal g := by
    change input.healthyPenalty 1 available (ENNReal.ofReal price) = _
    simpa only [g, StatisticalInput.goodPenaltyReal, hhead, Nat.zero_add] using
      (ofReal_healthyPenaltyReal input 1 available price).symm
  have hgoodCost : penaltyObjective (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
      (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule goodLaw (ENNReal.ofReal price) ≤
        ENNReal.ofReal (g + epsilon) := by
    rw [ENNReal.ofReal_add ho.1 hepsilon.le]
    simpa only [hgoodValue] using hgoodNear.le
  have hweights := BellmanExpectation.correctMass_add_bayesError input head localLaw test
  by_cases hnonempty : (I.eligible head ∩ available).Nonempty
  · obtain ⟨tool, htool, hmin⟩ := exists_badPenaltyReal_minimizer input head available price hnonempty
    obtain ⟨Bad, mBad, badRest⟩ := exists_availablePenaltyObjective_near (input.freshSuffix 1)
      (currentRelaxedContract (I.freshSuffix 1)) (zeroNormalAccounting (I.freshSuffix 1)) (available.erase tool)
      (ENNReal.ofReal price) ENNReal.ofReal_ne_top epsilon hepsilon
    let : MeasurableSpace Bad := mBad
    obtain ⟨badLaw, hBad, bad, hbadNear⟩ := badRest
    let : IsProbabilityMeasure badLaw := hBad
    have hbadValue : availablePenaltyValue (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
        (zeroNormalAccounting (I.freshSuffix 1)) (available.erase tool) (ENNReal.ofReal price) = ENNReal.ofReal b := by
      change input.healthyPenalty 1 (available.erase tool) (ENNReal.ofReal price) = _
      rw [show b = input.healthyPenaltyReal 1 (available.erase tool) price by
        simpa only [b, hhead, Nat.zero_add] using hmin]
      exact (ofReal_healthyPenaltyReal input 1 (available.erase tool) price).symm
    have hbadCost : penaltyObjective (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
        (zeroNormalAccounting (I.freshSuffix 1)) bad.val.rule badLaw (ENNReal.ofReal price) ≤
          ENNReal.ofReal (b + epsilon) := by
      rw [ENNReal.ofReal_add (ho.1.trans ho.2.1) hepsilon.le]
      simpa only [hbadValue] using hbadNear.le
    let policy := bellmanIndependentPolicy input head available (some tool) test good (available.erase tool) bad
    have hinf : input.healthyPenalty 0 available (ENNReal.ofReal price) ≤
        penaltyObjective input (currentRelaxedContract I) .uncapped (zeroNormalAccounting I)
          policy.val.rule (combinedLaw localLaw goodLaw badLaw) (ENNReal.ofReal price) := by
      change availablePenaltyValue input (currentRelaxedContract I) (zeroNormalAccounting I) available _ ≤ _
      exact availablePenaltyValue_le_policy input (currentRelaxedContract I) (zeroNormalAccounting I) available _
        (combinedLaw localLaw goodLaw badLaw) policy
    have hparent := BellmanExpectation.someTool_objective_le input (currentRelaxedContract I) rfl rfl rfl
      (zeroNormalAccounting I) head hhead localLaw goodLaw badLaw test available tool
      (Finset.mem_inter.mp htool).2 (Finset.mem_inter.mp htool).1 good bad (ENNReal.ofReal price)
    have hmix := bellman_mixture_le_shifted_bayes E localLaw test ho.1 ho.2.1 hepsilon.le hweights hgoodCost hbadCost
    have hbound := hinf.trans hparent
    have hbound' := hbound.trans (by simpa only [add_assoc] using hmix)
    exact hbound'.trans (by
      have ht := add_le_add (add_le_add (le_refl (ENNReal.ofReal g)) htest.le) (le_refl (ENNReal.ofReal epsilon))
      simpa only [add_assoc] using ht)
  · let badLaw : Measure Unit := Measure.dirac ()
    let : IsProbabilityMeasure badLaw := by dsimp only [badLaw]; infer_instance
    let bad : AvailablePolicy (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
        (zeroNormalAccounting (I.freshSuffix 1)) ∅ Unit :=
      ⟨abandonPolicy (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
        (zeroNormalAccounting (I.freshSuffix 1)) Unit,
        abandonPolicy_usesOnly (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
          (zeroNormalAccounting (I.freshSuffix 1)) ∅ Unit⟩
    have hb : b = price := by
      simp only [b, StatisticalInput.badPenaltyReal, hnonempty, ↓reduceDIte]
    have hbadCost : ENNReal.ofReal price ≤ ENNReal.ofReal (b + epsilon) := by
      rw [hb]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    let policy := bellmanIndependentPolicy input head available none test good ∅ bad
    let bad' : AvailablePolicy (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
        (zeroNormalAccounting (I.freshSuffix 1)) ∅ (CombinedSeed Local Good Unit) :=
      pullbackAvailable (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
        (zeroNormalAccounting (I.freshSuffix 1)) ∅ bad badSeed measurable_badSeed
    have hinf : input.healthyPenalty 0 available (ENNReal.ofReal price) ≤
        penaltyObjective input (currentRelaxedContract I) .uncapped (zeroNormalAccounting I)
          policy.val.rule (combinedLaw localLaw goodLaw badLaw) (ENNReal.ofReal price) := by
      change availablePenaltyValue input (currentRelaxedContract I) (zeroNormalAccounting I) available _ ≤ _
      exact availablePenaltyValue_le_policy input (currentRelaxedContract I) (zeroNormalAccounting I) available _
        (combinedLaw localLaw goodLaw badLaw) policy
    have hparent := BellmanExpectation.noTool_objective_le input (currentRelaxedContract I) rfl rfl rfl
      (zeroNormalAccounting I) head hhead localLaw goodLaw badLaw test available good bad'.val.rule
      bad'.val.measurable_rule (ENNReal.ofReal price)
    have hmix := bellman_mixture_le_shifted_bayes E localLaw test ho.1 ho.2.1 hepsilon.le hweights hgoodCost hbadCost
    have hbound := hinf.trans hparent
    have hbound' := hbound.trans (by simpa only [add_assoc] using hmix)
    exact hbound'.trans (by
      have ht := add_le_add (add_le_add (le_refl (ENNReal.ofReal g)) htest.le) (le_refl (ENNReal.ofReal epsilon))
      simpa only [add_assoc] using ht)

theorem healthyPenaltyReal_head_upper (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (available : Finset I.Tool) (price : ℝ) (hprice : 0 ≤ price) :
    input.healthyPenaltyReal 0 available price ≤
      input.goodPenaltyReal head available price + (input.experiment head).localValueReal
        (input.badPenaltyReal head available price - input.goodPenaltyReal head available price) := by
  have hs : 0 ≤ input.goodPenaltyReal head available price + (input.experiment head).localValueReal
      (input.badPenaltyReal head available price - input.goodPenaltyReal head available price) :=
    add_nonneg (input.penalty_successor_order head available price hprice).1
      ((input.experiment head).localValueReal_nonneg _)
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (healthyPenalty_head_upper input head hhead available price hprice)
  simpa only [StatisticalInput.healthyPenaltyReal, ENNReal.toReal_ofReal hs] using h

theorem currentPenaltyRecursion_head (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (available : Finset I.Tool) (price : ℝ) (hprice : 0 < price) :
    input.healthyPenaltyReal 0 available price =
      min price (input.goodPenaltyReal head available price + (input.experiment head).localValueReal
        (input.badPenaltyReal head available price - input.goodPenaltyReal head available price)) := by
  apply le_antisymm
  · exact le_min (input.healthyPenaltyReal_le_penalty 0 available price hprice.le)
      (healthyPenaltyReal_head_upper input head hhead available price hprice.le)
  · exact (min_le_right _ _).trans (healthyPenaltyReal_head_lower input head hhead available price hprice.le)

theorem currentPenaltyRecursion (input : StatisticalInput I) : input.CurrentPenaltyRecursion := by
  apply input.currentPenaltyRecursion_iff_freshHeads.mpr
  intro stage available price hprice
  exact currentPenaltyRecursion_head (input.freshSuffix stage.val) (I.freshHead stage) rfl available price hprice

end PaperProofs.Common.Native
