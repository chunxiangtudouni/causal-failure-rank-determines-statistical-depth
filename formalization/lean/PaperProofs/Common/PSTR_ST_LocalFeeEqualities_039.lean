module

public import PaperProofs.Common.PSTR_ST_SelectorTwoChildCost_033

/-! Local projection and congruence interfaces for the unchanged complete
fee goals. The availability change is an explicit Eq.mp on Spec, and each
rule/cost projection is transported before numerical fee assembly. Legacy
failed034 and diagnostic038 are preserved unchanged. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.PSTRStatistics.MaxSelector.LocalFees

open PaperProofs.Statistics

variable {I : Instance}

def certified_available_eq {before after : Finset I.Tool} (selector : Certified I before)
    (havailable : before = after) : Certified I after :=
  ⟨selector.choose,
    Eq.mp (congrArg (fun tools : Finset I.Tool => Spec I tools selector.choose) havailable) selector.spec⟩

theorem certified_available_eq_choose {before after : Finset I.Tool}
    (selector : Certified I before) (havailable : before = after) :
    (certified_available_eq selector havailable).choose = selector.choose := rfl

def inheritedGood {available : Finset I.Tool} (selector : Certified I available) (first : ℕ) :
    Certified (I.freshSuffix first) available :=
  certified_available_eq (selector.restrict first ∅)
    (show (available \ ∅ : Finset I.Tool) = available from Finset.sdiff_empty)

theorem inheritedGood_choose {available : Finset I.Tool} (selector : Certified I available) (first : ℕ) :
    (inheritedGood selector first).choose = MaxSelector.restrict I selector.choose first ∅ := rfl

def inheritedBad {available : Finset I.Tool} (selector : Certified I available) (first : ℕ) (tool : I.Tool) :
    Certified (I.freshSuffix first) (available.erase tool) :=
  certified_available_eq (selector.restrict first {tool})
    (show (available \ {tool} : Finset I.Tool) = available.erase tool from
      Finset.sdiff_singleton_eq_erase tool available)

theorem inheritedBad_choose {available : Finset I.Tool} (selector : Certified I available)
    (first : ℕ) (tool : I.Tool) :
    (inheritedBad selector first tool).choose = MaxSelector.restrict I selector.choose first {tool} := rfl

theorem policy_rule_projection (choose : Selector I) (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (limit : ReferenceObservationLimit I) :
    (policy choose input C hearly accounting available budget limit).rule =
      MaxSelector.rule choose input available budget limit := rfl

theorem policy_expectedBill_eq_raw (choose : Selector I) (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (ν : Measure Unit) :
    expectedBill input C .uncapped accounting
      (policy choose input C hearly accounting available budget limit).rule ν =
      expectedBill input C .uncapped accounting
        (MaxSelector.rule choose input available budget limit) ν :=
  congrArg (fun candidateRule : PolicyRule I Unit => expectedBill input C .uncapped accounting candidateRule ν)
    (policy_rule_projection choose input C hearly accounting available budget limit)

theorem policy_expectedObservationBill_eq_raw (choose : Selector I) (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (ν : Measure Unit) :
    expectedObservationBill input C .uncapped accounting
      (policy choose input C hearly accounting available budget limit).rule ν =
      expectedObservationBill input C .uncapped accounting
        (MaxSelector.rule choose input available budget limit) ν :=
  congrArg (fun candidateRule : PolicyRule I Unit =>
    expectedObservationBill input C .uncapped accounting candidateRule ν)
    (policy_rule_projection choose input C hearly accounting available budget limit)

theorem raw_expectedBill_le_observation_add (choose : Selector I) (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (ν : Measure Unit) [IsProbabilityMeasure ν] :
    expectedBill input C .uncapped accounting (MaxSelector.rule choose input available budget limit) ν ≤
      expectedObservationBill input C .uncapped accounting
        (MaxSelector.rule choose input available budget limit) ν +
        (min I.stageCount I.toolCount : ℕ) * input.fees.maxCorrection := by
  have hbill := policy_expectedBill_eq_raw choose input C hearly accounting available budget limit ν
  have hobs := policy_expectedObservationBill_eq_raw choose input C hearly accounting available budget limit ν
  have hbound := expectedBill_le_observation_add input C .uncapped accounting
    (policy choose input C hearly accounting available budget limit) ν
  have htype := congrArg₂
    (fun (full observations : ℝ≥0∞) => full ≤ observations +
      (min I.stageCount I.toolCount : ℕ) * input.fees.maxCorrection) hbill hobs
  exact Eq.mp htype hbound

theorem certified_rule_choose_eq {available : Finset I.Tool} (selector : Certified I available)
    (choose : Selector I) (hchoose : selector.choose = choose) (input : StatisticalInput I)
    (budget : ℚ) (limit : ReferenceObservationLimit I) :
    MaxSelector.rule selector.choose input available budget limit =
      MaxSelector.rule choose input available budget limit :=
  congrArg (fun choice : Selector I => MaxSelector.rule choice input available budget limit) hchoose

theorem certified_expectedBill_choose_eq {available : Finset I.Tool} (selector : Certified I available)
    (choose : Selector I) (hchoose : selector.choose = choose) (input : StatisticalInput I)
    (C : Contract I) (accounting : NormalAccounting I) (budget : ℚ)
    (limit : ReferenceObservationLimit I) (ν : Measure Unit) :
    expectedBill input C .uncapped accounting (MaxSelector.rule selector.choose input available budget limit) ν =
      expectedBill input C .uncapped accounting (MaxSelector.rule choose input available budget limit) ν :=
  congrArg (fun candidateRule : PolicyRule I Unit => expectedBill input C .uncapped accounting candidateRule ν)
    (certified_rule_choose_eq selector choose hchoose input budget limit)

theorem goodObservationCost_eq_givenSelector (input : StatisticalInput I) (available : Finset I.Tool)
    (selector : Certified I available) (stage : I.Stage)
    (child : Certified (I.freshSuffix stage.val) available)
    (hchoose : child.choose = MaxSelector.restrict I selector.choose stage.val ∅) (budget : ℚ) :
    BranchCost.goodObservationCost input available selector stage budget =
      Asymptotics.suffixObservationCost input stage available child budget := by
  exact congrArg (fun choice : Selector (I.freshSuffix stage.val) =>
    expectedObservationBill (input.freshSuffix stage.val)
      (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
      (zeroNormalAccounting (I.freshSuffix stage.val))
      (MaxSelector.rule choice (input.freshSuffix stage.val) available budget none) (Measure.dirac ())) hchoose.symm

theorem badObservationCost_eq_givenSelector (input : StatisticalInput I) (available : Finset I.Tool)
    (selector : Certified I available) (stage : I.Stage) (tool : I.Tool)
    (child : Certified (I.freshSuffix stage.val) (available.erase tool))
    (hchoose : child.choose = MaxSelector.restrict I selector.choose stage.val {tool}) (budget : ℚ) :
    BranchCost.badObservationCost input available selector stage tool budget =
      Asymptotics.suffixObservationCost input stage (available.erase tool) child budget := by
  exact congrArg (fun choice : Selector (I.freshSuffix stage.val) =>
    expectedObservationBill (input.freshSuffix stage.val)
      (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
      (zeroNormalAccounting (I.freshSuffix stage.val))
      (MaxSelector.rule choice (input.freshSuffix stage.val) (available.erase tool) budget none)
      (Measure.dirac ())) hchoose.symm

theorem badObservationCost_le_givenSelector_fullBill (input : StatisticalInput I)
    (available : Finset I.Tool) (selector : Certified I available) (stage : I.Stage) (tool : I.Tool)
    (child : Certified (I.freshSuffix stage.val) (available.erase tool))
    (hchoose : child.choose = MaxSelector.restrict I selector.choose stage.val {tool}) (budget : ℚ) :
    BranchCost.badObservationCost input available selector stage tool budget ≤
      expectedBill (input.freshSuffix stage.val)
        (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
        (zeroNormalAccounting (I.freshSuffix stage.val))
        (MaxSelector.rule child.choose (input.freshSuffix stage.val) (available.erase tool) budget none)
        (Measure.dirac ()) := by
  have hcost := badObservationCost_eq_givenSelector input available selector stage tool child hchoose budget
  have hbound : Asymptotics.suffixObservationCost input stage (available.erase tool) child budget ≤
      expectedBill (input.freshSuffix stage.val)
        (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
        (zeroNormalAccounting (I.freshSuffix stage.val))
        (MaxSelector.rule child.choose (input.freshSuffix stage.val) (available.erase tool) budget none)
        (Measure.dirac ()) :=
    expectedObservationBill_le_actual (input.freshSuffix stage.val)
      (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
      (zeroNormalAccounting (I.freshSuffix stage.val))
      (MaxSelector.rule child.choose (input.freshSuffix stage.val) (available.erase tool) budget none) (Measure.dirac ())
  exact hcost.le.trans hbound

noncomputable def rawChildFullBill (input : StatisticalInput I) (available : Finset I.Tool)
    (selector : Certified I available) (first : ℕ) (tool : I.Tool) (budget : ℚ) : ℝ≥0∞ :=
  expectedBill (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first)) .uncapped
    (zeroNormalAccounting (I.freshSuffix first))
    (MaxSelector.rule (MaxSelector.restrict I selector.choose first {tool})
      (input.freshSuffix first) (available.erase tool) budget none) (Measure.dirac ())

theorem rawChildFullBill_index_eq (input : StatisticalInput I) (available : Finset I.Tool)
    (selector : Certified I available) (first next : ℕ) (hindex : first = next)
    (tool : I.Tool) (budget : ℚ) :
    rawChildFullBill input available selector first tool budget =
      rawChildFullBill input available selector next tool budget :=
  congrArg (fun index : ℕ => rawChildFullBill input available selector index tool budget) hindex

theorem givenSelector_fullBill_eq_rawChild (input : StatisticalInput I) (available : Finset I.Tool)
    (selector : Certified I available) (first : ℕ) (tool : I.Tool)
    (child : Certified (I.freshSuffix first) (available.erase tool))
    (hchoose : child.choose = MaxSelector.restrict I selector.choose first {tool}) (budget : ℚ) :
    expectedBill (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first))
      (MaxSelector.rule child.choose (input.freshSuffix first) (available.erase tool) budget none) (Measure.dirac ()) =
      rawChildFullBill input available selector first tool budget :=
  certified_expectedBill_choose_eq child (MaxSelector.restrict I selector.choose first {tool}) hchoose
    (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first))
    (zeroNormalAccounting (I.freshSuffix first)) budget none (Measure.dirac ())


end PaperProofs.Common.Native.PSTRStatistics.MaxSelector.LocalFees
