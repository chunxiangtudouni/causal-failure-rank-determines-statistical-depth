module
public import RootPaper_Reference_LocalCost022

/-! Original-input endpoint: prepare once, retain the computed rows, then
answer each history with the measured controller and that row getter.
All native clocks, failed executions and the original numerical quotas are
included. The fixed strong WORD runtime is selected before all instances. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace RootPaper.Reference.Charged
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open RootPaper.Reference RationalControllerComputation
open scoped BigOperators
variable {I : Instance}

def prepareOnce (input : StatisticalInput I) (C : Contract I) (available : Finset I.Tool)
    (budget : Rat) (positive : 0<budget) :
    RootPaper.Prep.Calculation (RootPaper.Prep.NumericalPreparation I)×
      (List (VisibleEvent I)→ControllerCalculation input) :=
  let preparation:=RootPaper.Prep.preparationCalculation input C budget positive
  let quota:=fun stage : I.Stage => RootPaper.B23.readQuota preparation.value.rows stage.val
  (preparation,fun history => controllerCalculation input available budget quota history)

theorem initialize_controller (input : StatisticalInput I) (C : Contract I) (available : Finset I.Tool)
    (budget : Rat) (positive : 0<budget) (history : List (VisibleEvent I)) :
    (prepareOnce input C available budget positive).2 history=preparedController input C available budget positive history := rfl

theorem initialize_value (input : StatisticalInput I) (C : Contract I) (available : Finset I.Tool)
    (budget : Rat) (positive : 0<budget) :
    (prepareOnce input C available budget positive).1.value=
      ⟨computedExponent (I:=I) budget,RootPaper.Prep.originalRows input budget,numericQualification input C budget⟩ :=
  (RootPaper.Prep.preparationCalculation_spec I input C budget positive).1.trans
    (RootPaper.Prep.numericalPreparation_eq I input C budget positive)

theorem initialized_same_rule {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (early : C.reporting=.early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : Rat) (positive : 0<budget) (small : budget≤1/2)
    (seed : Seed) (truth : I.Stage→Bool) (tapes : ReviewTapes input) {n : Nat} {state : State I}
    (hp : Prefix input C .uncapped accounting
      (referenceRule input available budget (some (computedQuotas input budget))) seed truth tapes n state) :
    ((prepareOnce input C available budget positive).2 state.history).action=
      referenceRule input available budget (some (computedQuotas input budget)) seed state.history := by
  rw [initialize_controller]
  exact preparedController_same_rule input C early accounting available budget positive small seed truth tapes hp

def preparationRate : Nat := 1000000*RootPaper.Prep.nativeRate*4097^8+RootPaper.Prep.administrativeCoefficient
def clockRate (runtime : WordRuntime) : Nat := localRate runtime*(dataWidthRate+1)^localDegree runtime
def globalRate (runtime : WordRuntime) : Nat := preparationRate+2*clockRate runtime
def globalDegree (runtime : WordRuntime) : Nat := 3*localDegree runtime+1

theorem globalRate_positive (runtime : WordRuntime) : 0<globalRate runtime := by
  have positive : 0<RootPaper.Prep.administrativeCoefficient := by
    unfold RootPaper.Prep.administrativeCoefficient
    decide
  unfold globalRate preparationRate
  omega

theorem globalDegree_positive (runtime : WordRuntime) : 0<globalDegree runtime := by unfold globalDegree;omega

theorem native_clock_cost (runtime : WordRuntime) {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (early : C.reporting=.early) (accounting : NormalAccounting I)
    (policy : Policy input C .native accounting Seed) (available : Finset I.Tool) (budget : Rat)
    (positive : 0<budget) (small : budget≤1/2) (sample : Seed×input.World) (clock : Nat)
    (within : clock<originalHorizon input budget) :
    let history:=(run input C .native accounting policy.rule sample clock).history
    runningCost runtime (dataWidth input C budget history)
      ((prepareOnce input C available budget positive).2 history)≤
        generalStructureFactor I*clockRate runtime*(arithmeticScale input C budget)^(3*localDegree runtime) := by
  dsimp only
  let history:=(run input C .native accounting policy.rule sample clock).history
  let P:=arithmeticScale input C budget
  let B:=dataWidth input C budget history
  have one : 1≤P := by dsimp only [P,arithmeticScale];omega
  have clockBound : clock≤4*arithmeticScale input C budget := by
    have bound:=horizon_le_scale input C budget
    omega
  have width : B≤dataWidthRate*P^3 := native_dataWidth input C early accounting policy available budget sample clock clockBound
  have original : arithmeticScale input C budget≤B := by dsimp only [B,dataWidth];omega
  have room : history.length≤B := by dsimp only [B,dataWidth];omega
  have measured:=calculationCost_bound runtime input C available budget (preparedGetter input C budget positive)
    history B ⟨positive,small⟩ original room (preparedGetter_visits input C budget positive)
  have powerOne : 1≤P^3 := Nat.one_le_pow _ _ one
  have size : B+1≤(dataWidthRate+1)*P^3 := calc
    B+1≤dataWidthRate*P^3+P^3 := Nat.add_le_add width powerOne
    _=(dataWidthRate+1)*P^3 := by ring
  have power:=Nat.pow_le_pow_left size (localDegree runtime)
  have paid:=measured.trans (Nat.mul_le_mul_left (generalStructureFactor I*localRate runtime) power)
  rw [initialize_controller]
  exact paid.trans_eq (by unfold clockRate;rw [mul_pow,←pow_mul];ring)

noncomputable def totalRunningCost (runtime : WordRuntime) {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (policy : Policy input C .native accounting Seed) (available : Finset I.Tool) (budget : Rat)
    (positive : 0<budget) (sample : Seed×input.World) : Nat :=
  let initialized:=prepareOnce input C available budget positive
  RootPaper.Prep.runningCost (inputSize input C budget) initialized.1+
    ∑ clock∈Finset.range (originalHorizon input budget),
      let state:=run input C .native accounting policy.rule sample clock
      if state.halted then 0 else runningCost runtime (dataWidth input C budget state.history) (initialized.2 state.history)

theorem totalRunningCost_bound (runtime : WordRuntime) {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (early : C.reporting=.early) (accounting : NormalAccounting I)
    (policy : Policy input C .native accounting Seed) (available : Finset I.Tool) (budget : Rat)
    (positive : 0<budget) (small : budget≤1/2) (sample : Seed×input.World) :
    totalRunningCost runtime input C accounting policy available budget positive sample≤
      generalStructureFactor I*globalRate runtime*(arithmeticScale input C budget)^globalDegree runtime := by
  let P:=arithmeticScale input C budget
  let cap:=generalStructureFactor I*clockRate runtime*P^(3*localDegree runtime)
  have one : 1≤P := by dsimp only [P,arithmeticScale];omega
  have each (clock : Nat) (present : clock∈Finset.range (originalHorizon input budget)) :
      (let state:=run input C .native accounting policy.rule sample clock
       if state.halted then 0 else runningCost runtime (dataWidth input C budget state.history)
         ((prepareOnce input C available budget positive).2 state.history))≤cap := by
    dsimp only
    cases halted : (run input C .native accounting policy.rule sample clock).halted with
    | true => exact Nat.zero_le _
    | false =>
      simpa only [Bool.false_eq_true, ↓reduceIte] using
        (native_clock_cost runtime input C early accounting policy available budget positive small
          sample clock (Finset.mem_range.mp present))
  have summed:=Finset.sum_le_sum each
  have sum :
      (∑ clock∈Finset.range (originalHorizon input budget),
        let state:=run input C .native accounting policy.rule sample clock
        if state.halted then 0 else runningCost runtime (dataWidth input C budget state.history)
          ((prepareOnce input C available budget positive).2 state.history))≤originalHorizon input budget*cap := by
    simpa using summed
  have horizon:=(Nat.mul_le_mul_right cap (horizon_le_scale input C budget))
  have loop :
      (∑ clock∈Finset.range (originalHorizon input budget),
        let state:=run input C .native accounting policy.rule sample clock
        if state.halted then 0 else runningCost runtime (dataWidth input C budget state.history)
          ((prepareOnce input C available budget positive).2 state.history))≤
        generalStructureFactor I*(2*clockRate runtime)*P^globalDegree runtime :=
    (sum.trans horizon).trans_eq (by unfold cap globalDegree;rw [pow_succ];ring)
  have preparation:=RootPaper.Prep.preparationCalculation_cost I input C budget positive
  have degree : 12≤globalDegree runtime := by unfold globalDegree localDegree;omega
  have elevated:=preparation.trans (Nat.mul_le_mul_left preparationRate (Nat.pow_le_pow_right one degree))
  have reserve : P^globalDegree runtime≤generalStructureFactor I*P^globalDegree runtime := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (P^globalDegree runtime) (factor_positive I)
  have prep:=elevated.trans (Nat.mul_le_mul_left preparationRate reserve)
  have paid:=Nat.add_le_add prep loop
  exact paid.trans_eq (by dsimp only [totalRunningCost,prepareOnce,globalRate,P];ring)

theorem paper_reference_accounted :
    ∃ runtime : WordRuntime,0<globalRate runtime ∧ 0<globalDegree runtime ∧
      ∀ (I : Instance) (input : StatisticalInput I) (C : Contract I) (available : Finset I.Tool)
        (budget : Rat) (positive : 0<budget) (_small : budget≤1/2),
        (prepareOnce input C available budget positive).1.value=
          ⟨computedExponent (I:=I) budget,RootPaper.Prep.originalRows input budget,numericQualification input C budget⟩ ∧
        (∀ (accounting : NormalAccounting I) (_early : C.reporting=.early) (seed : Unit)
          (truth : I.Stage→Bool) (tapes : ReviewTapes input) (n : Nat) (state : State I),
          Prefix input C .uncapped accounting
            (referenceRule input available budget (some (computedQuotas input budget))) seed truth tapes n state→
          ((prepareOnce input C available budget positive).2 state.history).action=
            referenceRule input available budget (some (computedQuotas input budget)) seed state.history) ∧
        ∀ (accounting : NormalAccounting I) (_early : C.reporting=.early)
          (policy : Policy input C .native accounting Unit) (sample : Unit×input.World),
          totalRunningCost runtime input C accounting policy available budget positive sample≤
            generalStructureFactor I*globalRate runtime*(arithmeticScale input C budget)^globalDegree runtime := by
  obtain ⟨runtime⟩:=wordRuntime_exists
  refine ⟨runtime,globalRate_positive runtime,globalDegree_positive runtime,?_⟩
  intro I input C available budget positive small
  refine ⟨initialize_value input C available budget positive,?_,?_⟩
  · intro accounting early seed truth tapes n state hp
    exact initialized_same_rule input C early accounting available budget positive small seed truth tapes hp
  · intro accounting early policy sample
    exact totalRunningCost_bound runtime input C early accounting policy available budget positive small sample

end RootPaper.Reference.Charged
