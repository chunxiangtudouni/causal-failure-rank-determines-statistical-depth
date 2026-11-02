module
public import RootPaper_Reference_ChargedBounds015
public import RootPaper_B23_QuotaView003

/-! Whole-run counts on actual native histories. Quotas are read from the
same prepared row list, and their record visits are paid by the controller.
All samples, abandoned paths and the original numerical quota are retained. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace RootPaper.Reference.Charged
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open RootPaper.Reference RationalControllerComputation
open scoped BigOperators
variable {I : Instance}

def preparedGetter (input : StatisticalInput I) (C : Contract I) (budget : Rat) (positive : 0<budget) :
    I.Stage→Nat×Nat := fun stage =>
  RootPaper.B23.readQuota (RootPaper.Prep.preparationCalculation input C budget positive).value.rows stage.val

theorem preparedGetter_values (input : StatisticalInput I) (C : Contract I) (budget : Rat) (positive : 0<budget) :
    (fun stage => (preparedGetter input C budget positive stage).1)=computedQuotas input budget := by
  funext stage
  exact (RootPaper.B23.actual_prepared_quota_view input C budget positive stage).1

theorem preparedGetter_visits (input : StatisticalInput I) (C : Contract I) (budget : Rat) (positive : 0<budget)
    (stage : I.Stage) : (preparedGetter input C budget positive stage).2≤I.stageCount+1 :=
  (RootPaper.B23.actual_prepared_quota_view input C budget positive stage).2

def preparedController (input : StatisticalInput I) (C : Contract I) (available : Finset I.Tool)
    (budget : Rat) (positive : 0<budget) (history : List (VisibleEvent I)) : ControllerCalculation input :=
  controllerCalculation input available budget (preparedGetter input C budget positive) history

theorem preparedController_same_rule {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (early : C.reporting=.early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : Rat) (positive : 0<budget) (small : budget≤1/2)
    (seed : Seed) (truth : I.Stage→Bool) (tapes : ReviewTapes input) {n : Nat} {state : State I}
    (hp : Prefix input C .uncapped accounting
      (referenceRule input available budget (some (computedQuotas input budget))) seed truth tapes n state) :
    (preparedController input C available budget positive state.history).action=
      referenceRule input available budget (some (computedQuotas input budget)) seed state.history := by
  have actual:=controllerCalculation_same_rule input C early accounting available budget positive small
    (preparedGetter input C budget positive) seed truth tapes (n:=n) (state:=state)
  rw [preparedGetter_values] at actual
  exact actual hp

structure WorkCounts where
  queries : Nat
  transitions : Nat
  scalar : Nat
  words : Nat
  administration : Nat

def countsAt (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (quota : I.Stage→Nat×Nat) (history : List (VisibleEvent I)) (halted : Bool) : WorkCounts :=
  if halted then ⟨0,0,0,0,0⟩ else
    let calculation:=controllerCalculation input available budget quota history
    ⟨calculation.ranks.length,rankTicks calculation.ranks,calculation.scalar.length,
      calculation.words.length,calculation.administration⟩

theorem countsAt_bounds (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (quota : I.Stage→Nat×Nat) (history : List (VisibleEvent I)) (halted : Bool) (length quotaVisits : Nat)
    (data : history.length≤length) (getter : ∀ stage,(quota stage).2≤quotaVisits) :
    (countsAt input available budget quota history halted).queries≤2*(length+1) ∧
    (countsAt input available budget quota history halted).transitions≤6*generalStructureFactor I*(length+1) ∧
    (countsAt input available budget quota history halted).scalar≤3*(length+1)^2 ∧
    (countsAt input available budget quota history halted).words≤1 ∧
    (countsAt input available budget quota history halted).administration≤controllerUnits I length quotaVisits := by
  cases halted with
  | true => simp only [countsAt,ite_true];exact ⟨Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by omega,Nat.zero_le _⟩
  | false =>
      simp only [countsAt,Bool.false_eq_true,ite_false]
      have bounded:=controllerCalculation_bounds input available budget quota history quotaVisits getter
      refine ⟨?_,?_,?_,bounded.words,?_⟩
      · exact bounded.queries.trans (by omega)
      · exact bounded.transitions.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right data 1))
      · exact bounded.scalar.trans (Nat.mul_le_mul_left 3
          (Nat.pow_le_pow_left (Nat.add_le_add_right data 1) 2))
      · exact bounded.administration.trans (controllerUnits_mono I quotaVisits data)

noncomputable def wholeCounts {Seed : Type*} [MeasurableSpace Seed] (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : Policy input C mode accounting Seed)
    (available : Finset I.Tool) (budget : Rat) (quota : I.Stage→Nat×Nat)
    (sample : Seed×input.World) (horizon : Nat) : WorkCounts :=
  let perClock := fun clock =>
    let state:=run input C mode accounting policy.rule sample clock
    countsAt input available budget quota state.history state.halted
  ⟨∑ clock∈Finset.range horizon,(perClock clock).queries,
    ∑ clock∈Finset.range horizon,(perClock clock).transitions,
    ∑ clock∈Finset.range horizon,(perClock clock).scalar,
    ∑ clock∈Finset.range horizon,(perClock clock).words,
    ∑ clock∈Finset.range horizon,(perClock clock).administration⟩

private theorem sum_cap (horizon cap : Nat) (items : Nat→Nat)
    (each : ∀ clock∈Finset.range horizon,items clock≤cap) :
    (∑ clock∈Finset.range horizon,items clock)≤horizon*cap := by
  simpa using Finset.sum_le_sum each

theorem wholeCounts_bounds {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (early : C.reporting=.early)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : Policy input C mode accounting Seed)
    (available : Finset I.Tool) (budget : Rat) (quota : I.Stage→Nat×Nat)
    (sample : Seed×input.World) (horizon quotaVisits : Nat)
    (getter : ∀ stage,(quota stage).2≤quotaVisits) :
    let total:=wholeCounts input C mode accounting policy available budget quota sample horizon
    total.queries≤2*horizon*(2*horizon+1) ∧
    total.transitions≤6*generalStructureFactor I*horizon*(2*horizon+1) ∧
    total.scalar≤3*horizon*(2*horizon+1)^2 ∧
    total.words≤horizon ∧
    total.administration≤horizon*controllerUnits I (2*horizon) quotaVisits := by
  have each (clock : Nat) (present : clock∈Finset.range horizon) :=
    countsAt_bounds input available budget quota
      (run input C mode accounting policy.rule sample clock).history
      (run input C mode accounting policy.rule sample clock).halted (2*horizon) quotaVisits
      ((run_history_length input C early mode accounting policy sample clock).trans
        (Nat.mul_le_mul_left 2 (Nat.le_of_lt (Finset.mem_range.mp present)))) getter
  dsimp only [wholeCounts]
  refine ⟨?_,?_,?_,?_,?_⟩
  · have bounded:=sum_cap horizon (2*(2*horizon+1)) _ (fun clock present => (each clock present).1)
    nlinarith
  · have bounded:=sum_cap horizon (6*generalStructureFactor I*(2*horizon+1)) _
      (fun clock present => (each clock present).2.1)
    nlinarith
  · have bounded:=sum_cap horizon (3*(2*horizon+1)^2) _ (fun clock present => (each clock present).2.2.1)
    nlinarith
  · have bounded:=sum_cap horizon 1 _ (fun clock present => (each clock present).2.2.2.1)
    simpa only [Nat.mul_one] using bounded
  · exact sum_cap horizon (controllerUnits I (2*horizon) quotaVisits) _
      (fun clock present => (each clock present).2.2.2.2)

end RootPaper.Reference.Charged
