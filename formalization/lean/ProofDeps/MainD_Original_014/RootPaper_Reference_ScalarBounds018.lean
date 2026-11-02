module
public import RootPaper_Reference_Depths017
public import RootPaper_TableCost_Fees009

/-! Consume the shared, closed scalar algorithms and operand-provenance
lemmas. No scalar fee, width, positivity or rank-depth oracle is introduced. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace RootPaper.Reference.Charged
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open RootPaper.Reference RationalControllerComputation PSTRWordBool
open RootPaper.TableCost (CallBound budgetWork_callBound)
variable {I : Instance}

theorem callBound_mono {small large first last : Nat} (width : small≤large) (depth : first≤last)
    (call : ScalarCall I) (bounded : CallBound small first call) : CallBound large last call := by
  cases call with
  | budgetVisit kind error risk => exact ⟨bounded.1.trans width,bounded.2.trans depth⟩
  | half risk => exact bounded.trans width
  | target risk n => exact ⟨bounded.1,bounded.2.1,bounded.2.2.1.trans width,bounded.2.2.2.trans depth⟩
  | badRisk risk target => exact ⟨bounded.1.trans width,bounded.2.trans (by omega)⟩
  | word stage target n => exact bounded.elim

theorem targetWork_callBound (kind : ReferenceBudgetCase) (risk : Rat) (S D : Nat)
    (positive : 0<risk) (width : RatInput.Encoder.fieldSize risk≤S)
    (depth : RootB236.RiskFold.caseDepth kind≤D) (call : ScalarCall I)
    (member : call∈(targetWork kind risk).2) : CallBound S D call := by
  cases kind with
  | infiniteRank => cases member
  | noTool =>
      have same : call=.half risk := List.mem_singleton.mp member
      subst call
      exact width
  | finiteBad d =>
      have same : call=.target risk d.val := List.mem_singleton.mp member
      subst call
      exact ⟨positive,d.pos,width,depth⟩

theorem kernel_callBound (available : Finset I.Tool) (budget : Rat) (cache : ReferenceReplayCache I)
    (valid : 0<budget ∧ budget≤1/2) (depths : EventDepths I cache.events)
    (call : ScalarCall I) (member : call∈(kernel I available budget cache).scalar) :
    CallBound (2*RatInput.Encoder.fieldSize budget+6*cache.events.length+4) (I.stageCount+1) call := by
  have halfBound : CallBound (2*RatInput.Encoder.fieldSize budget+6*cache.events.length+4)
      (I.stageCount+1) (.half (I:=I) budget) := by
    change RatInput.Encoder.fieldSize budget≤_
    omega
  have budgetBound (called : ScalarCall I) (present : called∈(budgetWork (I:=I) (budget/2) cache.events).2) :=
    budgetWork_callBound budget cache.events (I.stageCount+1) valid depths called present
  unfold kernel at member
  cases currentStage : referenceReplayStage I cache with
  | none =>
      rw [currentStage] at member
      rcases List.mem_cons.mp member with same|present
      · subst call;exact halfBound
      · exact budgetBound call present
  | some stage =>
      rw [currentStage] at member
      dsimp only at member
      rcases List.mem_cons.mp member with same|present
      · subst call;exact halfBound
      · rcases List.mem_append.mp present with replayed|target
        · exact budgetBound call replayed
        · cases stopped : cache.halted || decide (cache.phase≠.testing) with
          | true => simp only [stopped,ite_true,List.not_mem_nil] at target
          | false =>
              simp only [stopped,Bool.false_eq_true,ite_false] at target
              cases classified : (kindWork I available stage (historyUsed cache.entryHistory)).classification with
              | none => simp only [classified,List.not_mem_nil] at target
              | some kind =>
                  cases current : (budgetWork (I:=I) (budget/2) cache.events).1 with
                  | none => simp only [classified,current,List.not_mem_nil] at target
                  | some risk =>
                      simp only [classified,current] at target
                      by_cases guard : 0<risk ∧ risk≤1/4 ∧ cache.events.length≤I.stageCount
                      · rw [ite_eq_left guard] at target
                        have path : referenceBudgetPath (budget/2) cache.events=some risk :=
                          (budgetWork_value (I:=I) (budget/2) cache.events).symm.trans current
                        have width:=RootB236.RiskFold.original_path_width budget cache.events risk valid path
                        exact targetWork_callBound kind risk _ _ guard.1 width
                          (kindWork_depth available stage (historyUsed cache.entryHistory) kind classified) call target
                      · rw [ite_eq_right guard] at target
                        cases target

theorem replayCalculation_callBound (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) (history : List (VisibleEvent I)) (limit : Nat)
    (valid : 0<budget ∧ budget≤1/2) (bounded : CacheBound limit cache) (depths : EventDepths I cache.events)
    (call : ScalarCall I) (member : call∈(replayCalculation input available budget cache history).scalar) :
    CallBound (2*RatInput.Encoder.fieldSize budget+6*(limit+history.length)+4) (I.stageCount+1) call := by
  induction history generalizing cache limit with
  | nil => cases member
  | cons event rest ih =>
      have front (called : ScalarCall I) (present : called∈(stepCalculation input available budget cache event).scalar) :
          CallBound (2*RatInput.Encoder.fieldSize budget+6*(limit+(event::rest).length)+4) (I.stageCount+1) called := by
        rw [stepCalculation_scalar] at present
        exact callBound_mono (by have reports:=bounded.2.2;omega) (Nat.le_refl _)
          called (kernel_callBound available budget cache valid depths called present)
      dsimp only [replayCalculation] at member
      cases selected : (stepCalculation input available budget cache event).value with
      | none =>
          rw [selected] at member
          exact front call member
      | some child =>
          rw [selected] at member
          rcases List.mem_append.mp member with earlier|later
          · exact front call earlier
          · have childBound:=step_cacheBound input available budget cache child event limit bounded
              ((stepCalculation_value input available budget cache event).symm.trans selected)
            have childDepth:=stepCalculation_depths input available budget cache event child depths selected
            have result:=ih child (limit+1) childBound childDepth later
            have same : limit+1+rest.length=limit+(event::rest).length := by simp only [List.length_cons];omega
            rw [same] at result
            exact result

theorem parseCalculation_callBound (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (history : List (VisibleEvent I)) (valid : 0<budget ∧ budget≤1/2) (call : ScalarCall I)
    (member : call∈(parseCalculation input available budget history).scalar) :
    CallBound (2*RatInput.Encoder.fieldSize budget+6*history.length+4) (I.stageCount+1) call := by
  have actual : (parseCalculation input available budget history).scalar=
      (replayCalculation input available budget (referenceReplayInitial I) history).scalar := by
    dsimp only [parseCalculation]
    cases (replayCalculation input available budget (referenceReplayInitial I) history).value <;> rfl
  rw [actual] at member
  simpa only [Nat.zero_add] using replayCalculation_callBound input available budget
    (referenceReplayInitial I) history 0 valid initial_cacheBound
    (by intro event impossible;cases impossible) call member

end RootPaper.Reference.Charged
