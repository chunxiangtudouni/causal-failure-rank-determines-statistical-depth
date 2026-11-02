module
public import RootPaper_Reference_ChargedBody011
public import RootPaper_Reference_Counts006

/-! Measured replay stops at the first rejected event. Its successful and
failed paths both retain every performed traversal and primitive call. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace RootPaper.Reference.Charged
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open RootPaper.Reference
open RationalControllerComputation
variable {I : Instance}

def replayCalculation (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) : List (VisibleEvent I)→StepCalculation I
  | [] => ⟨some cache,[],[],4⟩
  | event::rest =>
      let front:=stepCalculation input available budget cache event
      match front.value with
      | none => {front with administration:=front.administration+4}
      | some next =>
          let tail:=replayCalculation input available budget next rest
          ⟨tail.value,front.ranks++tail.ranks,front.scalar++tail.scalar,
            front.administration+tail.administration+8⟩

theorem replayCalculation_projection (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) (history : List (VisibleEvent I)) :
    (replayCalculation input available budget cache history).value=(replayFrom input available budget cache history).result ∧
    (replayCalculation input available budget cache history).ranks=(replayFrom input available budget cache history).ranks ∧
    (replayCalculation input available budget cache history).scalar=(replayFrom input available budget cache history).scalar := by
  induction history generalizing cache with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons event rest ih =>
      have value : (stepCalculation input available budget cache event).value=
          (step input available budget cache event).result :=
        (stepCalculation_value input available budget cache event).trans (step_result input available budget cache event).symm
      have ranks : (stepCalculation input available budget cache event).ranks=
          (step input available budget cache event).ranks := stepCalculation_ranks input available budget cache event
      have scalar : (stepCalculation input available budget cache event).scalar=
          (step input available budget cache event).scalar := stepCalculation_scalar input available budget cache event
      simp only [replayCalculation,replayFrom,←value]
      cases actual : (stepCalculation input available budget cache event).value with
      | none => exact ⟨actual.symm.trans value,ranks,scalar⟩
      | some next =>
          dsimp only
          exact ⟨(ih next).1,by rw [ranks,(ih next).2.1],by rw [scalar,(ih next).2.2]⟩

theorem replayCalculation_value (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) (history : List (VisibleEvent I)) :
    (replayCalculation input available budget cache history).value=
      history.foldlM (referenceAvailableStep input available budget) cache :=
  (replayCalculation_projection input available budget cache history).1.trans
    (replayFrom_eq input available budget cache history)

def stepUnits (I : Instance) (limit : Nat) : Nat :=
  (6*I.toolCount+120)*(3*limit+1)+2*(6*I.toolCount+12)*(I.toolCount+1)+9*I.toolCount+260

theorem stepUnits_mono (I : Instance) {a b : Nat} (ordered : a≤b) : stepUnits I a≤stepUnits I b := by
  unfold stepUnits
  nlinarith

theorem stepAdministration_le (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) (limit : Nat) (bounded : CacheBound limit cache) :
    (stepCalculation input available budget cache event).administration≤stepUnits I limit := by
  have work:=stepCalculation_work input available budget cache event
  dsimp only [CacheBound,stepUnits] at *
  nlinarith

theorem replayCalculation_work (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) (history : List (VisibleEvent I)) (limit : Nat)
    (bounded : CacheBound limit cache) :
    (replayCalculation input available budget cache history).administration≤
      history.length*(stepUnits I (limit+history.length)+8)+4 := by
  induction history generalizing cache limit with
  | nil => simp only [replayCalculation,List.length_nil,Nat.zero_mul,Nat.zero_add];omega
  | cons event rest ih =>
      have front:=(stepAdministration_le input available budget cache event limit bounded).trans
        (stepUnits_mono I (Nat.le_add_right limit (event::rest).length))
      simp only [List.length_cons] at front
      cases actual : (stepCalculation input available budget cache event).value with
      | none =>
          simp only [replayCalculation,actual,List.length_cons]
          nlinarith
      | some next =>
          have nextBound:=step_cacheBound input available budget cache next event limit bounded
            ((stepCalculation_value input available budget cache event).symm.trans actual)
          have tail:=ih next (limit+1) nextBound
          have same : limit+1+rest.length=limit+(event::rest).length := by simp only [List.length_cons];omega
          rw [same] at tail
          simp only [replayCalculation,actual,List.length_cons]
          simp only [List.length_cons] at tail
          nlinarith

theorem replayCalculation_bounds (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) (history : List (VisibleEvent I)) (limit : Nat)
    (bounded : CacheBound limit cache) :
    (∀ next,(replayCalculation input available budget cache history).value=some next→CacheBound (limit+history.length) next) ∧
    (replayCalculation input available budget cache history).ranks.length≤2*history.length ∧
    rankTicks (replayCalculation input available budget cache history).ranks≤6*generalStructureFactor I*history.length ∧
    (replayCalculation input available budget cache history).scalar.length≤history.length*(3*(limit+history.length)+3) ∧
    (replayCalculation input available budget cache history).administration≤
      history.length*(stepUnits I (limit+history.length)+8)+4 := by
  have counted:=replayFrom_bounds input available budget cache history limit bounded
  obtain ⟨value,ranks,scalar⟩:=replayCalculation_projection input available budget cache history
  refine ⟨?_,?_,?_,?_,replayCalculation_work input available budget cache history limit bounded⟩
  · intro next actual
    exact counted.result next (value.symm.trans actual)
  · rw [ranks];exact counted.queries
  · rw [ranks];exact counted.transitions
  · rw [scalar];exact counted.scalar

end RootPaper.Reference.Charged
