module
public import RootPaper_Reference_ChargedController014

/-! Bounds on the actual dedicated calculation, including rejected events
and final guards. Structural queries and statistical calls remain separate;
F is not inserted into either the query count or the local traversal count. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace RootPaper.Reference.Charged
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open RootPaper.Reference RationalControllerComputation
variable {I : Instance}

theorem snapshot_observations_length (cache : ReferenceReplayCache I) :
    (RootPaper.Reference.snapshot cache).observations.length≤cache.seen.length := by
  unfold RootPaper.Reference.snapshot
  cases referenceReplayStage I cache with
  | none => exact Nat.zero_le _
  | some stage => exact List.length_filterMap_le _ _

theorem decisionCalculation_bounds (input : StatisticalInput I) (quota : I.Stage→Nat×Nat)
    (cache : ReferenceReplayCache I) (view : Snapshot I) (data : Kernel I) (quotaVisits : Nat)
    (getter : ∀ stage,(quota stage).2≤quotaVisits) :
    (decisionCalculation input quota cache view data).scalar.length≤1 ∧
    (decisionCalculation input quota cache view data).words.length≤1 ∧
    (decisionCalculation input quota cache view data).administration≤16*(view.observations.length+1)+quotaVisits+32 := by
  unfold decisionCalculation
  cases cache.halted with
  | true => simp
  | false =>
      simp only [Bool.false_eq_true,ite_false]
      cases view.stage with
      | none => exact ⟨by simp,by simp,by simp⟩
      | some stage =>
          dsimp only
          cases cache.phase with
          | testing =>
              obtain ⟨scalar,words,work⟩:=testingCalculation_bounds input quota stage view.observations data
              exact ⟨scalar,words,work.trans (by have bound:=getter stage;omega)⟩
          | written => exact ⟨by simp,by simp,by simp⟩
          | reported => exact ⟨by simp,by simp,by simp⟩
          | allocated tool => exact ⟨by simp,by simp,by simp⟩
          | executed tool => exact ⟨by simp,by simp,by simp⟩

def parseUnits (I : Instance) (length : Nat) : Nat :=
  length*(stepUnits I length+8)+(6*I.toolCount+128)*(3*length+1)+100

def controllerUnits (I : Instance) (length quotaVisits : Nat) : Nat :=
  parseUnits I length+(3*I.toolCount+64)*(3*length+1)+
    2*(6*I.toolCount+12)*(I.toolCount+1)+quotaVisits+256

structure ParsedBounds (length : Nat) (calculation : ParsedCalculation I) : Prop where
  result : ∀ cache view,calculation.value=some (cache,view)→CacheBound length cache
  queries : calculation.ranks.length≤2*length
  transitions : rankTicks calculation.ranks≤6*generalStructureFactor I*length
  scalar : calculation.scalar.length≤length*(3*length+3)
  administration : calculation.administration≤parseUnits I length

theorem parseCalculation_bounds (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (history : List (VisibleEvent I)) :
    ParsedBounds history.length (parseCalculation input available budget history) := by
  obtain ⟨result,queries,ticks,scalar,work⟩:=replayCalculation_bounds input available budget
    (referenceReplayInitial I) history 0 initial_cacheBound
  simp only [Nat.zero_add] at result scalar work
  cases parsed : (replayCalculation input available budget (referenceReplayInitial I) history).value with
  | none =>
      simp only [parseCalculation,parsed]
      refine ⟨?_,queries,ticks,scalar,?_⟩
      · intro cache view impossible
        cases impossible
      · dsimp only
        unfold parseUnits
        omega
  | some cache =>
      have bounded:=result cache parsed
      have ready:=readyCalculation_work cache history
      have paid : (replayCalculation input available budget (referenceReplayInitial I) history).administration+
          (readyCalculation cache history).administration+24≤parseUnits I history.length := by
        dsimp only [CacheBound,parseUnits] at *
        nlinarith
      simp only [parseCalculation,parsed]
      refine ⟨?_,queries,ticks,scalar,paid⟩
      intro next view actual
      split_ifs at actual with valid
      · have same:=congrArg Prod.fst (Option.some.inj actual)
        dsimp only at same
        subst next
        exact bounded

structure ControllerBounds {input : StatisticalInput I} (length quotaVisits : Nat)
    (calculation : ControllerCalculation input) : Prop where
  queries : calculation.ranks.length≤2*(length+1)
  transitions : rankTicks calculation.ranks≤6*generalStructureFactor I*(length+1)
  scalar : calculation.scalar.length≤3*(length+1)^2
  words : calculation.words.length≤1
  administration : calculation.administration≤controllerUnits I length quotaVisits

theorem controllerCalculation_bounds (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (quota : I.Stage→Nat×Nat) (history : List (VisibleEvent I)) (quotaVisits : Nat)
    (getter : ∀ stage,(quota stage).2≤quotaVisits) :
    ControllerBounds history.length quotaVisits (controllerCalculation input available budget quota history) := by
  have replayed:=parseCalculation_bounds input available budget history
  cases parsed : (parseCalculation input available budget history).value with
  | none =>
      simp only [controllerCalculation,parsed]
      refine ⟨?_,?_,?_,by simp,?_⟩
      · dsimp only;have count:=replayed.queries;omega
      · dsimp only;have count:=replayed.transitions;nlinarith
      · dsimp only;have count:=replayed.scalar;nlinarith
      · have count:=replayed.administration
        dsimp only
        unfold controllerUnits
        omega
  | some pair =>
      rcases pair with ⟨cache,view⟩
      have correct:=parseCalculation_view input available budget history cache view parsed
      have bounded:=replayed.result cache view parsed
      obtain ⟨queries,ticks,scalar⟩:=kernel_bounds available budget cache
      have data:=kernelCalculation_value available budget cache view correct
      have dataWork:=kernelCalculation_work available budget cache view
      obtain ⟨testing,words,decisionWork⟩:=decisionCalculation_bounds input quota cache view
        (kernelCalculation available budget cache view).1 quotaVisits getter
      have observations : view.observations.length≤cache.seen.length := by
        rw [correct]
        exact snapshot_observations_length cache
      rw [data] at testing words decisionWork
      simp only [controllerCalculation,parsed]
      rw [data]
      refine ⟨?_,?_,?_,words,?_⟩
      · dsimp only
        simp only [List.length_append]
        have earlier:=replayed.queries
        omega
      · dsimp only
        have earlier:=replayed.transitions
        simp only [rankTicks,List.map_append,List.sum_append] at *
        nlinarith
      · dsimp only
        simp only [List.length_append]
        have earlier:=replayed.scalar
        dsimp only [CacheBound] at bounded
        nlinarith
      · have earlier:=replayed.administration
        dsimp only
        dsimp only [CacheBound,controllerUnits] at *
        nlinarith

theorem controllerUnits_mono (I : Instance) {a b : Nat} (quotaVisits : Nat) (ordered : a≤b) :
    controllerUnits I a quotaVisits≤controllerUnits I b quotaVisits := by
  have units:=stepUnits_mono I ordered
  have replayed:=Nat.mul_le_mul ordered (Nat.add_le_add_right units 8)
  dsimp only [controllerUnits,parseUnits] at *
  nlinarith

end RootPaper.Reference.Charged
