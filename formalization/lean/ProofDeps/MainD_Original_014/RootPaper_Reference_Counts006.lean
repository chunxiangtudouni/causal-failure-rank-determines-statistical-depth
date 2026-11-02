module
public import RootPaper_Reference_Decision004
public import RootPaper_Reference_Prefix005

/-! Separate structural and statistical work bounds of the concrete cache
algorithm. Counters are read from its recursive records, not defined as F
times a polynomial. These bounds do not identify runs of different selectors. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace RootPaper.Reference
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open RationalControllerComputation
variable {I : Instance}

def rankTicks (calls : List (RankCall I)) : Nat := (calls.map RankCall.transitions).sum

theorem kernel_bounds (available : Finset I.Tool) (budget : Rat) (cache : ReferenceReplayCache I) :
    (kernel I available budget cache).ranks.length≤2 ∧
    rankTicks (kernel I available budget cache).ranks≤6*generalStructureFactor I ∧
    (kernel I available budget cache).scalar.length≤3*cache.events.length+2 := by
  have arithmetic:=budgetWork_calls (I:=I) (budget/2) cache.events
  unfold kernel
  cases current : referenceReplayStage I cache with
  | none =>
      simp only [List.length_nil,rankTicks,List.map_nil,List.sum_nil,List.length_cons]
      omega
  | some stage =>
      have ranks:=kindWork_calls available stage (historyUsed cache.entryHistory)
      let selected : Option Rat×List (ScalarCall I):=
        if cache.halted || decide (cache.phase≠.testing) then (none,[]) else
          match (kindWork I available stage (historyUsed cache.entryHistory)).classification,
              (budgetWork (I:=I) (budget/2) cache.events).1 with
          | some kind,some risk => if 0<risk ∧ risk≤1/4 ∧ cache.events.length≤I.stageCount
              then targetWork kind risk else (none,[])
          | _,_ => (none,[])
      have targetBound : selected.2.length≤1 := by
        dsimp only [selected]
        repeat' split
        all_goals first | exact targetWork_calls _ _ | simp
      change (kindWork I available stage (historyUsed cache.entryHistory)).ranks.length≤2 ∧
        rankTicks (kindWork I available stage (historyUsed cache.entryHistory)).ranks≤6*generalStructureFactor I ∧
        (.half budget::(budgetWork (I:=I) (budget/2) cache.events).2++selected.2).length≤3*cache.events.length+2
      refine ⟨ranks.1,ranks.2,?_⟩
      simp only [List.length_cons,List.length_append]
      omega

structure ReplayBounds (limit count : Nat) (execution : Execution I) : Prop where
  result : ∀ cache,execution.result=some cache→CacheBound (limit+count) cache
  queries : execution.ranks.length≤2*count
  transitions : rankTicks execution.ranks≤6*generalStructureFactor I*count
  scalar : execution.scalar.length≤count*(3*(limit+count)+3)
  reads : execution.historyReads.length≤8*count
  scanned : execution.historyReads.sum≤8*count*(limit+count)
  copied : execution.copied≤count*(2*(limit+count)+2)

theorem step_bounds (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) (limit : Nat)
    (bounded : CacheBound limit cache) : ReplayBounds limit 1 (step input available budget cache event) := by
  obtain ⟨queries,transitions,scalar⟩:=kernel_bounds available budget cache
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro next actual
    have nextBound:=step_cacheBound input available budget cache next event limit bounded
      ((step_result input available budget cache event).symm.trans actual)
    exact nextBound
  · exact queries
  · simpa only [step,Nat.mul_one] using transitions
  · change (kernel I available budget cache).scalar.length≤1*(3*(limit+1)+3)
    have reports:=bounded.2.2
    omega
  · change [cache.seen.length,cache.seen.length,cache.seen.length,cache.seen.length,
      cache.seen.length,cache.seen.length,cache.seen.length,cache.entryHistory.length].length≤8*1
    change (8 : Nat)≤8
    omega
  · change [cache.seen.length,cache.seen.length,cache.seen.length,cache.seen.length,
      cache.seen.length,cache.seen.length,cache.seen.length,cache.entryHistory.length].sum≤8*1*(limit+1)
    simp only [List.sum_cons,List.sum_nil]
    dsimp only [CacheBound] at bounded
    omega
  · change cache.seen.length+cache.events.length+2≤1*(2*(limit+1)+2)
    dsimp only [CacheBound] at bounded
    omega

theorem replayFrom_bounds (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) (history : List (VisibleEvent I)) (limit : Nat)
    (bounded : CacheBound limit cache) :
    ReplayBounds limit history.length (replayFrom input available budget cache history) := by
  induction history generalizing cache limit with
  | nil =>
      refine ⟨?_,by simp [replayFrom],by simp [replayFrom,rankTicks],by simp [replayFrom],
        by simp [replayFrom],by simp [replayFrom],by simp [replayFrom]⟩
      intro next actual
      have same : cache=next := Option.some.inj actual
      subst next
      exact bounded
  | cons event rest ih =>
      have front:=step_bounds input available budget cache event limit bounded
      cases actual : (step input available budget cache event).result with
      | none =>
          simp only [replayFrom,actual]
          refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
          · intro next impossible
            rw [actual] at impossible
            cases impossible
          · have bound:=front.queries
            simp only [List.length_cons]
            omega
          · have bound:=front.transitions
            simp only [List.length_cons]
            nlinarith
          · have bound:=front.scalar
            simp only [List.length_cons]
            nlinarith
          · have bound:=front.reads
            simp only [List.length_cons]
            omega
          · have bound:=front.scanned
            simp only [List.length_cons]
            nlinarith
          · have bound:=front.copied
            simp only [List.length_cons]
            nlinarith
      | some next =>
          have tail:=ih next (limit+1) (front.result next actual)
          simp only [replayFrom,actual]
          refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
          · intro final finished
            have bound:=tail.result final finished
            convert bound using 1
            simp only [List.length_cons]
            omega
          · have first:=front.queries
            have last:=tail.queries
            simp only [List.length_append,List.length_cons]
            omega
          · have first:=front.transitions
            have last:=tail.transitions
            simp only [rankTicks,List.map_append,List.sum_append,List.length_cons] at *
            nlinarith
          · have first:=front.scalar
            have last:=tail.scalar
            simp only [List.length_append,List.length_cons]
            nlinarith
          · have first:=front.reads
            have last:=tail.reads
            simp only [List.length_append,List.length_cons]
            omega
          · have first:=front.scanned
            have last:=tail.scanned
            simp only [List.sum_append,List.length_cons]
            nlinarith
          · have first:=front.copied
            have last:=tail.copied
            simp only [List.length_cons]
            nlinarith

end RootPaper.Reference
