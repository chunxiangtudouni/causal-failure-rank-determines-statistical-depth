module
public import Paid.PDCompute_CoreBranch_Finish_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
@[expose] public section
namespace PDCompute.CoreBranch
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open RootD27.Core PDLower.CoreSearch PDCompute.CoreSearchLoop

def middleRisk (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve) : ℚ :=
  P.solveRisk (P.cachedSolveMultiplier P.endpointCache fee (midpointPenalty lower upper))

theorem bisect_equal (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (equal : middleRisk P fee lower upper=P.certificate.risk) :
    updatedSourceState P fee (midpointPenalty lower upper) lower upper false true=
      P.cachedBisect P.endpointCache fee (.bracket lower upper) := by
  unfold middleRisk midpointPenalty at equal
  unfold cachedBisect
  dsimp only
  rw [ite_eq_left equal]
  rfl

theorem bisect_lower (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (unequal : ¬middleRisk P fee lower upper=P.certificate.risk)
    (greater : P.certificate.risk<middleRisk P fee lower upper) :
    updatedSourceState P fee (midpointPenalty lower upper) lower upper false false=
      P.cachedBisect P.endpointCache fee (.bracket lower upper) := by
  unfold middleRisk midpointPenalty at unequal greater
  unfold cachedBisect
  dsimp only
  rw [ite_eq_right unequal,ite_eq_left greater]
  rfl

theorem bisect_upper (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (unequal : ¬middleRisk P fee lower upper=P.certificate.risk)
    (notGreater : ¬P.certificate.risk<middleRisk P fee lower upper) :
    updatedSourceState P fee (midpointPenalty lower upper) lower upper true false=
      P.cachedBisect P.endpointCache fee (.bracket lower upper) := by
  unfold middleRisk midpointPenalty at unequal notGreater
  unfold cachedBisect
  dsimp only
  rw [ite_eq_right unequal,ite_eq_right notGreater]
  rfl

/-- Actual equality/less decisions and one true81-op update. Branch
conditions are DERIVED from the true physical stats/prepared fields. -/
theorem suffix_result (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (origin decrementPC : ℕ) (before : State)
    (budget : ℕ) (position : before.pc=origin+251) (ready : Ready P fee before)
    (represented : SearchStateRep P fee before (.bracket lower upper))
    (data : MidpointData P fee (midpointPenalty lower upper) before) (safe : RootD27.Bits.SafeBits before budget)
    (small : 7≤budget) (naturalRoom : 32*coreOperandBound P fee≤budget)
    (endBits : (Cell.natural (origin+516)).bits≤budget) (decrementBits : natBits decrementPC≤budget)
    (belowEntry : origin+516<labels.solveEntry) (decrementBelow : decrementPC<labels.solveEntry)
    (fetched : FetchesCode program origin (bisectionBodyCode origin labels.solveEntry decrementPC)) :
    Nonempty (Result program labels input P fee lower upper budget origin decrementPC before
      (P.cachedBisect P.endpointCache fee (.bracket lower upper))) := by
  have parts:=suffix_fetch_parts program origin labels.solveEntry decrementPC fetched
  have riskValue:=(prepared_selector_fields P fee before ready.prepared).2
  have equalityFetch : FetchesCode program before.pc
      (comparisonDecisionCode .equal 27 3 (origin+262) (origin+273)) := by rw [position];exact parts.1
  obtain ⟨tested,equality,equalityPC⟩:=comparison_prefix P fee (midpointPenalty lower upper) lower upper
    program labels input before .equal 27 3 (middleRisk P fee lower upper) P.certificate.risk
      (origin+262) (origin+273) budget origin ready represented data safe small endBits belowEntry
      (by omega) (by omega) (by omega) (by decide) (by decide) data.risk riskValue equalityFetch
  have equalTarget : tested.pc=if middleRisk P fee lower upper=P.certificate.risk then origin+273 else origin+262 := by
    simpa only [comparisonDecisionTarget,Comparison.rat,beq_iff_eq] using equalityPC
  by_cases equal : middleRisk P fee lower upper=P.certificate.risk
  · have testedPC : tested.pc=origin+273:=by simpa only [ite_eq_left equal] using equalTarget
    have updateFetch : FetchesCode program tested.pc (branchUpdateCode tested.pc false true decrementPC) := by
      rw [testedPC];exact parts.2.2.1
    obtain ⟨result⟩:=finish_prefix P fee lower upper program labels input origin decrementPC budget before tested
      180 equality (by decide) false true (by decide) small naturalRoom endBits decrementBits belowEntry decrementBelow
      (by omega) updateFetch
    exact ⟨result.change_source (bisect_equal P fee lower upper equal)⟩
  · have testedPC : tested.pc=origin+262:=by simpa only [ite_eq_right equal] using equalTarget
    have lessFetch : FetchesCode program tested.pc
        (comparisonDecisionCode .less 3 27 (origin+435) (origin+354)) := by rw [testedPC];exact parts.2.1
    have testedSafe:=(equality.properties tested (List.mem_of_getLast? equality.last)).2
    have testedRisk:=(prepared_selector_fields P fee tested equality.ready.prepared).2
    obtain ⟨compared,less,lessPC⟩:=comparison_prefix P fee (midpointPenalty lower upper) lower upper
      program labels input tested .less 3 27 P.certificate.risk (middleRisk P fee lower upper)
        (origin+435) (origin+354) budget origin equality.ready equality.represented equality.data testedSafe
        small endBits belowEntry (by omega) (by omega) (by omega) (by decide) (by decide)
        testedRisk equality.data.risk lessFetch
    have lessTarget : compared.pc=if P.certificate.risk<middleRisk P fee lower upper then origin+354 else origin+435 := by
      simpa only [comparisonDecisionTarget,Comparison.rat,decide_eq_true_eq] using lessPC
    by_cases greater : P.certificate.risk<middleRisk P fee lower upper
    · have comparedPC : compared.pc=origin+354:=by simpa only [ite_eq_left greater] using lessTarget
      have updateFetch : FetchesCode program compared.pc (branchUpdateCode compared.pc false false decrementPC) := by
        rw [comparedPC];exact parts.2.2.2.1
      obtain ⟨result⟩:=finish_prefix P fee lower upper program labels input origin decrementPC budget before compared
        360 (equality.join less) (by decide) false false (by decide) small naturalRoom endBits decrementBits
        belowEntry decrementBelow (by omega) updateFetch
      exact ⟨result.change_source (bisect_lower P fee lower upper equal greater)⟩
    · have comparedPC : compared.pc=origin+435:=by simpa only [ite_eq_right greater] using lessTarget
      have updateFetch : FetchesCode program compared.pc (branchUpdateCode compared.pc true false decrementPC) := by
        rw [comparedPC];exact parts.2.2.2.2
      obtain ⟨result⟩:=finish_prefix P fee lower upper program labels input origin decrementPC budget before compared
        360 (equality.join less) (by decide) true false (by decide) small naturalRoom endBits decrementBits
        belowEntry decrementBelow (by omega) updateFetch
      exact ⟨result.change_source (bisect_upper P fee lower upper equal greater)⟩

/-- Original true bisection suffix on ONE trace, from actual midpoint64
post through native risk decisions to actual copied/updated source. -/
theorem suffix_actual (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (origin decrementPC : ℕ) (before : State)
    (budget : ℕ) (position : before.pc=origin+251) (ready : Ready P fee before)
    (represented : SearchStateRep P fee before (.bracket lower upper))
    (data : MidpointData P fee (midpointPenalty lower upper) before) (safe : RootD27.Bits.SafeBits before budget)
    (small : 7≤budget) (naturalRoom : 32*coreOperandBound P fee≤budget)
    (endBits : (Cell.natural (origin+516)).bits≤budget) (decrementBits : natBits decrementPC≤budget)
    (belowEntry : origin+516<labels.solveEntry) (decrementBelow : decrementPC<labels.solveEntry)
    (fetched : FetchesCode program origin (bisectionBodyCode origin labels.solveEntry decrementPC)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤5000*PDCompute.Solver.entryCount P.certificate.stages P.tools+2000 ∧
      after.pc=decrementPC ∧ Ready P fee after ∧
      SearchStateRep P fee after (P.cachedBisect P.endpointCache fee (.bracket lower upper)) ∧
      after.heap 28=before.heap 28 ∧ after.output=before.output ∧
      (∀ state∈trace,RegionMemory before state (branchRegion P)) ∧
      (∀ state∈trace,RootD27.Bits.SafeBits state budget) ∧
      peakCells trace≤workingCells before+(originalSolveEncoding P fee (midpointPenalty lower upper)).length+3 ∧
      (∀ state∈trace,(origin+251≤state.pc ∧ state.pc≤origin+515) ∨ state.pc=decrementPC) ∧
      (∀ state∈trace.dropLast,origin+251≤state.pc ∧ state.pc<origin+516) ∧
      actualSolveRequests labels trace=[] ∧ PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=0 ∧
      SolverCallRefinement program labels P fee 40000 trace := by
  obtain ⟨result⟩:=suffix_result P fee lower upper program labels input origin decrementPC before budget position
    ready represented data safe small naturalRoom endBits decrementBits belowEntry decrementBelow fetched
  have capacity:=encoding_capacity P fee (midpointPenalty lower upper)
  unfold retainedTableCapacity at capacity
  refine ⟨result.trace,result.after,result.head,result.last,result.chain,result.timeBound.trans (by omega),
    result.pc,result.ready,result.represented,result.counter,result.output,result.memory,result.safe,result.space,
    result.scope,result.proper,result.requests,result.count,result.refinement⟩

end PDCompute.CoreBranch
