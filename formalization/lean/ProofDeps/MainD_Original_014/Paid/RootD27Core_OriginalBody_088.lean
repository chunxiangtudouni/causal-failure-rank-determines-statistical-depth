module

public import Paid.RootD27Core_LiveBody_087

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CoreSearch PDCompute.CoreSearchLoop PDCompute.CoreSearchBudget

/-- The actual516 body, with its true outer decrement520. -/
def originalSearchBody (origin : ℕ) (labels : RoutineLabels) : List Instruction :=
  bisectionBodyCode (origin+4) labels.solveEntry (origin+520)

theorem originalSearchBody_length (origin : ℕ) (labels : RoutineLabels) :
    (originalSearchBody origin labels).length=516 :=
  bisectionBody_length _ _ _

/-- All original j<J cases of the real516 body. Every scalar, solver and
natural-address room is DERIVED from the original input and the one
fixed-program B. There is no BodySpec, reachability, table-answer or
comparison-answer hypothesis. The resulting internal certificate is
therefore ready to instantiate the actual J-loop theorem. -/
theorem original_body_calls (program : Program) (labels : RoutineLabels) (input : List Cell)
    (P : Parameters) (fee : ℚ) (origin pcUpper : ℕ)
    (endBound : origin+529≤pcUpper) (belowEntry : origin+529<labels.solveEntry)
    (solverOrigin : labels.solveEntry+1≤pcUpper)
    (solverLength : (solverCalleeCode .liveHeap (labels.solveEntry+1)).length≤pcUpper)
    (markerLabel : labels.solveReturn=PDLower.CoreRuntimeNumeric.commonSolverMarkerPC labels)
    (stubFetch : program[labels.solveEntry]?=some (.jump (labels.solveEntry+1)))
    (bodyFetch : FetchesCode program (labels.solveEntry+1) (solverCalleeCode .liveHeap (labels.solveEntry+1))) :
    CallBodySpec program labels input P fee origin (originalSearchBody origin labels)
      (PDCompute.CoreGlobalBudget.budget P fee pcUpper) (coreSearchRegion P)
      (50000*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools) 40000 := by
  intro j inside before position ready represented _counter safe fetched
  let B:=PDCompute.CoreGlobalBudget.budget P fee pcUpper
  let scale:=originalScalarScale P fee
  let entries:=PDCompute.Solver.entryCount P.certificate.stages P.tools
  have beforePC : before.pc=origin+4:=position
  have actualFetch : FetchesCode program before.pc
      (bisectionBodyCode before.pc labels.solveEntry (origin+520)) := by
    simpa only [originalSearchBody,beforePC] using fetched
  have endBits : (Cell.natural (before.pc+516)).bits≤B :=
    PDCompute.CoreGlobalBudget.budget_pc_cell P fee pcUpper _ (by rw [beforePC];omega)
  have endNat : natBits (before.pc+516)≤B := by
    change 1+natBits (before.pc+516)≤B at endBits
    omega
  have decrementBits : natBits (origin+520)≤B:=
    PDCompute.CoreGlobalBudget.budget_pc P fee pcUpper _ (by omega)
  have actualBelow : before.pc+516<labels.solveEntry:=by rw [beforePC];omega
  have decrementBelow : origin+520<labels.solveEntry:=by omega
  have small : 7≤B:=PDCompute.CoreGlobalBudget.budget_small P fee pcUpper
  have rooms:=PDCompute.CoreGlobalBudget.original_search_rooms P fee pcUpper j (by omega)
  have addressBits : 1+natBits headerWords≤B:=
    PDCompute.CoreGlobalBudget.budget_header P fee pcUpper headerWords (by decide)
  have baseBits : (Cell.natural (99+2*P.certificate.M)).bits≤B:=
    PDCompute.CoreGlobalBudget.budget_base P fee pcUpper
  have naturalRoom : 32*coreOperandBound P fee≤B:=
    PDCompute.CoreGlobalBudget.budget_runtime P fee pcUpper
  have controlRoom : PDLower.CoreRuntimeNumeric.runtimeControlRoom P (labels.solveEntry+1)≤B:=
    PDCompute.CoreGlobalBudget.budget_runtime_control P fee pcUpper _ solverOrigin solverLength
  have positive : 0<(P.certificate.M+1)*entries := by
    unfold entries PDCompute.Solver.entryCount
    positivity
  generalize stateEq : source P fee j=state at represented
  have reindex : ∀ after,SearchStateRep P fee after (P.cachedMultiplierStep P.endpointCache fee state) →
      SearchStateRep P fee after (source P fee (j+1)) := by
    intro after result
    change SearchStateRep P fee after (P.cachedMultiplierStep P.endpointCache fee (source P fee j))
    rw [stateEq]
    exact result
  cases state with
  | exact solution =>
    obtain ⟨trace,after,head,last,chain,cost,pc,afterReady,afterRep,counter,output,memory,bits,_space,
      _proper,requests,count,calls⟩:=
      bisection_exact_actual P fee solution program labels input before (origin+520) B 40000 ready represented
        safe small endNat decrementBits actualBelow decrementBelow actualFetch
    have nextRequests : P.nextSolveRequests fee (source P fee j)=[] := by
      rw [stateEq]
      simp only [nextSolveRequests]
      split_ifs <;> rfl
    refine ⟨trace,after,head,last,chain,cost.trans ?_,?_,afterReady,reindex after afterRep,counter,output,
      (fun state member=>(memory state member).enlarge (Finset.empty_subset _)),bits,by omega,?_,calls⟩
    · change 75≤50000*(P.certificate.M+1)*entries
      simp only [Nat.mul_assoc]
      omega
    · simpa only [PDCompute.CoreSearchLoop.decrementPC,originalSearchBody_length,Nat.add_assoc] using pc
    · rw [←stateEq,nextRequests]
      exact requests
  | bracket lower upper =>
    have intrinsic : ScalarInputBits P fee lower upper scale := by
      have scalar:=rooms.1
      change StateScalarInput P fee scale (source P fee j) at scalar
      rw [stateEq] at scalar
      exact scalar
    by_cases stopped : P.searchStopped fee (.bracket lower upper)
    · obtain ⟨trace,after,head,last,chain,cost,pc,afterReady,afterRep,counter,output,memory,bits,_space,
        _proper,requests,count,calls⟩:=
        bisection_stopped_actual P fee lower upper program labels input before (origin+520) scale B 40000
          ready represented stopped safe small intrinsic rooms.2.2.2.2 addressBits endNat decrementBits
          actualBelow decrementBelow actualFetch
      have nextRequests : P.nextSolveRequests fee (source P fee j)=[] := by
        rw [stateEq]
        simp only [nextSolveRequests,ite_eq_left stopped]
      refine ⟨trace,after,head,last,chain,cost.trans ?_,?_,afterReady,reindex after afterRep,counter,output,
        (fun state member=>(memory state member).enlarge (scalar_subset_coreSearch P)),bits,by omega,?_,calls⟩
      · change 3090≤50000*(P.certificate.M+1)*entries
        simp only [Nat.mul_assoc]
        omega
      · simpa only [PDCompute.CoreSearchLoop.decrementPC,originalSearchBody_length,Nat.add_assoc] using pc
      · rw [←stateEq,nextRequests]
        exact requests
    · have midpointRoom : 4194304*solverBitScale P fee ((lower.multiplier+upper.multiplier)/2)
          P.certificate.stages P.tools≤B:=rooms.2.2.2.1 lower upper stateEq
      obtain ⟨trace,after,head,last,chain,cost,pc,afterReady,afterRep,counter,output,memory,bits,_space,
        requests,count,calls⟩:=
        bisection_live_actual P fee lower upper program labels input before (origin+520) scale B ready represented
          stopped safe small intrinsic rooms.2.2.2.2 addressBits baseBits endBits decrementBits naturalRoom
          controlRoom midpointRoom markerLabel actualBelow decrementBelow actualFetch stubFetch bodyFetch
      have nextRequests : P.nextSolveRequests fee (source P fee j)=[(lower.multiplier+upper.multiplier)/2] := by
        rw [stateEq]
        simp only [nextSolveRequests,ite_eq_right stopped]
      refine ⟨trace,after,head,last,chain,cost,?_,afterReady,reindex after afterRep,counter,output,memory,bits,
        by omega,?_,calls⟩
      · simpa only [PDCompute.CoreSearchLoop.decrementPC,originalSearchBody_length,Nat.add_assoc] using pc
      · rw [←stateEq,nextRequests]
        exact requests

end RootD27.Core
