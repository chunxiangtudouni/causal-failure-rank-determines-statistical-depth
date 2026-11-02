module

public import Paid.RootD27Core_RootStatisticsResources_044
public import Paid.RootD27Core_DenseInitialCall_049

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

theorem dense_root_end (base n k : ℕ) :
    cellBase base k n k+6=resultBase base n k := by
  unfold cellBase resultBase PDCompute.Solver.entryCount entryWords
  ring

theorem dense_root_statistics_pointer (base n k : ℕ) :
    cellBase base k n k+3=resultBase base n k-3 := by
  have endAddress:=dense_root_end base n k
  omega

theorem dense_result_source_bound (base n k : ℕ) : 51≤resultBase base n k := by
  have positive : 1≤PDCompute.Solver.entryCount n k := by change 0<(n+1)*(k+1);positivity
  unfold resultBase tableBase headerWords entryWords
  omega

/-- The three real statistics occupy the tail of the actual root dense
record, exactly three cells before the returned serialization pointer. -/
theorem dense_root_statistics_heap (before : State) (base n k : ℕ) (entry : MenuEntry)
    (root : HeapList before (cellBase base k n k) (denseEncodeEntry entry)) :
    HeapList before (resultBase base n k-3)
      [.rational entry.observation,.rational entry.repairs,.rational entry.failure] := by
  rw [←dense_root_statistics_pointer base n k]
  apply PDLower.CalibrationCompute.HeapList.of_values
  · intro offset inside
    change offset<3 at inside
    have address : cellBase base k n k+3+offset=cellBase base k n k+(offset+3):=by omega
    rw [address]
    exact root.1 (offset+3) (by rw [denseEncodeEntry_length];unfold entryWords;omega)
  · intro offset inside
    change offset<3 at inside
    have address : cellBase base k n k+3+offset=cellBase base k n k+(offset+3):=by omega
    rw [address]
    have value:=PDLower.CalibrationCompute.HeapList.value root (offset+3)
      (by rw [denseEncodeEntry_length];unfold entryWords;omega)
    rw [value]
    obtain ⟨action,observation,repairs,failure⟩:=entry
    cases action <;> interval_cases offset <;> rfl

/-- The original solveRecord, rather than externally supplied statistics,
is physically read from the SAME completed solver's root record. -/
theorem original_root_statistics_actual (P : Parameters) (fee penalty : ℚ)
    (program : Program) (input : List Cell) (before : State) (target : ℕ)
    (lower : 13≤target) (upper : target+2<46)
    (prepared : HeapList before 0 (preparedInput P fee))
    (address : before.register .address=.natural (resultBase (99+2*P.certificate.M) P.certificate.stages P.tools))
    (root : HeapList before (cellBase (99+2*P.certificate.M) P.tools P.certificate.stages P.tools)
      (denseEncodeEntry (menuEntryAt (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)
        P.certificate.stages P.tools)))
    (fetched : FetchesCode program before.pc (rootStatisticsCode target)) :
    ∃ trace : List State,
      trace.head?=some before ∧
      trace.getLast?=some (rootStatisticsResult before target P.certificate.M
        (P.solveRecord (P.cachedSolveMultiplier P.endpointCache fee penalty)).observation
        (P.solveRecord (P.cachedSolveMultiplier P.endpointCache fee penalty)).repairs
        (P.solveRisk (P.cachedSolveMultiplier P.endpointCache fee penalty))) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤315 ∧
      (∀ state∈trace,RegionMemory before state {target,target+1,target+2}) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+20) ∧
      peakCells trace≤workingCells before+3 := by
  have menuLive : 7∈before.live:=prepared.1 7 (by change 7<13;decide)
  have menuValue:=PDLower.CalibrationCompute.HeapList.value prepared 7 (by change 7<13;decide)
  change before.heap 7=.natural P.certificate.M at menuValue
  exact rootStatistics_actual program input before target
    (resultBase (99+2*P.certificate.M) P.certificate.stages P.tools) P.certificate.M
    (P.solveRecord (P.cachedSolveMultiplier P.endpointCache fee penalty)).observation
    (P.solveRecord (P.cachedSolveMultiplier P.endpointCache fee penalty)).repairs
    (P.solveRisk (P.cachedSolveMultiplier P.endpointCache fee penalty)) lower upper
    (dense_result_source_bound _ _ _) address (dense_root_statistics_heap before _ _ _ _ root) menuLive menuValue fetched

end RootD27.Core
