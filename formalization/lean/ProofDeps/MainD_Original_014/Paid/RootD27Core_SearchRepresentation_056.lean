module

public import Paid.RootD27Core_SolverStatistics_051
public import Paid.RootD27Core_RetainedCommit_055

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

def multiplierSlot (upper : Bool) : ℕ:=if upper then 15 else 14
def statisticsSlot (upper : Bool) : ℕ:=if upper then 19 else 16
def tableLengthSlot (upper : Bool) : ℕ:=if upper then 23 else 22

def originalSolveRecord (P : Parameters) (fee penalty : ℚ) : MenuEntry :=
  P.solveRecord (P.cachedSolveMultiplier P.endpointCache fee penalty)

def originalSolveEncoding (P : Parameters) (fee penalty : ℚ) : List Cell :=
  encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)

def originalStatistics (P : Parameters) (fee penalty : ℚ) : List Cell :=
  [.rational (originalSolveRecord P fee penalty).observation,
   .rational (originalSolveRecord P fee penalty).repairs,
   .rational (originalSolveRecord P fee penalty).failure]

/-- All metadata is physically live, and the actual retained buffer
contains the original solve's true encoding. This is an internal runtime
invariant to construct from calls/stores, not an original input premise. -/
def SolvedBuffer (P : Parameters) (fee penalty : ℚ) (upper : Bool) (state : State) : Prop :=
  HeapList state (multiplierSlot upper) [.rational penalty] ∧
  HeapList state (statisticsSlot upper) (originalStatistics P fee penalty) ∧
  HeapList state (tableLengthSlot upper) [.natural (originalSolveEncoding P fee penalty).length] ∧
  HeapList state (retainedTableBase (99+2*P.certificate.M) P.certificate.stages P.tools upper)
    (originalSolveEncoding P fee penalty)

def OriginalSolved (P : Parameters) (fee : ℚ) (solution : MultiplierSolve) : Prop :=
  solution=P.cachedSolveMultiplier P.endpointCache fee solution.multiplier

def SearchStateRep (P : Parameters) (fee : ℚ) (state : State) : MultiplierState→Prop
  | .exact solution => OriginalSolved P fee solution ∧ HeapList state 13 [.natural 0] ∧
      SolvedBuffer P fee solution.multiplier false state
  | .bracket lower upper => OriginalSolved P fee lower ∧ OriginalSolved P fee upper ∧
      HeapList state 13 [.natural 1] ∧ SolvedBuffer P fee lower.multiplier false state ∧
      SolvedBuffer P fee upper.multiplier true state

theorem originalSolved_cached (P : Parameters) (fee penalty : ℚ) :
    OriginalSolved P fee (P.cachedSolveMultiplier P.endpointCache fee penalty) := rfl

theorem statisticsSlot_bounds (upper : Bool) : 13≤statisticsSlot upper ∧ statisticsSlot upper+2<46 := by
  cases upper <;> decide

theorem tableLengthSlot_bounds (upper : Bool) : 13≤tableLengthSlot upper ∧ tableLengthSlot upper<46 := by
  cases upper <;> decide

/-- A precise phase frame transfers the four physical buffer components.
The caller proves these separations from its actual finite write region. -/
theorem SolvedBuffer.preserve {P : Parameters} {fee penalty : ℚ} {upper : Bool} {before after : State}
    (represented : SolvedBuffer P fee penalty upper before) (region : Finset ℕ)
    (memory : RegionMemory before after region)
    (multiplierOutside : ∀ offset<1,multiplierSlot upper+offset∉region)
    (statisticsOutside : ∀ offset<3,statisticsSlot upper+offset∉region)
    (lengthOutside : ∀ offset<1,tableLengthSlot upper+offset∉region)
    (tableOutside : ∀ offset<(originalSolveEncoding P fee penalty).length,
      retainedTableBase (99+2*P.certificate.M) P.certificate.stages P.tools upper+offset∉region) :
    SolvedBuffer P fee penalty upper after := by
  refine ⟨memory.heapList represented.1 ?_,memory.heapList represented.2.1 ?_,
    memory.heapList represented.2.2.1 ?_,memory.heapList represented.2.2.2 tableOutside⟩
  · exact multiplierOutside
  · exact statisticsOutside
  · exact lengthOutside

end RootD27.Core
