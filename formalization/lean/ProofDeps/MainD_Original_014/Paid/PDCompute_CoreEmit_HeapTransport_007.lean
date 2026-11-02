module

public import Paid.PDCompute_CoreEmit_Composition_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDCompute.CoreEmit
open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (HeapList)

theorem heapList_same {before after : State} {base : ℕ} {cells : List Cell}
    (stored : HeapList before base cells) (heap : after.heap=before.heap) (live : after.live=before.live) :
    HeapList after base cells := by
  apply HeapList.of_values
  · intro offset inside
    rw [live]
    exact stored.1 offset inside
  · intro offset inside
    rw [heap]
    exact HeapList.value stored offset inside

theorem PreparedDimensions.preserve {before after : State} {n k M : ℕ}
    (stored : PreparedDimensions before n k M) (heap : after.heap=before.heap) (live : after.live=before.live) :
    PreparedDimensions after n k M :=
  ⟨heapList_same stored.1 heap live,heapList_same stored.2.1 heap live,heapList_same stored.2.2 heap live⟩

theorem SolvePayload.preserve {before after : State} {n k M : ℕ} {upper : Bool} {solution : MultiplierSolve}
    (stored : SolvePayload before n k M upper solution) (heap : after.heap=before.heap) (live : after.live=before.live) :
    SolvePayload after n k M upper solution :=
  ⟨heapList_same stored.1 heap live,heapList_same stored.2.1 heap live,heapList_same stored.2.2 heap live⟩

theorem StatePayload.preserve {before after : State} {n k M : ℕ} {state : MultiplierState}
    (stored : StatePayload before n k M state) (heap : after.heap=before.heap) (live : after.live=before.live) :
    StatePayload after n k M state := by
  cases state with
  | exact solution => exact ⟨heapList_same stored.1 heap live,stored.2.preserve heap live⟩
  | bracket lower upper =>
    exact ⟨heapList_same stored.1 heap live,stored.2.1.preserve heap live,stored.2.2.preserve heap live⟩

theorem emitted_complete (before state : State) (cells : List Cell)
    (heap : state.heap=before.heap) (live : state.live=before.live)
    (output : state.output=before.output++cells) : RootD27.Core.EmittedPrefix before cells state :=
  ⟨heap,live,cells,[],by simp,output⟩

end PDCompute.CoreEmit
