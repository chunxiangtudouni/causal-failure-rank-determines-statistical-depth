module

public import Paid.PDCompute_SolverNatCounter_032

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

/-- The cache's addresses avoid the solver's allocation. This static
property survives header/dense-table allocation; disjointness of the
ENTIRE current live heap would cease to hold after the first real store. -/
def EndpointAvoids (mode : ReaderMode) (P : Parameters) (source base n k : ℕ) : Prop :=
  match mode with
  | .inputROM => True
  | .liveHeap => ∀ offset < (encodeList encodeEndpoint P.endpointCache.toList).length,
    source+offset ∉ workspace base n k

theorem EndpointSource.avoids_of_disjoint (mode : ReaderMode) (input : List Cell) (P : Parameters)
    (source base n k : ℕ) (before : State) (hsource : EndpointSource mode input P source before)
    (hdisjoint : Disjoint before.live (workspace base n k)) : EndpointAvoids mode P source base n k := by
  cases mode with
  | inputROM => trivial
  | liveHeap =>
    intro offset inside member
    exact Finset.disjoint_left.mp hdisjoint (hsource.1 offset inside) member

theorem EndpointSource.frame_of_avoids (mode : ReaderMode) (input : List Cell) (P : Parameters)
    (source base n k : ℕ) (before after : State) (hsource : EndpointSource mode input P source before)
    (avoids : EndpointAvoids mode P source base n k) (frame : Frame before after base n k) :
    EndpointSource mode input P source after := by
  cases mode with
  | inputROM => exact hsource
  | liveHeap =>
    change PDLower.CalibrationCompute.HeapList _ _ _
    apply PDLower.CalibrationCompute.HeapList.of_values
    · intro offset inside
      exact (frame.2 _ (avoids offset inside)).mpr (hsource.1 offset inside)
    · intro offset inside
      rw [frame.1 _ (avoids offset inside)]
      exact PDLower.CalibrationCompute.HeapList.value hsource offset inside

end PDCompute.Solver
