module

public import Paid.PDLower_CalibrationCompute_EmitHeader_048
public import Paid.PDLower_CalibrationCompute_HeapAppend_042

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

theorem HeapList.storeResultOutside {before : State} {start : ℕ} {values : List Cell}
    (represented : HeapList before start values) (base offset : ℕ) (source : Register)
    (separate : ∀ i<values.length,base+offset ≠ start+i) :
    HeapList (storeSlotResult before base offset source) start values := by
  exact HeapList.writeOutside represented (base+offset) (before.register source) separate

/-- The two physical result writes extend the actual encoded cache,
including the case of arbitrary prior contents at those two addresses. -/
theorem emitLead_cache {before : State} {base start : ℕ} {values : List Cell}
    (represented : HeapList before start values) (q weight : ℚ) :
    HeapList (emitLeadResult before base (start+values.length) q weight) start
      (values++[.rational q,.rational weight]) := by
  have first := represented.appendCell (.rational q)
  have second := first.appendCell (.rational weight)
  simpa only [List.length_append,List.length_singleton,List.append_assoc,List.singleton_append,
    emitLeadResult,HeapList,heapSegment,writeCell,loadSlotResult,Nat.add_assoc] using second

/-- Header updates after emission do not erase previously computed
calibration constants. -/
theorem emit_cache {before : State} {base start : ℕ} {values : List Cell}
    (represented : HeapList before start values) (level : ℕ) (q weight : ℚ)
    (outside : base+16≤start) :
    HeapList (emitResult before base (start+values.length) level q weight) start
      (values++[.rational q,.rational weight]) := by
  have lead := emitLead_cache (base:=base) represented q weight
  have updated := lead.storeResultOutside base 15 .index (by intros; omega)
  let middle := incrementSlotLoaded
    (storeSlotResult (emitLeadResult before base (start+values.length) q weight) base 15 .index) base 5 level
  have unchanged : HeapList middle start (values++[.rational q,.rational weight]) := updated
  exact unchanged.storeResultOutside base 5 .index (by intros; omega)

end PDLower.CalibrationCompute
