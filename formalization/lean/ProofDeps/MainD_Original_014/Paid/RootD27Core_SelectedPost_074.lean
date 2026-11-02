module

public import Paid.RootD27Core_BisectionLayout_073

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open PDLower.CoreSearch

/-- A postcondition rule for the actual metadata writer. It applies to
the joint numeric witness as well as the functional one, without mixing
independently selected traces. All four buffer components are physical. -/
theorem selected_buffer_of_metadata (P : Parameters) (fee penalty : ℚ) (upper isExact : Bool)
    (before after : State) (values : ℕ→Cell) (header : Header before 0 values)
    (afterHeader : Header after 0 (selectedMetadataValues values upper isExact))
    (memory : RegionMemory before after (selectedMetadataRegion upper))
    (middlePrice : values 24=.rational penalty)
    (middleStatistics : HeapList before 25 (originalStatistics P fee penalty))
    (table : HeapList before
      (retainedTableBase (99+2*P.certificate.M) P.certificate.stages P.tools upper)
      (originalSolveEncoding P fee penalty))
    (length : HeapList before (tableLengthSlot upper) [.natural (originalSolveEncoding P fee penalty).length]) :
    SolvedBuffer P fee penalty upper after ∧ HeapList after 13 [.natural (if isExact then 0 else 1)] := by
  have sourceValues : ∀ offset (inside : offset<3),values (25+offset)=(originalStatistics P fee penalty)[offset]'inside := by
    intro offset inside
    have bound : 25+offset<headerWords:=by unfold headerWords;omega
    have value:=header.value (25+offset) bound
    simp only [Nat.zero_add] at value
    exact value.symm.trans (PDLower.CalibrationCompute.HeapList.value middleStatistics offset inside)
  have priceAfter : HeapList after (multiplierSlot upper) [.rational penalty] := by
    apply header_scalarHeapList afterHeader
    · change multiplierSlot upper+1≤headerWords
      cases upper <;> decide
    · intro offset inside
      have zero : offset=0:=by change offset<1 at inside;omega
      subst offset
      simpa only [Nat.add_zero,List.getElem_cons_zero] using
        (selectedMetadata_price values upper isExact).trans middlePrice
  have statisticsAfter : HeapList after (statisticsSlot upper) (originalStatistics P fee penalty) := by
    apply header_scalarHeapList afterHeader
    · change statisticsSlot upper+3≤headerWords
      cases upper <;> decide
    · intro offset inside
      change offset<3 at inside
      exact (selectedMetadata_statistics values upper isExact offset inside).trans (sourceValues offset inside)
  have lengthAfter : HeapList after (tableLengthSlot upper) [.natural (originalSolveEncoding P fee penalty).length] := by
    apply memory.heapList length
    intro offset _inside
    apply selectedMetadata_above_outside
    have lower : 22≤tableLengthSlot upper:=by cases upper <;> decide
    omega
  have tableAfter : HeapList after
      (retainedTableBase (99+2*P.certificate.M) P.certificate.stages P.tools upper)
      (originalSolveEncoding P fee penalty) := by
    apply memory.heapList table
    intro offset _inside
    apply selectedMetadata_above_outside
    have lower:=retained_base_above_workspace (99+2*P.certificate.M) P.certificate.stages P.tools upper
    unfold workspaceSize headerWords at lower
    omega
  have tagAfter : HeapList after 13 [.natural (if isExact then 0 else 1)] := by
    apply header_scalarHeapList afterHeader
    · change 13+1≤headerWords
      decide
    · intro offset inside
      have zero : offset=0:=by change offset<1 at inside;omega
      subst offset
      simpa only [Nat.add_zero,List.getElem_cons_zero] using selectedMetadata_tag values upper isExact
  exact ⟨⟨priceAfter,statisticsAfter,lengthAfter,tableAfter⟩,tagAfter⟩

theorem selected_exact_rep (P : Parameters) (fee penalty : ℚ) (state : State)
    (buffer : SolvedBuffer P fee penalty false state) (tag : HeapList state 13 [.natural 0]) :
    SearchStateRep P fee state (.exact (P.cachedSolveMultiplier P.endpointCache fee penalty)) :=
  ⟨originalSolved_cached P fee penalty,tag,buffer⟩

theorem selected_lower_rep (P : Parameters) (fee penalty : ℚ) (upper : MultiplierSolve)
    (before after : State) (upperOriginal : OriginalSolved P fee upper)
    (upperBuffer : SolvedBuffer P fee upper.multiplier true before)
    (memory : RegionMemory before after (selectedMetadataRegion false))
    (middleBuffer : SolvedBuffer P fee penalty false after) (tag : HeapList after 13 [.natural 1]) :
    SearchStateRep P fee after (.bracket (P.cachedSolveMultiplier P.endpointCache fee penalty) upper) :=
  ⟨originalSolved_cached P fee penalty,upperOriginal,tag,middleBuffer,
    upperBuffer.preserve_selected_metadata (by decide) memory⟩

theorem selected_upper_rep (P : Parameters) (fee penalty : ℚ) (lower : MultiplierSolve)
    (before after : State) (lowerOriginal : OriginalSolved P fee lower)
    (lowerBuffer : SolvedBuffer P fee lower.multiplier false before)
    (memory : RegionMemory before after (selectedMetadataRegion true))
    (middleBuffer : SolvedBuffer P fee penalty true after) (tag : HeapList after 13 [.natural 1]) :
    SearchStateRep P fee after (.bracket lower (P.cachedSolveMultiplier P.endpointCache fee penalty)) :=
  ⟨lowerOriginal,originalSolved_cached P fee penalty,tag,
    lowerBuffer.preserve_selected_metadata (by decide) memory,middleBuffer⟩

end RootD27.Core
