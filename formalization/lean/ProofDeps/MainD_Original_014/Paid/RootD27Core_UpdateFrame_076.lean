module

public import Paid.RootD27Core_BranchControl_075

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

/-- Exact final footprint of the real52-op restore/copy/length block. -/
def savedCopyRegion (P : Parameters) (fee penalty : ℚ) (upper : Bool) : Finset ℕ :=
  retainedCopyRegion (99+2*P.certificate.M) P.certificate.stages P.tools
    (originalSolveEncoding P fee penalty).length upper∪{tableLengthSlot upper}

theorem savedCopy_small_outside (P : Parameters) (fee penalty : ℚ) (upper : Bool)
    (address : ℕ) (small : address<46) (different : address≠tableLengthSlot upper) :
    address∉savedCopyRegion P fee penalty upper := by
  have lower : 48≤retainedTableBase (99+2*P.certificate.M) P.certificate.stages P.tools upper := by
    have bound:=retained_base_above_workspace (99+2*P.certificate.M) P.certificate.stages P.tools upper
    unfold workspaceSize headerWords at bound
    omega
  intro member
  rcases Finset.mem_union.mp member with copied|lengthSlot
  · rcases Finset.mem_union.mp copied with scratch|destination
    · simp only [Finset.mem_insert,Finset.mem_singleton] at scratch
      omega
    · have bounds:=(mem_cellRegion_iff _ _ _).mp destination
      omega
  · exact different (Finset.mem_singleton.mp lengthSlot)

theorem savedCopy_midpoint_outside (P : Parameters) (fee penalty : ℚ) (upper : Bool)
    (address : ℕ) (lower : 24≤address) (upperBound : address≤28) :
    address∉savedCopyRegion P fee penalty upper := by
  apply savedCopy_small_outside P fee penalty upper address (by omega)
  have bound : tableLengthSlot upper≤23:=by cases upper <;> decide
  omega

/-- This also applies to a SAME-B numeric witness: it consumes its
actual final footprint, rather than choosing a second execution. -/
theorem SolvedBuffer.preserve_other_saved_copy {P : Parameters} {fee keptPenalty writtenPenalty : ℚ}
    {kept written : Bool} {before after : State}
    (represented : SolvedBuffer P fee keptPenalty kept before) (different : written≠kept)
    (memory : RegionMemory before after (savedCopyRegion P fee writtenPenalty written)) :
    SolvedBuffer P fee keptPenalty kept after := by
  apply represented.preserve_other_call different
  exact memory.enlarge Finset.subset_union_right

/-- The current header stays live under the real copy. Its midpoint,
three actual solver statistics and remaining counter are unchanged. -/
theorem savedCopy_header_fields (P : Parameters) (fee penalty : ℚ) (upper : Bool)
    (before after : State) (header : Header before 0 (fun slot=>before.heap slot))
    (memory : RegionMemory before after (savedCopyRegion P fee penalty upper)) :
    Header after 0 (fun slot=>after.heap slot) ∧
    after.heap 24=before.heap 24 ∧
    (∀ offset<3,after.heap (25+offset)=before.heap (25+offset)) ∧
    after.heap 28=before.heap 28 := by
  refine ⟨?_,memory.1 24 (savedCopy_midpoint_outside P fee penalty upper 24 (by decide) (by decide)),?_,
    memory.1 28 (savedCopy_midpoint_outside P fee penalty upper 28 (by decide) (by decide))⟩
  · intro slot inside
    exact ⟨memory.2.2.1 (header.live slot inside),by simp only [Nat.zero_add]⟩
  · intro offset inside
    exact memory.1 (25+offset) (savedCopy_midpoint_outside P fee penalty upper (25+offset) (by omega) (by omega))

theorem savedCopy_statistics (P : Parameters) (fee penalty : ℚ) (upper : Bool)
    (before after : State) (statistics : HeapList before 25 (originalStatistics P fee penalty))
    (memory : RegionMemory before after (savedCopyRegion P fee penalty upper)) :
    HeapList after 25 (originalStatistics P fee penalty) := by
  apply memory.heapList statistics
  intro offset inside
  change offset<3 at inside
  exact savedCopy_midpoint_outside P fee penalty upper (25+offset) (by omega) (by omega)

theorem savedCopy_prepared (P : Parameters) (fee penalty : ℚ) (upper : Bool)
    (before after : State) (prepared : HeapList before 0 (preparedInput P fee))
    (memory : RegionMemory before after (savedCopyRegion P fee penalty upper)) :
    HeapList after 0 (preparedInput P fee) := by
  apply memory.heapList prepared
  intro offset inside
  change offset<13 at inside
  apply savedCopy_small_outside
  · omega
  · have lower:=(tableLengthSlot_bounds upper).1
    omega

/-- The endpoint cache is below the real solver workspace and both
retained destinations. No disjointness premise is added to the input. -/
theorem savedCopy_cache (P : Parameters) (fee penalty : ℚ) (upper : Bool)
    (before after : State)
    (stored : HeapList before 96 (encodeList encodeEndpoint P.endpointCache.toList))
    (memory : RegionMemory before after (savedCopyRegion P fee penalty upper)) :
    HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) := by
  apply memory.heapList stored
  intro offset inside member
  have length : (encodeList encodeEndpoint P.endpointCache.toList).length=1+2*(P.certificate.M+1) := by
    rw [←RootD27.Endpoint.endpointPrefix_original,RootD27.Endpoint.endpointPrefix_length]
    omega
  have sourceUpper : 96+offset<99+2*P.certificate.M := by rw [length] at inside;omega
  rcases Finset.mem_union.mp member with copied|lengthSlot
  · rcases Finset.mem_union.mp copied with scratch|destination
    · simp only [Finset.mem_insert,Finset.mem_singleton] at scratch
      omega
    · have bounds:=(mem_cellRegion_iff _ _ _).mp destination
      have destinationLower:=retained_base_above_workspace (99+2*P.certificate.M)
        P.certificate.stages P.tools upper
      unfold workspaceSize headerWords at destinationLower
      omega
  · have equal:=Finset.mem_singleton.mp lengthSlot
    have bound:=(tableLengthSlot_bounds upper).2
    omega

/-- Assemble the source branch from the actual copied table and actual
metadata writer, keeping the other original solution physically intact. -/
theorem lower_update_rep (P : Parameters) (fee penalty : ℚ) (upper : MultiplierSolve)
    (before copied after : State) (values : ℕ→Cell)
    (upperOriginal : OriginalSolved P fee upper)
    (upperBuffer : SolvedBuffer P fee upper.multiplier true before)
    (copyMemory : RegionMemory before copied (savedCopyRegion P fee penalty false))
    (header : Header copied 0 values)
    (afterHeader : Header after 0 (selectedMetadataValues values false false))
    (metadataMemory : RegionMemory copied after (selectedMetadataRegion false))
    (middlePrice : values 24=.rational penalty)
    (statistics : HeapList before 25 (originalStatistics P fee penalty))
    (table : HeapList copied
      (retainedTableBase (99+2*P.certificate.M) P.certificate.stages P.tools false)
      (originalSolveEncoding P fee penalty))
    (length : HeapList copied (tableLengthSlot false) [.natural (originalSolveEncoding P fee penalty).length]) :
    SearchStateRep P fee after (.bracket (P.cachedSolveMultiplier P.endpointCache fee penalty) upper) := by
  have copiedStatistics:=savedCopy_statistics P fee penalty false before copied statistics copyMemory
  obtain ⟨buffer,tag⟩:=selected_buffer_of_metadata P fee penalty false false copied after values header
    afterHeader metadataMemory middlePrice copiedStatistics table length
  exact selected_lower_rep P fee penalty upper copied after upperOriginal
    (upperBuffer.preserve_other_saved_copy (by decide) copyMemory) metadataMemory buffer tag

theorem upper_update_rep (P : Parameters) (fee penalty : ℚ) (lower : MultiplierSolve)
    (before copied after : State) (values : ℕ→Cell)
    (lowerOriginal : OriginalSolved P fee lower)
    (lowerBuffer : SolvedBuffer P fee lower.multiplier false before)
    (copyMemory : RegionMemory before copied (savedCopyRegion P fee penalty true))
    (header : Header copied 0 values)
    (afterHeader : Header after 0 (selectedMetadataValues values true false))
    (metadataMemory : RegionMemory copied after (selectedMetadataRegion true))
    (middlePrice : values 24=.rational penalty)
    (statistics : HeapList before 25 (originalStatistics P fee penalty))
    (table : HeapList copied
      (retainedTableBase (99+2*P.certificate.M) P.certificate.stages P.tools true)
      (originalSolveEncoding P fee penalty))
    (length : HeapList copied (tableLengthSlot true) [.natural (originalSolveEncoding P fee penalty).length]) :
    SearchStateRep P fee after (.bracket lower (P.cachedSolveMultiplier P.endpointCache fee penalty)) := by
  have copiedStatistics:=savedCopy_statistics P fee penalty true before copied statistics copyMemory
  obtain ⟨buffer,tag⟩:=selected_buffer_of_metadata P fee penalty true false copied after values header
    afterHeader metadataMemory middlePrice copiedStatistics table length
  exact selected_upper_rep P fee penalty lower copied after lowerOriginal
    (lowerBuffer.preserve_other_saved_copy (by decide) copyMemory) metadataMemory buffer tag

theorem exact_update_rep (P : Parameters) (fee penalty : ℚ)
    (before copied after : State) (values : ℕ→Cell)
    (copyMemory : RegionMemory before copied (savedCopyRegion P fee penalty false))
    (header : Header copied 0 values)
    (afterHeader : Header after 0 (selectedMetadataValues values false true))
    (metadataMemory : RegionMemory copied after (selectedMetadataRegion false))
    (middlePrice : values 24=.rational penalty)
    (statistics : HeapList before 25 (originalStatistics P fee penalty))
    (table : HeapList copied
      (retainedTableBase (99+2*P.certificate.M) P.certificate.stages P.tools false)
      (originalSolveEncoding P fee penalty))
    (length : HeapList copied (tableLengthSlot false) [.natural (originalSolveEncoding P fee penalty).length]) :
    SearchStateRep P fee after (.exact (P.cachedSolveMultiplier P.endpointCache fee penalty)) := by
  have copiedStatistics:=savedCopy_statistics P fee penalty false before copied statistics copyMemory
  obtain ⟨buffer,tag⟩:=selected_buffer_of_metadata P fee penalty false true copied after values header
    afterHeader metadataMemory middlePrice copiedStatistics table length
  exact selected_exact_rep P fee penalty after buffer tag

end RootD27.Core
