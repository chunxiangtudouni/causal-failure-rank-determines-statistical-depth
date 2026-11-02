module
public import Paid.RootD27Core_OriginalLoopLower_094
public import Paid.PDCompute_CoreInitialize_Resources_004
public import Paid.PDCompute_CoreFinalization_Actual_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace PDCompute.CoreSuffix
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open RootD27.Core PDLower.CoreSearch PDCompute.CoreSearchLoop

/-- The literal main suffix of the unique core layout: 164 + 529 + 252.
The two solvers are the actual shared callee, not duplicated code. -/
def code (origin : ℕ) (labels : RoutineLabels) : List Instruction :=
  initializeSearchCode origin labels.solveEntry++
    (PDCompute.CoreSearchLoop.code (origin+164) (originalSearchBody (origin+164) labels)++
      finalizationCode (origin+693))

theorem code_length (origin : ℕ) (labels : RoutineLabels) : (code origin labels).length=945 := by
  simp only [code,List.length_append,initializeSearch_length,PDCompute.CoreSearchLoop.code_length,
    originalSearchBody_length,finalization_length]

theorem fetch_parts (program : Program) (origin : ℕ) (labels : RoutineLabels)
    (fetched : FetchesCode program origin (code origin labels)) :
    FetchesCode program origin (initializeSearchCode origin labels.solveEntry) ∧
    FetchesCode program (origin+164) (PDCompute.CoreSearchLoop.code (origin+164) (originalSearchBody (origin+164) labels)) ∧
    FetchesCode program (origin+693) (finalizationCode (origin+693)) := by
  change FetchesCode program origin (_++(_++_)) at fetched
  refine ⟨fetched.append_left,?_,?_⟩
  · simpa only [initializeSearch_length] using fetched.append_right.append_left
  · simpa only [initializeSearch_length,PDCompute.CoreSearchLoop.code_length,originalSearchBody_length,Nat.add_assoc]
      using fetched.append_right.append_right

theorem initial_call_subset (P : Parameters) (fee penalty : ℚ) (upper : Bool) :
    solvedBufferCallRegion P fee penalty upper⊆coreSearchRegion P := by
  apply Finset.union_subset
  · apply Finset.union_subset
    · exact PDCompute.CoreMemory.solverWorkspace_subset_global P.certificate.M P.certificate.stages P.tools
    · intro address member
      apply scalar_subset_coreSearch P
      cases upper <;> simp only [statisticsSlot,Bool.false_eq_true,ite_false,ite_true,
        Finset.mem_insert,Finset.mem_singleton] at member <;>
        rcases member with rfl|rfl|rfl <;> decide
  · apply Finset.union_subset
    · exact PDCompute.CoreMemory.retainedCopy_subset_global P.certificate.M P.certificate.stages P.tools
        _ upper ((original_table_capacity P fee penalty P.certificate.stages P.tools).trans
          (retained_capacity_enough P.certificate.stages P.tools))
    · intro address member
      have same:=Finset.mem_singleton.mp member
      subst address
      apply scalar_subset_coreSearch P
      cases upper <;> decide

theorem initialization_subset (P : Parameters) (fee : ℚ) :
    initializeSearchRegion P fee⊆coreSearchRegion P :=
  Finset.union_subset (scalar_subset_coreSearch P)
    (Finset.union_subset (initial_call_subset P fee 0 false) (initial_call_subset P fee P.Lambda true))

/-- A single physical heap region and a separate genuine output prefix.
It permits old live scratch inside the region and never clears it. -/
structure OutputRegion (P : Parameters) (before : State) (cells : List Cell) (current : State) : Prop where
  heapOutside : ∀ address,address∉coreSearchRegion P→current.heap address=before.heap address
  liveUpper : current.live⊆before.live∪coreSearchRegion P
  liveLower : before.live⊆current.live
  emitted : ∃ written pending : List Cell,cells=written++pending ∧ current.output=before.output++written

theorem OutputRegion.of_memory {P : Parameters} {before current : State} (cells : List Cell)
    (memory : RegionMemory before current (coreSearchRegion P)) : OutputRegion P before cells current :=
  ⟨memory.1,memory.2.1,memory.2.2.1,[],cells,by simp,by simpa using memory.2.2.2⟩

theorem OutputRegion.after_memory {P : Parameters} {before middle current : State} {cells : List Cell}
    (memory : RegionMemory before middle (coreSearchRegion P))
    (later : PDCompute.CoreFinalization.OutputRegion middle cells current) : OutputRegion P before cells current := by
  refine ⟨fun address outside=>(later.heapOutside address (fun inside=>outside (scalar_subset_coreSearch P inside))).trans
    (memory.1 address outside),?_,?_,?_⟩
  · rw [later.live]
    exact memory.2.1
  · rw [later.live]
    exact memory.2.2.1
  · obtain ⟨written,pending,decomposition,output⟩:=later.emitted
    exact ⟨written,pending,decomposition,by simpa only [memory.2.2.2] using output⟩

theorem OutputRegion.output_length {P : Parameters} {before current : State} {cells : List Cell}
    (actual : OutputRegion P before cells current) : current.output.length≤before.output.length+cells.length := by
  obtain ⟨written,pending,decomposition,output⟩:=actual.emitted
  have length:=congrArg List.length decomposition
  simp only [List.length_append] at length
  rw [output,List.length_append]
  omega

end PDCompute.CoreSuffix
