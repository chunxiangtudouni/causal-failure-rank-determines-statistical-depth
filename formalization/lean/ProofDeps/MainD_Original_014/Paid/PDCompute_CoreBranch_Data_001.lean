module
public import Paid.RootD27Core_BranchUpdate_085

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace PDCompute.CoreBranch
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open RootD27.Core PDLower.CoreSearch PDCompute.CoreSearchLoop

def midpointPenalty (lower upper : MultiplierSolve) : ℚ:=(lower.multiplier+upper.multiplier)/2

/-- EXACT physical post of frozen original midpoint64. None of the
comparison results or chosen branches is supplied by this certificate. -/
structure MidpointData (P : Parameters) (fee penalty : ℚ) (state : State) : Prop where
  price : state.heap 24=.rational penalty
  statistics : HeapList state 25 (originalStatistics P fee penalty)
  saved : HeapList state 46 [.natural (resultBase (99+2*P.certificate.M) P.certificate.stages P.tools),
    .natural (originalSolveEncoding P fee penalty).length]
  table : HeapList state (resultBase (99+2*P.certificate.M) P.certificate.stages P.tools)
    (originalSolveEncoding P fee penalty)

theorem MidpointData.risk {P : Parameters} {fee penalty : ℚ} {state : State}
    (data : MidpointData P fee penalty state) :
    state.heap 27=.rational (P.solveRisk (P.cachedSolveMultiplier P.endpointCache fee penalty)) :=
  PDLower.CalibrationCompute.HeapList.value data.statistics 2 (by change 2<3;decide)

theorem MidpointData.preserve {P : Parameters} {fee penalty : ℚ} {before after : State}
    (data : MidpointData P fee penalty before) (memory : RegionMemory before after {40}) :
    MidpointData P fee penalty after := by
  refine ⟨(memory.1 24 (by decide)).trans data.price,?_,?_,?_⟩
  · apply memory.heapList data.statistics
    intro offset inside
    change offset<3 at inside
    simp only [Finset.mem_singleton]
    omega
  · apply memory.heapList data.saved
    intro offset _inside
    simp only [Finset.mem_singleton]
    omega
  · apply memory.heapList data.table
    intro offset _inside
    have bound:=dense_result_source_bound (99+2*P.certificate.M) P.certificate.stages P.tools
    simp only [Finset.mem_singleton]
    omega

theorem ready_after_comparison {P : Parameters} {fee : ℚ} {before after : State}
    (ready : Ready P fee before) (header : Header after 0 (fun slot=>after.heap slot))
    (fresh : after.register .fresh=.natural 0) (memory : RegionMemory before after {40}) : Ready P fee after := by
  refine ⟨header,fresh,?_,?_⟩
  · apply memory.heapList ready.prepared
    intro offset inside
    change offset<13 at inside
    simp only [Finset.mem_singleton]
    omega
  · apply memory.heapList ready.cache
    intro offset _inside
    simp only [Finset.mem_singleton]
    omega

def branchRegion (P : Parameters) : Finset ℕ :=
  (scalarRegion∪{46,47})∪
    (cellRegion (retainedTableBase (99+2*P.certificate.M) P.certificate.stages P.tools false)
      (retainedTableCapacity P.certificate.stages P.tools)∪
     cellRegion (retainedTableBase (99+2*P.certificate.M) P.certificate.stages P.tools true)
      (retainedTableCapacity P.certificate.stages P.tools))

theorem scalar_subset_branch (P : Parameters) : scalarRegion⊆branchRegion P :=
  Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left

theorem encoding_capacity (P : Parameters) (fee penalty : ℚ) :
    (originalSolveEncoding P fee penalty).length≤retainedTableCapacity P.certificate.stages P.tools :=
  (original_table_capacity P fee penalty P.certificate.stages P.tools).trans
    (retained_capacity_enough P.certificate.stages P.tools)

theorem update_region_subset (P : Parameters) (fee penalty : ℚ) (upper : Bool) :
    savedCopyRegion P fee penalty upper∪scalarRegion⊆branchRegion P := by
  apply Finset.union_subset
  · intro address member
    rcases Finset.mem_union.mp member with copied|lengthSlot
    · rcases Finset.mem_union.mp copied with scratch|target
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ scratch)
      · have bound:=(mem_cellRegion_iff _ _ address).mp target
        have capacity:=encoding_capacity P fee penalty
        have full : address∈cellRegion (retainedTableBase (99+2*P.certificate.M) P.certificate.stages P.tools upper)
            (retainedTableCapacity P.certificate.stages P.tools) :=
          (mem_cellRegion_iff _ _ address).mpr ⟨bound.1,by omega⟩
        apply Finset.mem_union_right
        cases upper with
        | false=>exact Finset.mem_union_left _ full
        | true=>exact Finset.mem_union_right _ full
    · have same:=Finset.mem_singleton.mp lengthSlot
      subst address
      apply scalar_subset_branch
      cases upper <;> decide
  · exact scalar_subset_branch P

theorem suffix_fetch_parts (program : Program) (origin entry decrementPC : ℕ)
    (fetched : FetchesCode program origin (bisectionBodyCode origin entry decrementPC)) :
    FetchesCode program (origin+251) (comparisonDecisionCode .equal 27 3 (origin+262) (origin+273)) ∧
    FetchesCode program (origin+262) (comparisonDecisionCode .less 3 27 (origin+435) (origin+354)) ∧
    FetchesCode program (origin+273) (branchUpdateCode (origin+273) false true decrementPC) ∧
    FetchesCode program (origin+354) (branchUpdateCode (origin+354) false false decrementPC) ∧
    FetchesCode program (origin+435) (branchUpdateCode (origin+435) true false decrementPC) := by
  have parts:=bisectionBody_fetch_parts program origin entry decrementPC fetched
  have middle:=parts.2.2.1
  simp only [midpointDecisionCode,List.append_assoc] at middle
  refine ⟨?_,?_,parts.2.2.2.2.1,parts.2.2.2.2.2.1,parts.2.2.2.2.2.2⟩
  · simpa only [midpointSave_length,comparisonDecisionCode,Nat.add_assoc] using middle.append_right
  · simpa only [comparisonDecisionCode,riskDecisionCode] using parts.2.2.2.1

end PDCompute.CoreBranch
