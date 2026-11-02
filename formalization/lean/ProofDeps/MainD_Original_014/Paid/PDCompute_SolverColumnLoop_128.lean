module

public import Paid.PDCompute_SolverFullCell_119
public import Paid.PDCompute_SolverCounterBack_122
public import Paid.PDCompute_SolverMatrixFetch_120
public import Paid.PDCompute_SolverMatrixContents_123
public import Paid.PDCompute_SolverRegionSpace_124

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

attribute [local irreducible] fullCellCode

theorem fetch_append_control (program : Program) (origin : ℕ) (code : List Instruction) (instruction : Instruction)
    (first : FetchesCode program origin code) (last : program[origin+code.length]?=some instruction) :
    FetchesCode program origin (code++[instruction]) := by
  intro offset inside
  by_cases proper : offset < code.length
  · exact (first offset proper).trans (List.getElem?_append_left proper).symm
  · have same : offset=code.length := by simp only [List.length_append,List.length_singleton] at inside; omega
    subst offset
    simpa only [List.getElem?_append_right (le_refl _),Nat.sub_self,List.getElem?_cons_zero] using last

def matrixStepCost (P : Parameters) : ℕ := 2500*(P.certificate.M+1)+23685

/-- COMPLETE actual inner loop of matrix113, with fullCell119,
the real natural guard and real9-op counter/backedge.
All completed cells are actual original entries, and EVERY prefix has
the true fixed-workspace footprint. -/
theorem matrix_columns_trace_memory (mode : ReaderMode) (program : Program) (input : List Cell)
    (origin : ℕ) (fetch : FetchesCode program origin (matrixCode mode origin))
    (P : Parameters) (fee penalty : ℚ) (base n k source row remaining : ℕ)
    (avoids : EndpointAvoids mode P source base n k) (rowBound : row ≤ n)
    (before : State) (values : ℕ → Cell) (column : ℕ)
    (finish : column+remaining=k+1) (hpc : before.pc=matrixColumnTestPC origin)
    (header : Header before base values) (contents : MatrixContents P values fee penalty n k source row column)
    (hbase : before.register .fresh=.natural base) (hsource : EndpointSource mode input P source before)
    (prior : DensePrefix before base k (solverEntry P fee penalty k) (row*(k+1)+column)) :
    ∃ trace : List State, ∃ after : State, ∃ afterValues : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ matrixStepCost P*remaining+135 ∧ Header after base afterValues ∧
      MatrixContents P afterValues fee penalty n k source row (k+1) ∧
      DensePrefix after base k (solverEntry P fee penalty k) ((row+1)*(k+1)) ∧
      SavedInputValues values afterValues ∧ after.register .fresh=.natural base ∧
      after.pc=matrixRowAdvancePC mode origin ∧ Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace,RegionMemory before state (workspace base n k) := by
  induction remaining generalizing before values column with
  | zero =>
    have columnEq : column=k+1 := by omega
    have guardFetch : FetchesCode program before.pc
        (naturalBranchCode .lessEqual 20 4 (matrixRowAdvancePC mode origin) (matrixCellPC origin)) := by
      rw [hpc]
      exact matrix_column_test_fetch mode program origin fetch
    obtain ⟨trace,after,head,last,chain,bound,afterHeader,afterBase,afterPC,frame,output,memory⟩:=
      naturalBranch_trace_memory program input before base n k 20 4 column k
        (matrixRowAdvancePC mode origin) (matrixCellPC origin) .lessEqual values header (by decide) (by decide)
        contents.columnValue contents.kValue hbase guardFetch
    have beyond : ¬ column ≤ k := by omega
    have finalPrefix:=prior.header (HeaderMemory.trace_last memory last)
    have indexEq : row*(k+1)+column=(row+1)*(k+1) := by rw [columnEq]; ring
    refine ⟨trace,after,values,head,last,chain,?_,afterHeader,?_,?_,SavedInputValues.refl values,afterBase,?_,frame,output,?_⟩
    · simpa only [Nat.mul_zero,Nat.zero_add] using bound
    · simpa only [columnEq] using contents
    · simpa only [indexEq] using finalPrefix
    · simpa only [Comparison.nat,decide_eq_true_eq,ite_eq_right beyond] using afterPC
    · exact fun state member => (memory state member).region _ (headerRegion_subset_workspace base n k)
  | succ remaining ih =>
    have columnBound : column ≤ k := by omega
    have guardFetch : FetchesCode program before.pc
        (naturalBranchCode .lessEqual 20 4 (matrixRowAdvancePC mode origin) (matrixCellPC origin)) := by
      rw [hpc]
      exact matrix_column_test_fetch mode program origin fetch
    obtain ⟨guardTrace,tested,guardHead,guardLast,guardChain,guardTime,testedHeader,testedBase,testedPC,
      guardFrame,guardOutput,guardMemory⟩:=
      naturalBranch_trace_memory program input before base n k 20 4 column k
        (matrixRowAdvancePC mode origin) (matrixCellPC origin) .lessEqual values header (by decide) (by decide)
        contents.columnValue contents.kValue hbase guardFetch
    have atCell : tested.pc=matrixCellPC origin := by
      simpa only [Comparison.nat,decide_eq_true_eq,ite_eq_left columnBound] using testedPC
    have testedSource:=EndpointSource.frame_of_avoids mode input P source base n k before tested hsource avoids guardFrame
    have testedPrior:=prior.header (HeaderMemory.trace_last guardMemory guardLast)
    obtain ⟨cellTrace,written,cellValues,cellHead,cellLast,cellChain,cellTime,cellHeader,cellPrefix,cellControls,writtenBase,cellPC,
      cellFrame,cellOutput,cellMemory⟩:=
      fullCell_trace_memory mode program input (matrixCellPC origin) P fee penalty row column tested base n k source values
        atCell testedHeader testedBase testedSource avoids contents.sourceValue contents.penaltyValue contents.kValue contents.feeValue
        contents.lastValue contents.rowValue contents.columnValue rowBound columnBound testedPrior (matrix_cell_fetch mode program origin fetch)
    have cellContents:=contents.preserve (fun slot range => cellControls slot range)
    have backFetch : FetchesCode program written.pc (counterBackCode 20 1 (matrixColumnTestPC origin)) := by
      rw [cellPC]
      apply fetch_append_control program _ _ _ (matrix_column_advance_fetch mode program origin fetch)
      have back:=matrix_column_back_fetch mode program origin fetch
      simpa only [matrixColumnBackPC] using back
    obtain ⟨counterTrace,next,counterHead,counterLast,counterChain,counterTime,nextHeader,nextBase,nextPC,
      counterFrame,counterOutput,counterMemory,_⟩:=counterBack_trace_memory_pc program input written base n k 20 column 1
        (matrixColumnTestPC origin) cellValues cellHeader writtenBase (by decide) cellContents.columnValue backFetch
    let nextValues:=Function.update cellValues 20 (.natural (column+1))
    have nextContents : MatrixContents P nextValues fee penalty n k source row (column+1) := cellContents.column (column+1)
    have nextPrefix : DensePrefix next base k (solverEntry P fee penalty k) (row*(k+1)+(column+1)) := by
      simpa only [Nat.add_assoc] using cellPrefix.header (HeaderMemory.trace_last counterMemory counterLast)
    have prefixFrame:=guardFrame.trans (cellFrame.trans counterFrame)
    have nextSource:=EndpointSource.frame_of_avoids mode input P source base n k before next hsource avoids prefixFrame
    have nextFinish : column+1+remaining=k+1 := by omega
    obtain ⟨laterTrace,after,afterValues,laterHead,laterLast,laterChain,laterTime,afterHeader,afterContents,afterPrefix,
      laterInputs,afterBase,afterPC,laterFrame,laterOutput,laterMemory⟩:=
      ih (before:=next) (values:=nextValues) (column:=column+1) nextFinish nextPC nextHeader nextContents nextBase nextSource nextPrefix
    have cellRegionInside : cellRegion base headerWords ∪ cellRegion (cellBase base k row column) 6 ⊆ workspace base n k := by
      intro address member
      rcases Finset.mem_union.mp member with inHeader|inCell
      · exact headerRegion_subset_workspace base n k inHeader
      · obtain ⟨offset,inside,rfl⟩:=Finset.mem_image.mp inCell
        exact denseCell_mem_workspace base n k row column offset rowBound columnBound (Finset.mem_range.mp inside)
    have guardRegion : ∀ state ∈ guardTrace,RegionMemory before state (workspace base n k) :=
      fun state member => (guardMemory state member).region _ (headerRegion_subset_workspace base n k)
    have cellRegion : ∀ state ∈ cellTrace,RegionMemory tested state (workspace base n k) :=
      fun state member => (cellMemory state member).enlarge cellRegionInside
    have counterRegion : ∀ state ∈ counterTrace,RegionMemory written state (workspace base n k) :=
      fun state member => (counterMemory state member).region _ (headerRegion_subset_workspace base n k)
    have join1:=joinTrace_spec program input guardTrace cellTrace before tested written 135 (2500*(P.certificate.M+1)+23400)
      guardHead guardLast cellHead cellLast guardChain cellChain guardTime cellTime
    have memory1:=RegionMemory.join_trace guardTrace cellTrace before tested _ guardLast guardRegion cellRegion
    have join2:=joinTrace_spec program input (joinTrace guardTrace cellTrace) counterTrace before written next
      (135+(2500*(P.certificate.M+1)+23400)) 150 join1.1 join1.2.1 counterHead counterLast join1.2.2.1 counterChain join1.2.2.2 counterTime
    have stepBound : time program (joinTrace (joinTrace guardTrace cellTrace) counterTrace) ≤ matrixStepCost P := by
      calc
        _ ≤ (135+(2500*(P.certificate.M+1)+23400))+150 := join2.2.2.2
        _ = _ := by unfold matrixStepCost; ring
    have memory2:=RegionMemory.join_trace (joinTrace guardTrace cellTrace) counterTrace before written _ join1.2.1 memory1 counterRegion
    have join3:=joinTrace_spec program input (joinTrace (joinTrace guardTrace cellTrace) counterTrace) laterTrace before next after
      (matrixStepCost P) (matrixStepCost P*remaining+135) join2.1 join2.2.1 laterHead laterLast join2.2.2.1 laterChain stepBound laterTime
    have cellInputs : SavedInputValues values cellValues := fun slot inside => cellControls slot (Or.inl inside)
    have nextInputs : SavedInputValues values nextValues := cellInputs.trans (SavedInputValues.update cellValues 20 _ (by decide))
    refine ⟨joinTrace (joinTrace (joinTrace guardTrace cellTrace) counterTrace) laterTrace,after,afterValues,
      join3.1,join3.2.1,join3.2.2.1,?_,afterHeader,afterContents,afterPrefix,nextInputs.trans laterInputs,afterBase,afterPC,
      prefixFrame.trans laterFrame,laterOutput.trans (counterOutput.trans (cellOutput.trans guardOutput)),
      RegionMemory.join_trace _ laterTrace before next _ join2.2.1 memory2 laterMemory⟩
    calc
      _ ≤ matrixStepCost P+(matrixStepCost P*remaining+135) := join3.2.2.2
      _ = _ := by ring

end PDCompute.Solver
