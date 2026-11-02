module
public import Paid.PDCompute_Nat_Loop_CellCertificate_001
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000
@[expose] public section
namespace PDCompute.NatLoop
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame PDCompute.NatControl
attribute [local irreducible] fullCellCode

/-- Original128 execution with one unchanged caller budget and an explicit internal actual-fullcell component. -/
theorem matrix_columns_trace_resources (mode : ReaderMode) (rootOrigin : ℕ) (input : List Cell)
    (origin : ℕ) (fetch : FetchesCode (solverLocatedProgram mode rootOrigin) origin (matrixPackCode mode origin))
    (P : Parameters) (fee penalty : ℚ) (base n k source row remaining : ℕ)
    (caller : State) (incoming budget : ℕ)
    (context : SolverControlContext caller incoming base n k mode rootOrigin budget)
    (cells : FullCellSameB mode rootOrigin origin input P fee penalty base n k source budget)
    (avoids : EndpointAvoids mode P source base n k) (rowBound : row ≤ n)
    (before : State) (values : ℕ → Cell) (column : ℕ)
    (finish : column+remaining=k+1) (hpc : before.pc=matrixColumnTestPC origin)
    (header : Header before base values) (contents : MatrixContents P values fee penalty n k source row column)
    (hbase : before.register .fresh=.natural base) (hsource : EndpointSource mode input P source before)
    (prior : DensePrefix before base k (solverEntry P fee penalty k) (row*(k+1)+column))
    (safe : RootD27.Bits.SafeBits before budget) :
    ∃ trace : List State, ∃ after : State, ∃ afterValues : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step (solverLocatedProgram mode rootOrigin) input first=some later) ∧
      time (solverLocatedProgram mode rootOrigin) trace ≤ matrixStepCost P*remaining+135 ∧ Header after base afterValues ∧
      MatrixContents P afterValues fee penalty n k source row (k+1) ∧
      DensePrefix after base k (solverEntry P fee penalty k) ((row+1)*(k+1)) ∧
      SavedInputValues values afterValues ∧ after.register .fresh=.natural base ∧
      after.pc=matrixRowAdvancePC mode origin ∧ Frame before after base n k ∧ after.output=before.output ∧
      (∀ state ∈ trace,RegionMemory before state (workspace base n k)) ∧
      ∀ state∈trace,RootD27.Bits.SafeBits state budget := by
  let program:=solverLocatedProgram mode rootOrigin
  have matrixFetch : FetchesCode program origin (matrixCode mode origin):=fetch.append_left
  induction remaining generalizing before values column with
  | zero =>
    have columnEq : column=k+1 := by omega
    obtain ⟨trace,after,head,last,chain,bound,afterHeader,afterBase,afterPC,frame,output,resources⟩:=
      matrix_column_guard_trace_context mode rootOrigin origin input caller before incoming base n k column budget values
        context header hbase safe contents.columnValue contents.kValue hpc fetch
    have memory : ∀ state∈trace,HeaderMemory before state base:=fun state member=>(resources state member).1
    have bits : ∀ state∈trace,RootD27.Bits.SafeBits state budget:=fun state member=>(resources state member).2
    have beyond : ¬ column ≤ k := by omega
    have finalPrefix:=prior.header (HeaderMemory.trace_last memory last)
    have indexEq : row*(k+1)+column=(row+1)*(k+1) := by rw [columnEq]; ring
    refine ⟨trace,after,values,head,last,chain,?_,afterHeader,?_,?_,SavedInputValues.refl values,afterBase,?_,frame,output,?_,bits⟩
    · simpa only [Nat.mul_zero,Nat.zero_add] using bound
    · simpa only [columnEq] using contents
    · simpa only [indexEq] using finalPrefix
    · simpa only [Comparison.nat,decide_eq_true_eq,ite_eq_right beyond] using afterPC
    · exact fun state member => (memory state member).region _ (headerRegion_subset_workspace base n k)
  | succ remaining ih =>
    have columnBound : column ≤ k := by omega
    obtain ⟨guardTrace,tested,guardHead,guardLast,guardChain,guardTime,testedHeader,testedBase,testedPC,
      guardFrame,guardOutput,guardResources⟩:=
      matrix_column_guard_trace_context mode rootOrigin origin input caller before incoming base n k column budget values
        context header hbase safe contents.columnValue contents.kValue hpc fetch
    have guardMemory : ∀ state∈guardTrace,HeaderMemory before state base:=fun state member=>(guardResources state member).1
    have guardBits : ∀ state∈guardTrace,RootD27.Bits.SafeBits state budget:=fun state member=>(guardResources state member).2
    have atCell : tested.pc=matrixCellPC origin := by
      simpa only [Comparison.nat,decide_eq_true_eq,ite_eq_left columnBound] using testedPC
    have testedSource:=EndpointSource.frame_of_avoids mode input P source base n k before tested hsource avoids guardFrame
    have testedPrior:=prior.header (HeaderMemory.trace_last guardMemory guardLast)
    obtain ⟨cellTrace,written,cellValues,cellHead,cellLast,cellChain,cellTime,cellHeader,cellPrefix,cellControls,writtenBase,cellPC,
      cellFrame,cellOutput,cellMemory,cellBits⟩:=
      cells row column tested values
        atCell testedHeader testedBase testedSource avoids contents.sourceValue contents.penaltyValue contents.kValue contents.feeValue
        contents.lastValue contents.rowValue contents.columnValue rowBound columnBound testedPrior (guardBits tested (List.mem_of_getLast? guardLast)) (matrix_cell_fetch mode program origin matrixFetch)
    have cellContents:=contents.preserve (fun slot range => cellControls slot range)
    obtain ⟨counterTrace,next,counterHead,counterLast,counterChain,counterTime,nextHeader,nextBase,nextPC,
      counterFrame,counterOutput,counterMemory,counterBits,_⟩:=matrix_column_backedge_trace_context mode rootOrigin origin input caller written
        incoming base n k column budget cellValues context cellHeader writtenBase (cellBits written (List.mem_of_getLast? cellLast))
        cellContents.columnValue columnBound cellPC fetch
    let nextValues:=Function.update cellValues 20 (.natural (column+1))
    have nextContents : MatrixContents P nextValues fee penalty n k source row (column+1) := cellContents.column (column+1)
    have nextPrefix : DensePrefix next base k (solverEntry P fee penalty k) (row*(k+1)+(column+1)) := by
      simpa only [Nat.add_assoc] using cellPrefix.header (HeaderMemory.trace_last counterMemory counterLast)
    have prefixFrame:=guardFrame.trans (cellFrame.trans counterFrame)
    have nextSource:=EndpointSource.frame_of_avoids mode input P source base n k before next hsource avoids prefixFrame
    have nextFinish : column+1+remaining=k+1 := by omega
    obtain ⟨laterTrace,after,afterValues,laterHead,laterLast,laterChain,laterTime,afterHeader,afterContents,afterPrefix,
      laterInputs,afterBase,afterPC,laterFrame,laterOutput,laterMemory,laterBits⟩:=
      ih (before:=next) (values:=nextValues) (column:=column+1) nextFinish nextPC nextHeader nextContents nextBase nextSource nextPrefix (counterBits next (List.mem_of_getLast? counterLast))
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
    have bits1:=PDCompute.Pack.joinTrace_invariant guardTrace cellTrace (fun state=>RootD27.Bits.SafeBits state budget) guardBits cellBits
    have bits2:=PDCompute.Pack.joinTrace_invariant (joinTrace guardTrace cellTrace) counterTrace (fun state=>RootD27.Bits.SafeBits state budget) bits1 counterBits
    have bits3:=PDCompute.Pack.joinTrace_invariant (joinTrace (joinTrace guardTrace cellTrace) counterTrace) laterTrace
      (fun state=>RootD27.Bits.SafeBits state budget) bits2 laterBits
    have cellInputs : SavedInputValues values cellValues := fun slot inside => cellControls slot (Or.inl inside)
    have nextInputs : SavedInputValues values nextValues := cellInputs.trans (SavedInputValues.update cellValues 20 _ (by decide))
    refine ⟨joinTrace (joinTrace (joinTrace guardTrace cellTrace) counterTrace) laterTrace,after,afterValues,
      join3.1,join3.2.1,join3.2.2.1,?_,afterHeader,afterContents,afterPrefix,nextInputs.trans laterInputs,afterBase,afterPC,
      prefixFrame.trans laterFrame,laterOutput.trans (counterOutput.trans (cellOutput.trans guardOutput)),
      RegionMemory.join_trace _ laterTrace before next _ join2.2.1 memory2 laterMemory,bits3⟩
    calc
      _ ≤ matrixStepCost P+(matrixStepCost P*remaining+135) := join3.2.2.2
      _ = _ := by ring

end PDCompute.NatLoop
