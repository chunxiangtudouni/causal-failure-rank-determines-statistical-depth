module
public import Paid.PDCompute_Nat_Loop_Columns_002
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000
@[expose] public section
namespace PDCompute.NatLoop
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame PDCompute.NatControl
attribute [local irreducible] fullCellCode

/-- Original129 outer loop, including dirty Header20 and real reset, on one SAME-B trace. -/
theorem matrix_rows_trace_resources (mode : ReaderMode) (rootOrigin : ℕ) (input : List Cell)
    (origin : ℕ) (fetch : FetchesCode (solverLocatedProgram mode rootOrigin) origin (matrixPackCode mode origin))
    (P : Parameters) (fee penalty : ℚ) (base n k source remaining : ℕ)
    (caller : State) (incoming budget : ℕ)
    (context : SolverControlContext caller incoming base n k mode rootOrigin budget)
    (cells : FullCellSameB mode rootOrigin origin input P fee penalty base n k source budget)
    (avoids : EndpointAvoids mode P source base n k)
    (before : State) (values : ℕ → Cell) (row : ℕ)
    (finish : row+remaining=n+1) (hpc : before.pc=matrixRowTestPC origin)
    (header : Header before base values) (contents : MatrixRowContents P values fee penalty n k source row)
    (hbase : before.register .fresh=.natural base) (hsource : EndpointSource mode input P source before)
    (prior : DensePrefix before base k (solverEntry P fee penalty k) (row*(k+1)))
    (safe : RootD27.Bits.SafeBits before budget) :
    ∃ trace : List State, ∃ after : State, ∃ afterValues : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step (solverLocatedProgram mode rootOrigin) input first=some later) ∧
      time (solverLocatedProgram mode rootOrigin) trace ≤ matrixRowCost P k*remaining+135 ∧ Header after base afterValues ∧
      MatrixRowContents P afterValues fee penalty n k source (n+1) ∧
      DensePrefix after base k (solverEntry P fee penalty k) (entryCount n k) ∧
      SavedInputValues values afterValues ∧ after.register .fresh=.natural base ∧
      after.pc=matrixEndPC mode origin ∧ Frame before after base n k ∧ after.output=before.output ∧
      (∀ state ∈ trace,RegionMemory before state (workspace base n k)) ∧
      ∀ state∈trace,RootD27.Bits.SafeBits state budget := by
  let program:=solverLocatedProgram mode rootOrigin
  induction remaining generalizing before values row with
  | zero =>
    have rowEq : row=n+1 := by omega
    obtain ⟨trace,after,head,last,chain,bound,afterHeader,afterBase,afterPC,frame,output,resources⟩:=
      matrix_row_guard_trace_context mode rootOrigin origin input caller before incoming base n k row budget values
        context header hbase safe contents.rowValue contents.nValue hpc fetch
    have memory : ∀ state∈trace,HeaderMemory before state base:=fun state member=>(resources state member).1
    have bits : ∀ state∈trace,RootD27.Bits.SafeBits state budget:=fun state member=>(resources state member).2
    have beyond : ¬ row ≤ n := by omega
    have finalPrefix:=prior.header (HeaderMemory.trace_last memory last)
    refine ⟨trace,after,values,head,last,chain,?_,afterHeader,?_,?_,SavedInputValues.refl values,afterBase,?_,frame,output,?_,bits⟩
    · simpa only [Nat.mul_zero,Nat.zero_add] using bound
    · simpa only [rowEq] using contents
    · simpa only [rowEq,PDCompute.Solver.entryCount] using finalPrefix
    · simpa only [Comparison.nat,decide_eq_true_eq,ite_eq_right beyond] using afterPC
    · exact fun state member => (memory state member).region _ (headerRegion_subset_workspace base n k)
  | succ remaining ih =>
    have rowBound : row ≤ n := by omega
    obtain ⟨guardTrace,tested,guardHead,guardLast,guardChain,guardTime,testedHeader,testedBase,testedPC,
      guardFrame,guardOutput,guardResources⟩:=
      matrix_row_guard_trace_context mode rootOrigin origin input caller before incoming base n k row budget values
        context header hbase safe contents.rowValue contents.nValue hpc fetch
    have guardMemory : ∀ state∈guardTrace,HeaderMemory before state base:=fun state member=>(guardResources state member).1
    have guardBits : ∀ state∈guardTrace,RootD27.Bits.SafeBits state budget:=fun state member=>(guardResources state member).2
    have atColumnInit : tested.pc=matrixColumnInitPC origin := by
      simpa only [Comparison.nat,decide_eq_true_eq,ite_eq_left rowBound] using testedPC
    let zeroValues:=Function.update values 20 (.natural 0)
    obtain ⟨initTrace,initialized,initHead,initLast,initChain,initTime,initializedHeader,initializedBase,initializedPC,
      initFrame,initOutput,initResources⟩:=
      matrix_column_initialize_trace_context mode rootOrigin origin input caller tested incoming base n k budget values
        context testedHeader testedBase (guardBits tested (List.mem_of_getLast? guardLast)) atColumnInit fetch
    have initMemory : ∀ state∈initTrace,HeaderMemory tested state base:=fun state member=>(initResources state member).1
    have initBits : ∀ state∈initTrace,RootD27.Bits.SafeBits state budget:=fun state member=>(initResources state member).2
    have initBound : time program initTrace ≤ 330 := initTime
    have atColumnTest : initialized.pc=matrixColumnTestPC origin := initializedPC
    have initializedContents : MatrixContents P zeroValues fee penalty n k source row 0 := contents.column 0
    have initializedPrefix : DensePrefix initialized base k (solverEntry P fee penalty k) (row*(k+1)+0) := by
      exact (prior.header (HeaderMemory.trace_last guardMemory guardLast)).header (HeaderMemory.trace_last initMemory initLast)
    have initializedSource:=EndpointSource.frame_of_avoids mode input P source base n k before initialized hsource avoids
      (guardFrame.trans initFrame)
    obtain ⟨columnTrace,completed,columnValues,columnHead,columnLast,columnChain,columnTime,completedHeader,completedContents,
      completedPrefix,columnInputs,completedBase,completedPC,columnFrame,columnOutput,columnMemory,columnBits⟩:=
      matrix_columns_trace_resources mode rootOrigin input origin fetch P fee penalty base n k source row (k+1) caller incoming budget context cells avoids rowBound
        initialized zeroValues 0 (Nat.zero_add _) atColumnTest initializedHeader initializedContents initializedBase initializedSource initializedPrefix (initBits initialized (List.mem_of_getLast? initLast))
    obtain ⟨counterTrace,next,counterHead,counterLast,counterChain,counterTime,nextHeader,nextBase,nextPC,
      counterFrame,counterOutput,counterMemory,counterBits,_⟩:=matrix_row_backedge_trace_context mode rootOrigin origin input caller completed
        incoming base n k row budget columnValues context completedHeader completedBase (columnBits completed (List.mem_of_getLast? columnLast))
        completedContents.rowValue rowBound completedPC fetch
    let nextValues:=Function.update columnValues 19 (.natural (row+1))
    have nextContents : MatrixRowContents P nextValues fee penalty n k source (row+1) := (completedContents.row (row+1)).toRow
    have nextPrefix:=completedPrefix.header (HeaderMemory.trace_last counterMemory counterLast)
    have prefixFrame:=guardFrame.trans (initFrame.trans (columnFrame.trans counterFrame))
    have nextSource:=EndpointSource.frame_of_avoids mode input P source base n k before next hsource avoids prefixFrame
    have nextFinish : row+1+remaining=n+1 := by omega
    obtain ⟨laterTrace,after,afterValues,laterHead,laterLast,laterChain,laterTime,afterHeader,afterContents,afterPrefix,
      laterInputs,afterBase,afterPC,laterFrame,laterOutput,laterMemory,laterBits⟩:=
      ih (before:=next) (values:=nextValues) (row:=row+1) nextFinish nextPC nextHeader nextContents nextBase nextSource nextPrefix (counterBits next (List.mem_of_getLast? counterLast))
    have guardRegion : ∀ state ∈ guardTrace,RegionMemory before state (workspace base n k) :=
      fun state member => (guardMemory state member).region _ (headerRegion_subset_workspace base n k)
    have initRegion : ∀ state ∈ initTrace,RegionMemory tested state (workspace base n k) :=
      fun state member => (initMemory state member).region _ (headerRegion_subset_workspace base n k)
    have counterRegion : ∀ state ∈ counterTrace,RegionMemory completed state (workspace base n k) :=
      fun state member => (counterMemory state member).region _ (headerRegion_subset_workspace base n k)
    have join1:=joinTrace_spec program input guardTrace initTrace before tested initialized 135 330
      guardHead guardLast initHead initLast guardChain initChain guardTime initBound
    have memory1:=RegionMemory.join_trace guardTrace initTrace before tested _ guardLast guardRegion initRegion
    have join2:=joinTrace_spec program input (joinTrace guardTrace initTrace) columnTrace before initialized completed 465
      (matrixStepCost P*(k+1)+135) join1.1 join1.2.1 columnHead columnLast join1.2.2.1 columnChain join1.2.2.2 columnTime
    have memory2:=RegionMemory.join_trace (joinTrace guardTrace initTrace) columnTrace before initialized _ join1.2.1 memory1 columnMemory
    have join3:=joinTrace_spec program input (joinTrace (joinTrace guardTrace initTrace) columnTrace) counterTrace before completed next
      (465+(matrixStepCost P*(k+1)+135)) 150 join2.1 join2.2.1 counterHead counterLast join2.2.2.1 counterChain join2.2.2.2 counterTime
    have stepBound : time program (joinTrace (joinTrace (joinTrace guardTrace initTrace) columnTrace) counterTrace) ≤ matrixRowCost P k := by
      calc
        _ ≤ (465+(matrixStepCost P*(k+1)+135))+150 := join3.2.2.2
        _ = _ := by unfold matrixRowCost; ring
    have memory3:=RegionMemory.join_trace (joinTrace (joinTrace guardTrace initTrace) columnTrace) counterTrace before completed _ join2.2.1 memory2 counterRegion
    have join4:=joinTrace_spec program input (joinTrace (joinTrace (joinTrace guardTrace initTrace) columnTrace) counterTrace) laterTrace before next after
      (matrixRowCost P k) (matrixRowCost P k*remaining+135) join3.1 join3.2.1 laterHead laterLast join3.2.2.1 laterChain stepBound laterTime
    have bits1:=PDCompute.Pack.joinTrace_invariant guardTrace initTrace (fun state=>RootD27.Bits.SafeBits state budget) guardBits initBits
    have bits2:=PDCompute.Pack.joinTrace_invariant (joinTrace guardTrace initTrace) columnTrace (fun state=>RootD27.Bits.SafeBits state budget) bits1 columnBits
    have bits3:=PDCompute.Pack.joinTrace_invariant (joinTrace (joinTrace guardTrace initTrace) columnTrace) counterTrace
      (fun state=>RootD27.Bits.SafeBits state budget) bits2 counterBits
    have bits4:=PDCompute.Pack.joinTrace_invariant (joinTrace (joinTrace (joinTrace guardTrace initTrace) columnTrace) counterTrace) laterTrace
      (fun state=>RootD27.Bits.SafeBits state budget) bits3 laterBits
    have initInputs : SavedInputValues values zeroValues := SavedInputValues.update values 20 _ (by decide)
    have nextInputs : SavedInputValues values nextValues :=
      (initInputs.trans columnInputs).trans (SavedInputValues.update columnValues 19 _ (by decide))
    refine ⟨joinTrace (joinTrace (joinTrace (joinTrace guardTrace initTrace) columnTrace) counterTrace) laterTrace,after,afterValues,
      join4.1,join4.2.1,join4.2.2.1,?_,afterHeader,afterContents,afterPrefix,nextInputs.trans laterInputs,afterBase,afterPC,
      prefixFrame.trans laterFrame,laterOutput.trans (counterOutput.trans (columnOutput.trans (initOutput.trans guardOutput))),
      RegionMemory.join_trace _ laterTrace before next _ join3.2.1 memory3 laterMemory,bits4⟩
    calc
      _ ≤ matrixRowCost P k+(matrixRowCost P k*remaining+135) := join4.2.2.2
      _ = _ := by ring

end PDCompute.NatLoop
