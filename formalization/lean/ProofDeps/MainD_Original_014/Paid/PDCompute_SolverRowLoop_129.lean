module

public import Paid.PDCompute_SolverColumnLoop_128

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

attribute [local irreducible] fullCellCode

/-- The outer test does not read incoming Header20: it resets that
column counter only after the row test succeeds. -/
structure MatrixRowContents (P : Parameters) (values : ℕ → Cell) (fee penalty : ℚ) (n k source row : ℕ) : Prop where
  sourceValue : values 0=.natural source
  penaltyValue : values 2=.rational penalty
  nValue : values 3=.natural n
  kValue : values 4=.natural k
  feeValue : values 5=.rational fee
  lastValue : values 6=.natural P.certificate.M
  rowValue : values 19=.natural row

theorem MatrixRowContents.column {P : Parameters} {values : ℕ → Cell} {fee penalty : ℚ} {n k source row : ℕ}
    (contents : MatrixRowContents P values fee penalty n k source row) (column : ℕ) :
    MatrixContents P (Function.update values 20 (.natural column)) fee penalty n k source row column :=
  ⟨contents.sourceValue,contents.penaltyValue,contents.nValue,contents.kValue,contents.feeValue,contents.lastValue,contents.rowValue,rfl⟩

theorem MatrixContents.toRow {P : Parameters} {values : ℕ → Cell} {fee penalty : ℚ} {n k source row column : ℕ}
    (contents : MatrixContents P values fee penalty n k source row column) :
    MatrixRowContents P values fee penalty n k source row :=
  ⟨contents.sourceValue,contents.penaltyValue,contents.nValue,contents.kValue,contents.feeValue,contents.lastValue,contents.rowValue⟩

def matrixRowCost (P : Parameters) (k : ℕ) : ℕ := matrixStepCost P*(k+1)+750

/-- COMPLETE actual outer loop: every original row is constructed by
the actual inner loop, and the original complete dense table follows.
Neither a completed row nor a cell execution is assumed as an oracle. -/
theorem matrix_rows_trace_memory (mode : ReaderMode) (program : Program) (input : List Cell)
    (origin : ℕ) (fetch : FetchesCode program origin (matrixCode mode origin))
    (P : Parameters) (fee penalty : ℚ) (base n k source remaining : ℕ)
    (avoids : EndpointAvoids mode P source base n k)
    (before : State) (values : ℕ → Cell) (row : ℕ)
    (finish : row+remaining=n+1) (hpc : before.pc=matrixRowTestPC origin)
    (header : Header before base values) (contents : MatrixRowContents P values fee penalty n k source row)
    (hbase : before.register .fresh=.natural base) (hsource : EndpointSource mode input P source before)
    (prior : DensePrefix before base k (solverEntry P fee penalty k) (row*(k+1))) :
    ∃ trace : List State, ∃ after : State, ∃ afterValues : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ matrixRowCost P k*remaining+135 ∧ Header after base afterValues ∧
      MatrixRowContents P afterValues fee penalty n k source (n+1) ∧
      DensePrefix after base k (solverEntry P fee penalty k) (entryCount n k) ∧
      SavedInputValues values afterValues ∧ after.register .fresh=.natural base ∧
      after.pc=matrixEndPC mode origin ∧ Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace,RegionMemory before state (workspace base n k) := by
  induction remaining generalizing before values row with
  | zero =>
    have rowEq : row=n+1 := by omega
    have guardFetch : FetchesCode program before.pc
        (naturalBranchCode .lessEqual 19 3 (matrixEndPC mode origin) (matrixColumnInitPC origin)) := by
      rw [hpc]
      exact matrix_row_test_fetch mode program origin fetch
    obtain ⟨trace,after,head,last,chain,bound,afterHeader,afterBase,afterPC,frame,output,memory⟩:=
      naturalBranch_trace_memory program input before base n k 19 3 row n
        (matrixEndPC mode origin) (matrixColumnInitPC origin) .lessEqual values header (by decide) (by decide)
        contents.rowValue contents.nValue hbase guardFetch
    have beyond : ¬ row ≤ n := by omega
    have finalPrefix:=prior.header (HeaderMemory.trace_last memory last)
    refine ⟨trace,after,values,head,last,chain,?_,afterHeader,?_,?_,SavedInputValues.refl values,afterBase,?_,frame,output,?_⟩
    · simpa only [Nat.mul_zero,Nat.zero_add] using bound
    · simpa only [rowEq] using contents
    · simpa only [rowEq,entryCount] using finalPrefix
    · simpa only [Comparison.nat,decide_eq_true_eq,ite_eq_right beyond] using afterPC
    · exact fun state member => (memory state member).region _ (headerRegion_subset_workspace base n k)
  | succ remaining ih =>
    have rowBound : row ≤ n := by omega
    have guardFetch : FetchesCode program before.pc
        (naturalBranchCode .lessEqual 19 3 (matrixEndPC mode origin) (matrixColumnInitPC origin)) := by
      rw [hpc]
      exact matrix_row_test_fetch mode program origin fetch
    obtain ⟨guardTrace,tested,guardHead,guardLast,guardChain,guardTime,testedHeader,testedBase,testedPC,
      guardFrame,guardOutput,guardMemory⟩:=
      naturalBranch_trace_memory program input before base n k 19 3 row n
        (matrixEndPC mode origin) (matrixColumnInitPC origin) .lessEqual values header (by decide) (by decide)
        contents.rowValue contents.nValue hbase guardFetch
    have atColumnInit : tested.pc=matrixColumnInitPC origin := by
      simpa only [Comparison.nat,decide_eq_true_eq,ite_eq_left rowBound] using testedPC
    let zeroValues:=Function.update values 20 (.natural 0)
    have initFetch : FetchesCode program tested.pc (headerCode [.constant 20 (.natural 0)]) := by
      rw [atColumnInit]
      exact matrix_column_init_fetch mode program origin fetch
    obtain ⟨initTrace,initialized,initHead,initLast,initChain,initTime,initializedHeader,initializedBase,initializedPC,
      initFrame,initOutput,initMemory⟩:=
      headerCode_trace_memory [.constant 20 (.natural 0)] program input tested base n k values zeroValues
        (by intro command member; have same:=List.mem_singleton.mp member; subst command; dsimp only [HeaderCommand.Valid,headerWords]; decide)
        testedHeader testedBase rfl initFetch
    have initBound : time program initTrace ≤ 330 := initTime
    have atColumnTest : initialized.pc=matrixColumnTestPC origin := by rw [initializedPC,atColumnInit]; rfl
    have initializedContents : MatrixContents P zeroValues fee penalty n k source row 0 := contents.column 0
    have initializedPrefix : DensePrefix initialized base k (solverEntry P fee penalty k) (row*(k+1)+0) := by
      exact (prior.header (HeaderMemory.trace_last guardMemory guardLast)).header (HeaderMemory.trace_last initMemory initLast)
    have initializedSource:=EndpointSource.frame_of_avoids mode input P source base n k before initialized hsource avoids
      (guardFrame.trans initFrame)
    obtain ⟨columnTrace,completed,columnValues,columnHead,columnLast,columnChain,columnTime,completedHeader,completedContents,
      completedPrefix,columnInputs,completedBase,completedPC,columnFrame,columnOutput,columnMemory⟩:=
      matrix_columns_trace_memory mode program input origin fetch P fee penalty base n k source row (k+1) avoids rowBound
        initialized zeroValues 0 (Nat.zero_add _) atColumnTest initializedHeader initializedContents initializedBase initializedSource initializedPrefix
    have backFetch : FetchesCode program completed.pc (counterBackCode 19 1 (matrixRowTestPC origin)) := by
      rw [completedPC]
      apply fetch_append_control program _ _ _ (matrix_row_advance_fetch mode program origin fetch)
      have back:=matrix_row_back_fetch mode program origin fetch
      simpa only [matrixRowBackPC] using back
    obtain ⟨counterTrace,next,counterHead,counterLast,counterChain,counterTime,nextHeader,nextBase,nextPC,
      counterFrame,counterOutput,counterMemory,_⟩:=counterBack_trace_memory_pc program input completed base n k 19 row 1
        (matrixRowTestPC origin) columnValues completedHeader completedBase (by decide) completedContents.rowValue backFetch
    let nextValues:=Function.update columnValues 19 (.natural (row+1))
    have nextContents : MatrixRowContents P nextValues fee penalty n k source (row+1) := (completedContents.row (row+1)).toRow
    have nextPrefix:=completedPrefix.header (HeaderMemory.trace_last counterMemory counterLast)
    have prefixFrame:=guardFrame.trans (initFrame.trans (columnFrame.trans counterFrame))
    have nextSource:=EndpointSource.frame_of_avoids mode input P source base n k before next hsource avoids prefixFrame
    have nextFinish : row+1+remaining=n+1 := by omega
    obtain ⟨laterTrace,after,afterValues,laterHead,laterLast,laterChain,laterTime,afterHeader,afterContents,afterPrefix,
      laterInputs,afterBase,afterPC,laterFrame,laterOutput,laterMemory⟩:=
      ih (before:=next) (values:=nextValues) (row:=row+1) nextFinish nextPC nextHeader nextContents nextBase nextSource nextPrefix
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
    have initInputs : SavedInputValues values zeroValues := SavedInputValues.update values 20 _ (by decide)
    have nextInputs : SavedInputValues values nextValues :=
      (initInputs.trans columnInputs).trans (SavedInputValues.update columnValues 19 _ (by decide))
    refine ⟨joinTrace (joinTrace (joinTrace (joinTrace guardTrace initTrace) columnTrace) counterTrace) laterTrace,after,afterValues,
      join4.1,join4.2.1,join4.2.2.1,?_,afterHeader,afterContents,afterPrefix,nextInputs.trans laterInputs,afterBase,afterPC,
      prefixFrame.trans laterFrame,laterOutput.trans (counterOutput.trans (columnOutput.trans (initOutput.trans guardOutput))),
      RegionMemory.join_trace _ laterTrace before next _ join3.2.1 memory3 laterMemory⟩
    calc
      _ ≤ matrixRowCost P k+(matrixRowCost P k*remaining+135) := join4.2.2.2
      _ = _ := by ring

end PDCompute.Solver
