module
public import Paid.PDCompute_Nat_LocatedControls_012
public import Paid.PDCompute_Nat_OriginalLiteralControls_011
public import Paid.PDCompute_SolverMatrixPack_142
public import Paid.PDCompute_SolverMatrixFetch_120

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 750000
@[expose] public section
namespace PDCompute.NatControl
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
attribute [local irreducible] fullCellCode cellFieldsCode

/-- Original matrix row test, including the terminating comparison.
Its PC/target costs come solely from the actual matrix+serializer text. -/
theorem matrix_row_guard_trace_context (mode : ReaderMode) (origin matrixOrigin : ℕ) (input : List Cell) (caller before : State)
    (incoming base n k row budget : ℕ) (values : ℕ → Cell)
    (context : SolverControlContext caller incoming base n k mode origin budget)
    (header : Header before base values) (fresh : before.register .fresh=.natural base) (safe : RootD27.Bits.SafeBits before budget)
    (hvalue : values 19=.natural row) (hlimit : values 3=.natural n) (hpc : before.pc=matrixRowTestPC matrixOrigin)
    (fetch : FetchesCode (solverLocatedProgram mode origin) matrixOrigin (matrixPackCode mode matrixOrigin)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun a b=>step (solverLocatedProgram mode origin) input a=some b) ∧
      time (solverLocatedProgram mode origin) trace≤135 ∧ Header after base values ∧ after.register .fresh=.natural base ∧
      after.pc=(if Comparison.lessEqual.nat row n then matrixColumnInitPC matrixOrigin else matrixEndPC mode matrixOrigin) ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  have matrixFetch : FetchesCode (solverLocatedProgram mode origin) matrixOrigin (matrixCode mode matrixOrigin):=fetch.append_left
  have guardFetch : FetchesCode (solverLocatedProgram mode origin) before.pc
      (naturalBranchCode .lessEqual 19 3 (matrixEndPC mode matrixOrigin) (matrixColumnInitPC matrixOrigin)):=by
    rw [hpc]
    exact matrix_row_test_fetch mode _ matrixOrigin matrixFetch
  have packFetch:=fetch.append_right
  rw [matrixCode_end] at packFetch
  obtain ⟨zeroInstruction,zeroFetch⟩:=fetchedBlock_head _ _ _ (by rw [PDCompute.Pack.serializerCode_length];decide) packFetch
  obtain ⟨nonzeroInstruction,nonzeroFetch⟩:=fetchedBlock_head _ _ _ (by decide) (matrix_column_init_fetch mode _ matrixOrigin matrixFetch)
  exact naturalBranch_trace_context mode origin input caller before incoming base n k 19 3 row n (matrixEndPC mode matrixOrigin) (matrixColumnInitPC matrixOrigin) budget .lessEqual values
    context header fresh (by decide) (by decide) hvalue hlimit safe zeroInstruction nonzeroInstruction zeroFetch nonzeroFetch guardFetch

/-- Original matrix column test, including the terminating comparison.
Its PC/target costs come solely from the actual matrix+serializer text. -/
theorem matrix_column_guard_trace_context (mode : ReaderMode) (origin matrixOrigin : ℕ) (input : List Cell) (caller before : State)
    (incoming base n k column budget : ℕ) (values : ℕ → Cell)
    (context : SolverControlContext caller incoming base n k mode origin budget)
    (header : Header before base values) (fresh : before.register .fresh=.natural base) (safe : RootD27.Bits.SafeBits before budget)
    (hvalue : values 20=.natural column) (hlimit : values 4=.natural k) (hpc : before.pc=matrixColumnTestPC matrixOrigin)
    (fetch : FetchesCode (solverLocatedProgram mode origin) matrixOrigin (matrixPackCode mode matrixOrigin)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun a b=>step (solverLocatedProgram mode origin) input a=some b) ∧
      time (solverLocatedProgram mode origin) trace≤135 ∧ Header after base values ∧ after.register .fresh=.natural base ∧
      after.pc=(if Comparison.lessEqual.nat column k then matrixCellPC matrixOrigin else matrixRowAdvancePC mode matrixOrigin) ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  have matrixFetch : FetchesCode (solverLocatedProgram mode origin) matrixOrigin (matrixCode mode matrixOrigin):=fetch.append_left
  have guardFetch : FetchesCode (solverLocatedProgram mode origin) before.pc
      (naturalBranchCode .lessEqual 20 4 (matrixRowAdvancePC mode matrixOrigin) (matrixCellPC matrixOrigin)):=by
    rw [hpc]
    exact matrix_column_test_fetch mode _ matrixOrigin matrixFetch
  obtain ⟨zeroInstruction,zeroFetch⟩:=fetchedBlock_head _ _ _ (by decide) (matrix_row_advance_fetch mode _ matrixOrigin matrixFetch)
  have positiveCell : 0<(fullCellCode mode (matrixCellPC matrixOrigin)).length:=by
    simp only [fullCellCode,List.length_append]
    have firstPositive : 0<rowPointerSetupCode.length:=by
      simp only [rowPointerSetupCode,List.length_append,PDLower.CalibrationCompute.storeSlot,List.length_cons,List.length_nil]
      omega
    omega
  obtain ⟨nonzeroInstruction,nonzeroFetch⟩:=fetchedBlock_head _ _ (fullCellCode mode (matrixCellPC matrixOrigin)) positiveCell (matrix_cell_fetch mode _ matrixOrigin matrixFetch)
  exact naturalBranch_trace_context mode origin input caller before incoming base n k 20 4 column k (matrixRowAdvancePC mode matrixOrigin) (matrixCellPC matrixOrigin) budget .lessEqual values
    context header fresh (by decide) (by decide) hvalue hlimit safe zeroInstruction nonzeroInstruction zeroFetch nonzeroFetch guardFetch

/-- Actual original row increment and fetched literal backjump.
The real loop bound pays +1; no new capacity/overflow premise is asked. -/
theorem matrix_row_backedge_trace_context (mode : ReaderMode) (origin matrixOrigin : ℕ) (input : List Cell) (caller before : State)
    (incoming base n k row budget : ℕ) (values : ℕ → Cell)
    (context : SolverControlContext caller incoming base n k mode origin budget)
    (header : Header before base values) (fresh : before.register .fresh=.natural base) (safe : RootD27.Bits.SafeBits before budget)
    (hvalue : values 19=.natural row) (bounded : row≤n) (hpc : before.pc=matrixRowAdvancePC mode matrixOrigin)
    (fetch : FetchesCode (solverLocatedProgram mode origin) matrixOrigin (matrixPackCode mode matrixOrigin)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun a b=>step (solverLocatedProgram mode origin) input a=some b) ∧
      time (solverLocatedProgram mode origin) trace≤150 ∧ Header after base (Function.update values 19 (.natural (row+1))) ∧
      after.register .fresh=.natural base ∧ after.pc=matrixRowTestPC matrixOrigin ∧ Frame before after base n k ∧ after.output=before.output ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) ∧
      ∀ state∈trace.dropLast,before.pc≤state.pc ∧ state.pc<before.pc+(counterBackCode 19 1 (matrixRowTestPC matrixOrigin)).length := by
  have matrixFetch : FetchesCode (solverLocatedProgram mode origin) matrixOrigin (matrixCode mode matrixOrigin):=fetch.append_left
  have backFetch : FetchesCode (solverLocatedProgram mode origin) before.pc (counterBackCode 19 1 (matrixRowTestPC matrixOrigin)):=by
    rw [hpc]
    apply fetch_append_control _ _ _ _ (matrix_row_advance_fetch mode _ matrixOrigin matrixFetch)
    have back:=matrix_row_back_fetch mode _ matrixOrigin matrixFetch
    simpa only [matrixRowBackPC] using back
  obtain ⟨targetInstruction,targetFetch⟩:=fetchedBlock_head _ _ _ (by change (0:ℕ)<8;decide) (matrix_row_test_fetch mode _ matrixOrigin matrixFetch)
  have nextCap : row+1≤PDCompute.Pack.naturalCap base n k:=
    (Nat.add_le_add_right bounded 1).trans (PDCompute.Pack.naturalCap_rows base n k)
  exact counterBack_one_trace_context mode origin input caller before incoming base n k 19 row (matrixRowTestPC matrixOrigin) budget values context header fresh
    (by decide) hvalue safe nextCap targetInstruction targetFetch backFetch

/-- Actual original column increment and fetched literal backjump.
The real loop bound pays +1; no new capacity/overflow premise is asked. -/
theorem matrix_column_backedge_trace_context (mode : ReaderMode) (origin matrixOrigin : ℕ) (input : List Cell) (caller before : State)
    (incoming base n k column budget : ℕ) (values : ℕ → Cell)
    (context : SolverControlContext caller incoming base n k mode origin budget)
    (header : Header before base values) (fresh : before.register .fresh=.natural base) (safe : RootD27.Bits.SafeBits before budget)
    (hvalue : values 20=.natural column) (bounded : column≤k) (hpc : before.pc=matrixCellPC matrixOrigin+(fullCellCode mode (matrixCellPC matrixOrigin)).length)
    (fetch : FetchesCode (solverLocatedProgram mode origin) matrixOrigin (matrixPackCode mode matrixOrigin)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun a b=>step (solverLocatedProgram mode origin) input a=some b) ∧
      time (solverLocatedProgram mode origin) trace≤150 ∧ Header after base (Function.update values 20 (.natural (column+1))) ∧
      after.register .fresh=.natural base ∧ after.pc=matrixColumnTestPC matrixOrigin ∧ Frame before after base n k ∧ after.output=before.output ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) ∧
      ∀ state∈trace.dropLast,before.pc≤state.pc ∧ state.pc<before.pc+(counterBackCode 20 1 (matrixColumnTestPC matrixOrigin)).length := by
  have matrixFetch : FetchesCode (solverLocatedProgram mode origin) matrixOrigin (matrixCode mode matrixOrigin):=fetch.append_left
  have backFetch : FetchesCode (solverLocatedProgram mode origin) before.pc (counterBackCode 20 1 (matrixColumnTestPC matrixOrigin)):=by
    rw [hpc]
    apply fetch_append_control _ _ _ _ (matrix_column_advance_fetch mode _ matrixOrigin matrixFetch)
    have back:=matrix_column_back_fetch mode _ matrixOrigin matrixFetch
    simpa only [matrixColumnBackPC] using back
  obtain ⟨targetInstruction,targetFetch⟩:=fetchedBlock_head _ _ _ (by change (0:ℕ)<8;decide) (matrix_column_test_fetch mode _ matrixOrigin matrixFetch)
  have nextCap : column+1≤PDCompute.Pack.naturalCap base n k:=
    (Nat.add_le_add_right bounded 1).trans (PDCompute.Pack.naturalCap_columns base n k)
  exact counterBack_one_trace_context mode origin input caller before incoming base n k 20 column (matrixColumnTestPC matrixOrigin) budget values context header fresh
    (by decide) hvalue safe nextCap targetInstruction targetFetch backFetch

/-- Actual original row zero initialization; prior dirty counter
contents are not read or constrained by a parameter-only bound. -/
theorem matrix_row_initialize_trace_context (mode : ReaderMode) (origin matrixOrigin : ℕ) (input : List Cell) (caller before : State)
    (incoming base n k budget : ℕ) (values : ℕ → Cell)
    (context : SolverControlContext caller incoming base n k mode origin budget)
    (header : Header before base values) (fresh : before.register .fresh=.natural base) (safe : RootD27.Bits.SafeBits before budget)
    (hpc : before.pc=matrixOrigin)
    (fetch : FetchesCode (solverLocatedProgram mode origin) matrixOrigin (matrixPackCode mode matrixOrigin)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun a b=>step (solverLocatedProgram mode origin) input a=some b) ∧
      time (solverLocatedProgram mode origin) trace≤330 ∧ Header after base (Function.update values 19 (.natural 0)) ∧
      after.register .fresh=.natural base ∧ after.pc=matrixRowTestPC matrixOrigin ∧ Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  have matrixFetch : FetchesCode (solverLocatedProgram mode origin) matrixOrigin (matrixCode mode matrixOrigin):=fetch.append_left
  have initFetch : FetchesCode (solverLocatedProgram mode origin) before.pc (headerCode [.constant 19 (.natural 0)]):=by
    rw [hpc]
    exact matrix_row_init_fetch mode _ matrixOrigin matrixFetch
  obtain ⟨trace,after,head,last,chain,cost,afterHeader,afterFresh,afterPC,frame,output,invariant⟩:=constantControl_trace_bits mode origin input caller before
    incoming base n k budget 19 0 values context header fresh safe (by decide) (Nat.zero_le _) initFetch
  refine ⟨trace,after,head,last,chain,cost,afterHeader,afterFresh,?_,frame,output,invariant⟩
  rw [afterPC,hpc]
  rfl

/-- Actual original column zero initialization; prior dirty counter
contents are not read or constrained by a parameter-only bound. -/
theorem matrix_column_initialize_trace_context (mode : ReaderMode) (origin matrixOrigin : ℕ) (input : List Cell) (caller before : State)
    (incoming base n k budget : ℕ) (values : ℕ → Cell)
    (context : SolverControlContext caller incoming base n k mode origin budget)
    (header : Header before base values) (fresh : before.register .fresh=.natural base) (safe : RootD27.Bits.SafeBits before budget)
    (hpc : before.pc=matrixColumnInitPC matrixOrigin)
    (fetch : FetchesCode (solverLocatedProgram mode origin) matrixOrigin (matrixPackCode mode matrixOrigin)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun a b=>step (solverLocatedProgram mode origin) input a=some b) ∧
      time (solverLocatedProgram mode origin) trace≤330 ∧ Header after base (Function.update values 20 (.natural 0)) ∧
      after.register .fresh=.natural base ∧ after.pc=matrixColumnTestPC matrixOrigin ∧ Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  have matrixFetch : FetchesCode (solverLocatedProgram mode origin) matrixOrigin (matrixCode mode matrixOrigin):=fetch.append_left
  have initFetch : FetchesCode (solverLocatedProgram mode origin) before.pc (headerCode [.constant 20 (.natural 0)]):=by
    rw [hpc]
    exact matrix_column_init_fetch mode _ matrixOrigin matrixFetch
  obtain ⟨trace,after,head,last,chain,cost,afterHeader,afterFresh,afterPC,frame,output,invariant⟩:=constantControl_trace_bits mode origin input caller before
    incoming base n k budget 20 0 values context header fresh safe (by decide) (Nat.zero_le _) initFetch
  refine ⟨trace,after,head,last,chain,cost,afterHeader,afterFresh,?_,frame,output,invariant⟩
  rw [afterPC,hpc]
  rfl

end PDCompute.NatControl
