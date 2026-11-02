module
public import Paid.PDCompute_Nat_RowPointerBits_006
public import Paid.PDCompute_Pack_SlotBitTrace_064
public import Paid.PDCompute_SolverRowPointerSetup_087

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000
@[expose] public section
namespace PDCompute.NatControl
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (storeSlot storeSlotResult)

theorem rowPointerSetup_trace_bits (program : Program) (input : List Cell) (before : State)
    (base n k row column budget : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hk : values 4=.natural k) (hr : values 19=.natural row) (hc : values 20=.natural column)
    (rowBound : row≤n) (columnBound : column≤k) (safe : RootD27.Bits.SafeBits before budget)
    (naturalBound : ∀ value≤PDCompute.Pack.naturalCap base n k,(.natural value : Cell).bits≤budget)
    (pcBits : natBits (before.pc+rowPointerSetupCode.length)≤budget)
    (fetch : FetchesCode program before.pc rowPointerSetupCode) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 5010 ∧
      Header after base (rowPointerValues (Function.update values 47 (.natural base)) base k row column) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+rowPointerSetupCode.length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace, HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  let saved:=storeSlotResult before base 47 .fresh
  let savedValues:=Function.update values 47 (.natural base)
  have fields : saved.heap=Function.update before.heap (base+47) (before.register .fresh) ∧
      saved.live=insert (base+47) before.live ∧ saved.register .fresh=before.register .fresh ∧
      saved.pc=before.pc+3 ∧ saved.output=before.output := ⟨rfl,rfl,rfl,rfl,rfl⟩
  have fetchSave : FetchesCode program before.pc (storeSlot 47 .fresh) := fetch.append_left
  obtain ⟨saveTrace,saveHead,saveLast,saveChain,saveTime,saveMemory,saveBits⟩ :=
    PDCompute.Pack.storeSlot_trace_safe program input before base 47 budget .fresh values header (by decide) hbase (by decide)
      safe (naturalBound _ (PDCompute.Pack.naturalCap_header_address base n k 47 (by decide)))
      ((natBits_mono (by simp only [rowPointerSetupCode,List.length_append,storeSlot,List.length_cons,List.length_nil];omega : before.pc+3≤before.pc+rowPointerSetupCode.length)).trans pcBits) fetchSave
  have savedHeap : saved.heap=Function.update before.heap (base+47) (.natural base) := by
    simpa only [hbase] using fields.1
  have savedHeader : Header saved base savedValues := by
    apply Header.update header 47 (.natural base) savedHeap
    rw [fields.2.1]
    exact Finset.subset_insert _ _
  have savedBase : saved.register .fresh=.natural base := fields.2.2.1.trans hbase
  have savedFrame : Frame before saved base n k :=
    slotWrite_frame before saved base 47 n k (.natural base) (by decide) savedHeap fields.2.1
  have fetchPointers : FetchesCode program saved.pc (runtimeCode rowPointerCommands) := by
    rw [fields.2.2.2.1]
    exact fetch.append_right
  have savedSafe : RootD27.Bits.SafeBits saved budget:=saveBits saved (List.mem_of_getLast? saveLast)
  have setupLength : rowPointerSetupCode.length=3+(runtimeCode rowPointerCommands).length:=by
    rw [rowPointerSetupCode,List.length_append]
    rfl
  have pointerPC : natBits (saved.pc+(runtimeCode rowPointerCommands).length)≤budget:=by
    rw [fields.2.2.2.1]
    simpa only [setupLength,Nat.add_assoc] using pcBits
  obtain ⟨pointerTrace,after,pointerHead,pointerLast,pointerChain,pointerTime,afterHeader,afterBase,afterPC,afterFrame,afterOutput,pointerInvariant⟩ :=
    rowPointer_trace_bits program input saved base n k row column budget savedValues savedHeader savedBase rfl hk hr hc
      rowBound columnBound savedSafe naturalBound pointerPC fetchPointers
  have joined:=joinTrace_spec program input saveTrace pointerTrace before saved after 60 4950
    saveHead saveLast pointerHead pointerLast saveChain pointerChain saveTime pointerTime
  refine ⟨joinTrace saveTrace pointerTrace,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,afterHeader,
    afterBase,?_,savedFrame.trans afterFrame,afterOutput.trans fields.2.2.2.2,
    fun state member=>⟨joinTrace_memory saveTrace pointerTrace before saved base saveLast saveMemory
      (fun current present=>(pointerInvariant current present).1) state member,
      PDCompute.Pack.joinTrace_invariant saveTrace pointerTrace (fun current=>RootD27.Bits.SafeBits current budget)
        saveBits (fun current present=>(pointerInvariant current present).2) state member⟩⟩
  have lengthEq : rowPointerSetupCode.length=3+(runtimeCode rowPointerCommands).length := by
    rw [rowPointerSetupCode,List.length_append]
    rfl
  calc
    after.pc = saved.pc+(runtimeCode rowPointerCommands).length := afterPC
    _ = before.pc+3+(runtimeCode rowPointerCommands).length :=
      congrArg (·+(runtimeCode rowPointerCommands).length) fields.2.2.2.1
    _ = before.pc+(3+(runtimeCode rowPointerCommands).length) := Nat.add_assoc _ _ _
    _ = before.pc+rowPointerSetupCode.length := by rw [lengthEq]


/-- The actual first setup saves freshB by real store47; there is NO
prefilled Header47 premise. Every iteration reuses this ONE caller B. -/
theorem rowPointerSetup_trace_controlAllowance (mode : ReaderMode) (origin : ℕ) (input : List Cell) (caller before : State)
    (base n k row column incoming : ℕ) (values : ℕ → Cell)
    (callerSafe : RootD27.Bits.SafeBits caller incoming) (callerFresh : caller.register .fresh=.natural base)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hk : values 4=.natural k) (hr : values 19=.natural row) (hc : values 20=.natural column)
    (rowBound : row≤n) (columnBound : column≤k)
    (safe : RootD27.Bits.SafeBits before (controlAllowance incoming n k origin (solverCalleeCode mode origin).length))
    (fetch : FetchesCode (solverLocatedProgram mode origin) before.pc rowPointerSetupCode) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun a b=>step (solverLocatedProgram mode origin) input a=some b) ∧ time (solverLocatedProgram mode origin) trace≤5010 ∧
      Header after base (rowPointerValues (Function.update values 47 (.natural base)) base k row column) ∧ after.register .fresh=.natural base ∧
      after.pc=before.pc+rowPointerSetupCode.length ∧ Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state (controlAllowance incoming n k origin (solverCalleeCode mode origin).length) := by
  have scope:=fetchedBlock_end_le origin (solverCalleeCode mode origin).toArray before.pc rowPointerSetupCode (by decide) fetch
  have pcBound : before.pc+rowPointerSetupCode.length≤origin+(solverCalleeCode mode origin).length:=by simpa only [List.size_toArray] using scope
  exact rowPointerSetup_trace_bits _ input before base n k row column _ values header fresh hk hr hc rowBound columnBound safe
    (fun value bound=>controlAllowance_natural caller base incoming n k origin _ value callerSafe callerFresh bound)
    (controlAllowance_pc incoming n k origin _ _ pcBound) fetch

end PDCompute.NatControl
