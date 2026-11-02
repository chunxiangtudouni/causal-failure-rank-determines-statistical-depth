module
public import Paid.PDCompute_Nat_MatrixControls_013
public import Paid.PDCompute_Nat_RowPointerSetupBits_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 750000
@[expose] public section
namespace PDCompute.NatControl
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame

theorem ControlContext.returnPC {caller : State} {incoming base n k origin span budget : ℕ}
    (context : ControlContext caller incoming base n k origin span budget) (returnPC : ℕ)
    (saved : caller.register .old=.natural returnPC) : natBits returnPC≤budget := by
  have bits:=context.initial_safe.register .old
  rw [saved] at bits
  change 1+natBits returnPC≤budget at bits
  omega

/-- Complete actual natural pointer setup under the ONE GLOBAL caller B.
The real store47 removes any prefilled-base-slot premise; all119 real
operations retain arbitrary dirty caller words through the same budget. -/
theorem rowPointerSetup_trace_context (mode : ReaderMode) (origin : ℕ) (input : List Cell) (caller before : State)
    (incoming base n k row column budget : ℕ) (values : ℕ → Cell)
    (context : SolverControlContext caller incoming base n k mode origin budget)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hk : values 4=.natural k) (hr : values 19=.natural row) (hc : values 20=.natural column)
    (rowBound : row≤n) (columnBound : column≤k) (safe : RootD27.Bits.SafeBits before budget)
    (fetch : FetchesCode (solverLocatedProgram mode origin) before.pc rowPointerSetupCode) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun a b=>step (solverLocatedProgram mode origin) input a=some b) ∧
      time (solverLocatedProgram mode origin) trace≤5010 ∧ Header after base (rowPointerValues (Function.update values 47 (.natural base)) base k row column) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+rowPointerSetupCode.length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget :=
  rowPointerSetup_trace_bits _ input before base n k row column budget values header fresh hk hr hc rowBound columnBound safe
    (fun value bounded=>context.natural value bounded) (SolverControlContext.block (before:=before) context _ (by decide) fetch) fetch

/-- Actual natural phase-entry instantiation: all arbitrary old state cells pay
only their actual initialBits, plus the original162 numeric scale once.
No natural/PC/overflow/whole-run certificate is added to the entry facts. -/
theorem rowPointerSetup_trace_original (mode : ReaderMode) (origin : ℕ) (input : List Cell) (before : State)
    (P : Parameters) (fee penalty : ℚ) (base n k row column : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hk : values 4=.natural k) (hr : values 19=.natural row) (hc : values 20=.natural column)
    (rowBound : row≤n) (columnBound : column≤k)
    (fetch : FetchesCode (solverLocatedProgram mode origin) before.pc rowPointerSetupCode) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun a b=>step (solverLocatedProgram mode origin) input a=some b) ∧
      time (solverLocatedProgram mode origin) trace≤5010 ∧ Header after base (rowPointerValues (Function.update values 47 (.natural base)) base k row column) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+rowPointerSetupCode.length ∧ Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state
        (originalControlBudget (PDCompute.Pack.initialBits before) P fee penalty n k origin (solverCalleeCode mode origin).length) := by
  have context:=controlContext_originalScale before (PDCompute.Pack.initialBits before) base n k origin (solverCalleeCode mode origin).length P fee penalty
    (PDCompute.Pack.initialBits_safe before) fresh
  exact rowPointerSetup_trace_context mode origin input before before _ base n k row column _ values context header fresh hk hr hc
    rowBound columnBound context.initial_safe fetch

/-- Original cellFields really writes zero to46 before the row/tool
conditional. The large incoming scratch value is carried then overwritten,
not restricted to a new parameter-only cap or cleared without execution. -/
theorem cellFields_zero_trace_context (mode : ReaderMode) (origin fieldOrigin : ℕ) (input : List Cell) (caller before : State)
    (incoming base n k budget : ℕ) (values : ℕ → Cell)
    (context : SolverControlContext caller incoming base n k mode origin budget)
    (header : Header before base values) (fresh : before.register .fresh=.natural base) (safe : RootD27.Bits.SafeBits before budget)
    (hpc : before.pc=fieldOrigin)
    (fetch : FetchesCode (solverLocatedProgram mode origin) fieldOrigin (cellFieldsCode mode fieldOrigin)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun a b=>step (solverLocatedProgram mode origin) input a=some b) ∧
      time (solverLocatedProgram mode origin) trace≤330 ∧ Header after base (Function.update values 46 (.natural 0)) ∧
      after.register .fresh=.natural base ∧ after.pc=fieldOrigin+4 ∧ Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  have zeroFetch : FetchesCode (solverLocatedProgram mode origin) before.pc (headerCode [.constant 46 (.natural 0)]):=by
    rw [hpc]
    exact fetch.append_left
  obtain ⟨trace,after,head,last,chain,cost,afterHeader,afterFresh,afterPC,frame,output,invariant⟩:=constantControl_trace_bits mode origin input caller before
    incoming base n k budget 46 0 values context header fresh safe (by decide) (Nat.zero_le _) zeroFetch
  refine ⟨trace,after,head,last,chain,cost,afterHeader,afterFresh,?_,frame,output,invariant⟩
  rw [afterPC,hpc]
  rfl

end PDCompute.NatControl
