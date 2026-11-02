module
public import Paid.PDCompute_Nat_RuntimeSequenceBits_003
public import Paid.PDCompute_Nat_ControlBudget_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
@[expose] public section
namespace PDCompute.NatControl
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
open PDROC.CalibrationRow.Operand

theorem rowPointer_evaluated_bits (values : ℕ → Cell) (base n k row column budget : ℕ)
    (hb : values 47=.natural base) (hk : values 4=.natural k) (hr : values 19=.natural row) (hc : values 20=.natural column)
    (rowBound : row≤n) (columnBound : column≤k) (initial : HeaderValueBits values budget)
    (naturalBound : ∀ value≤PDCompute.Pack.naturalCap base n k,(.natural value : Cell).bits≤budget) :
    RuntimeEvaluatedBits budget rowPointerCommands values := by
  have bounds:=rowPointerBounds base n k row column rowBound columnBound
  have small (value : ℕ) (bound : value≤48) : (.natural value : Cell).bits≤budget:=naturalBound _ (bound.trans (PDCompute.Pack.naturalCap_small base n k))
  let a:=Function.update values 46 (.natural 1)
  have bits_a : HeaderValueBits a budget:=initial.update (small 1 (by decide))
  let b:=Function.update a 35 (.natural (row-1))
  have bits_b : HeaderValueBits b budget:=bits_a.update (naturalBound _ bounds.predecessor)
  let c:=Function.update b 38 (.natural (k+1))
  have bits_c : HeaderValueBits c budget:=bits_b.update (naturalBound _ bounds.columns)
  let d:=Function.update c 35 (.natural ((row-1)*(k+1)))
  have bits_d : HeaderValueBits d budget:=bits_c.update (naturalBound _ bounds.product)
  let e:=Function.update d 35 (.natural ((row-1)*(k+1)+column))
  have bits_e : HeaderValueBits e budget:=bits_d.update (naturalBound _ bounds.index)
  let f:=Function.update e 46 (.natural 6)
  have bits_f : HeaderValueBits f budget:=bits_e.update (small 6 (by decide))
  let g:=Function.update f 35 (.natural (6*((row-1)*(k+1)+column)))
  have bits_g : HeaderValueBits g budget:=bits_f.update (naturalBound _ bounds.scaled)
  let h:=Function.update g 46 (.natural 48)
  have bits_h : HeaderValueBits h budget:=bits_g.update (small 48 (by decide))
  let i:=Function.update h 35 (.natural (48+6*((row-1)*(k+1)+column)))
  have bits_i : HeaderValueBits i budget:=bits_h.update (naturalBound _ bounds.offset)
  let j:=Function.update i 35 (.natural (cellBase base k (row-1) column))
  have bits_j : HeaderValueBits j budget:=bits_i.update (naturalBound _ bounds.good)
  let l:=Function.update j 46 (.natural 6)
  have bits_l : HeaderValueBits l budget:=bits_j.update (small 6 (by decide))
  let m:=Function.update l 36 (.natural (cellBase base k (row-1) column-6))
  have bits_m : HeaderValueBits m budget:=bits_l.update (naturalBound _ bounds.bad)
  let o:=Function.update m 38 (.natural (6*(k+1)))
  have bits_o : HeaderValueBits o budget:=bits_m.update (naturalBound _ bounds.stride)
  let p:=Function.update o 37 (.natural (cellBase base k (row-1) column+6*(k+1)))
  have bits_p : HeaderValueBits p budget:=bits_o.update (naturalBound _ bounds.destination)
  unfold rowPointerCommands
  refine ⟨a,rfl,bits_a,?_⟩
  refine ⟨b,?_,bits_b,?_⟩
  · simp [RuntimeCommand.eval,b,a,Cell.nat?,NatOp.eval,hr]
  refine ⟨c,?_,bits_c,?_⟩
  · simp [RuntimeCommand.eval,c,b,a,Cell.nat?,NatOp.eval,hk]
  refine ⟨d,?_,bits_d,?_⟩
  · simp [RuntimeCommand.eval,d,c,b,Cell.nat?,NatOp.eval]
  refine ⟨e,?_,bits_e,?_⟩
  · simp [RuntimeCommand.eval,e,d,c,b,a,Cell.nat?,NatOp.eval,hc]
  refine ⟨f,rfl,bits_f,?_⟩
  refine ⟨g,?_,bits_g,?_⟩
  · simp [RuntimeCommand.eval,g,f,e,Cell.nat?,NatOp.eval]
  refine ⟨h,rfl,bits_h,?_⟩
  refine ⟨i,?_,bits_i,?_⟩
  · simp [RuntimeCommand.eval,i,h,g,Cell.nat?,NatOp.eval]
  refine ⟨j,?_,bits_j,?_⟩
  · simp [RuntimeCommand.eval,j,i,h,g,f,e,d,c,b,a,Cell.nat?,NatOp.eval,hb,cellBase,tableBase,entryWords,headerWords,Nat.add_assoc]
  refine ⟨l,rfl,bits_l,?_⟩
  refine ⟨m,?_,bits_m,?_⟩
  · simp [RuntimeCommand.eval,m,l,j,Cell.nat?,NatOp.eval]
  refine ⟨o,?_,bits_o,?_⟩
  · simp [RuntimeCommand.eval,o,m,l,j,i,h,g,f,e,d,c,Cell.nat?,NatOp.eval]
  refine ⟨p,?_,bits_p,?_⟩
  · simp [RuntimeCommand.eval,p,o,m,l,j,Cell.nat?,NatOp.eval]
  trivial

/-- Original086 computes every real intermediate at the SAME budget.
The arbitrary incoming scratch/header fields are copied through unchanged. -/
theorem rowPointer_trace_bits (program : Program) (input : List Cell) (before : State)
    (base n k row column budget : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hb : values 47=.natural base) (hk : values 4=.natural k) (hr : values 19=.natural row) (hc : values 20=.natural column)
    (rowBound : row≤n) (columnBound : column≤k) (safe : RootD27.Bits.SafeBits before budget)
    (naturalBound : ∀ value≤PDCompute.Pack.naturalCap base n k,(.natural value : Cell).bits≤budget)
    (pcBits : natBits (before.pc+(runtimeCode rowPointerCommands).length)≤budget)
    (fetch : FetchesCode program before.pc (runtimeCode rowPointerCommands)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun a b=>step program input a=some b) ∧
      time program trace≤4950 ∧ Header after base (rowPointerValues values base k row column) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+(runtimeCode rowPointerCommands).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  have bounded:=rowPointer_evaluated_bits values base n k row column budget hb hk hr hc rowBound columnBound (HeaderValueBits.of_safe header safe) naturalBound
  obtain ⟨trace,after,head,last,chain,cost,afterHeader,afterFresh,afterPC,frame,output,invariant⟩:=runtimeCode_trace_bits rowPointerCommands program input before
    base n k budget values _ rowPointerCommands_valid header fresh (rowPointerCommands_eval values base k row column hb hk hr hc) safe bounded
    (naturalBound _ (baseHeader_le_cap base n k)) pcBits fetch
  exact ⟨trace,after,head,last,chain,cost.trans (by decide),afterHeader,afterFresh,afterPC,frame,output,invariant⟩

/-- Fixed original caller allowance. The linear PC bound comes from the
actual complete located program fetch; no added trace-scope hypothesis. -/
theorem rowPointer_trace_controlAllowance (mode : ReaderMode) (origin : ℕ) (input : List Cell) (caller before : State)
    (base n k row column incoming : ℕ) (values : ℕ → Cell)
    (callerSafe : RootD27.Bits.SafeBits caller incoming) (callerFresh : caller.register .fresh=.natural base)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hb : values 47=.natural base) (hk : values 4=.natural k) (hr : values 19=.natural row) (hc : values 20=.natural column)
    (rowBound : row≤n) (columnBound : column≤k)
    (safe : RootD27.Bits.SafeBits before (controlAllowance incoming n k origin (solverCalleeCode mode origin).length))
    (fetch : FetchesCode (solverLocatedProgram mode origin) before.pc (runtimeCode rowPointerCommands)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun a b=>step (solverLocatedProgram mode origin) input a=some b) ∧ time (solverLocatedProgram mode origin) trace≤4950 ∧
      Header after base (rowPointerValues values base k row column) ∧ after.register .fresh=.natural base ∧
      after.pc=before.pc+(runtimeCode rowPointerCommands).length ∧ Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state (controlAllowance incoming n k origin (solverCalleeCode mode origin).length) := by
  have scope:=fetchedBlock_end_le origin (solverCalleeCode mode origin).toArray before.pc (runtimeCode rowPointerCommands) (by decide) fetch
  have pcBound : before.pc+(runtimeCode rowPointerCommands).length≤origin+(solverCalleeCode mode origin).length:=by simpa only [List.size_toArray] using scope
  exact rowPointer_trace_bits _ input before base n k row column _ values header fresh hb hk hr hc rowBound columnBound safe
    (fun value bound=>controlAllowance_natural caller base incoming n k origin _ value callerSafe callerFresh bound)
    (controlAllowance_pc incoming n k origin _ _ pcBound) fetch

end PDCompute.NatControl
