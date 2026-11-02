module

public import Paid.PDCompute_SolverCellFields_118

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

attribute [local irreducible] cellFieldsCode

abbrev MatrixInputSlot (slot : ℕ) : Prop := slot < 7 ∨ slot=19 ∨ slot=20

theorem rowPointerValues_inputs (values : ℕ → Cell) (base k row column slot : ℕ) (control : MatrixInputSlot slot) :
    rowPointerValues (Function.update values 47 (.natural base)) base k row column slot=values slot := by
  have h35 : slot ≠ 35 := by unfold MatrixInputSlot at control; omega
  have h36 : slot ≠ 36 := by unfold MatrixInputSlot at control; omega
  have h37 : slot ≠ 37 := by unfold MatrixInputSlot at control; omega
  have h38 : slot ≠ 38 := by unfold MatrixInputSlot at control; omega
  have h46 : slot ≠ 46 := by unfold MatrixInputSlot at control; omega
  have h47 : slot ≠ 47 := by unfold MatrixInputSlot at control; omega
  simp only [rowPointerValues,Function.update_of_ne h35,Function.update_of_ne h36,Function.update_of_ne h37,
    Function.update_of_ne h38,Function.update_of_ne h46,Function.update_of_ne h47]

/-- A COMPLETE actual cell of the original finite table: addresses are
computed by ISA operations, all edge branches are executed, the original
entry is stored in live heap, and the real dense-prefix invariant grows.
The proof contains no assumed cell oracle or assumed row correctness. -/
theorem fullCell_trace_memory (mode : ReaderMode) (program : Program) (input : List Cell)
    (origin : ℕ) (P : Parameters) (fee penalty : ℚ) (row column : ℕ)
    (before : State) (base n k source : ℕ) (values : ℕ → Cell)
    (hpc : before.pc=origin) (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (avoids : EndpointAvoids mode P source base n k)
    (hsourceValue : values 0=.natural source) (hpenalty : values 2=.rational penalty) (hk : values 4=.natural k)
    (hfee : values 5=.rational fee) (last : values 6=.natural P.certificate.M)
    (hrow : values 19=.natural row) (hcolumn : values 20=.natural column) (rowBound : row ≤ n) (columnBound : column ≤ k)
    (prior : DensePrefix before base k (solverEntry P fee penalty k) (row*(k+1)+column))
    (fetch : FetchesCode program origin (fullCellCode mode origin)) :
    ∃ trace : List State, ∃ after : State, ∃ afterValues : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 2500*(P.certificate.M+1)+23400 ∧ Header after base afterValues ∧
      DensePrefix after base k (solverEntry P fee penalty k) (row*(k+1)+column+1) ∧
      (∀ slot,MatrixInputSlot slot → afterValues slot=values slot) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+(fullCellCode mode origin).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace,RegionMemory before state (cellRegion base headerWords ∪ cellRegion (cellBase base k row column) 6) := by
  let pointerValues:=rowPointerValues (Function.update values 47 (.natural base)) base k row column
  have pointerFetch : FetchesCode program before.pc rowPointerSetupCode := by rw [hpc]; exact fetch.append_left.append_left
  obtain ⟨pointerTrace,pointed,pointerHead,pointerLast,pointerChain,pointerTime,pointedHeader,pointedBase,pointedPC,
    pointerFrame,pointerOutput,pointerMemory⟩:=rowPointerSetup_trace_memory program input before base n k row column values
      header hbase hk hrow hcolumn pointerFetch
  have pointedAt : pointed.pc=origin+rowPointerSetupCode.length := by rw [pointedPC,hpc]
  have actualPrior:=prior.header (HeaderMemory.trace_last pointerMemory pointerLast)
  have actualSource:=EndpointSource.frame_of_avoids mode input P source base n k before pointed hsource avoids pointerFrame
  have keep (slot : ℕ) (control : MatrixInputSlot slot) : pointerValues slot=values slot :=
    rowPointerValues_inputs values base k row column slot control
  have fieldsFetch : FetchesCode program (origin+rowPointerSetupCode.length)
      (cellFieldsCode mode (origin+rowPointerSetupCode.length)) := fetch.append_left.append_right
  obtain ⟨fieldsTrace,prepared,preparedValues,fieldsHead,fieldsLast,fieldsChain,fieldsTime,preparedHeader,fields,currentPointer,
    preserved,preparedBase,preparedPC,fieldsFrame,fieldsOutput,fieldsMemory⟩:=
    cellFields_trace_memory mode program input (origin+rowPointerSetupCode.length) P fee penalty row column pointed base n k source
      pointerValues pointedAt pointedHeader pointedBase actualSource avoids
      ((keep 0 (by decide)).trans hsourceValue) ((keep 2 (by decide)).trans hpenalty)
      ((keep 5 (by decide)).trans hfee) ((keep 6 (by decide)).trans last)
      ((keep 19 (by decide)).trans hrow) ((keep 20 (by decide)).trans hcolumn) columnBound rfl rfl rfl actualPrior fieldsFetch
  have outside : ∀ offset < 6,cellBase base k row column+offset < base ∨ base+headerWords ≤ cellBase base k row column+offset := by
    intro offset _
    right
    unfold cellBase tableBase
    omega
  have regionInside : cellRegion (cellBase base k row column) 6 ⊆ workspace base n k := by
    intro address member
    obtain ⟨offset,inside,rfl⟩:=Finset.mem_image.mp member
    exact denseCell_mem_workspace base n k row column offset rowBound columnBound (Finset.mem_range.mp inside)
  have writeFetch : FetchesCode program prepared.pc writeCurrentEntryCode := by
    rw [preparedPC]
    have raw:=fetch.append_right
    simpa only [List.length_append,Nat.add_assoc] using raw
  obtain ⟨writeTrace,after,writeHead,writeLast,writeChain,writeTime,afterHeader,written,afterBase,_,afterPC,
    writeFrame,writeOutput,writeMemory⟩:=writeCurrentEntry_trace_memory program input prepared base (cellBase base k row column) n k
      preparedValues (solverEntry P fee penalty k row column) preparedHeader preparedBase currentPointer fields outside regionInside writeFetch
  have preparedPrior:=actualPrior.header (HeaderMemory.trace_last fieldsMemory fieldsLast)
  have complete:=preparedPrior.extend columnBound (RegionMemory.trace_last writeMemory writeLast) written
  have join1:=joinTrace_spec program input pointerTrace fieldsTrace before pointed prepared 5010 (2500*(P.certificate.M+1)+17685)
    pointerHead pointerLast fieldsHead fieldsLast pointerChain fieldsChain pointerTime fieldsTime
  have memory1:=joinTrace_memory pointerTrace fieldsTrace before pointed base pointerLast pointerMemory fieldsMemory
  have join2:=joinTrace_spec program input (joinTrace pointerTrace fieldsTrace) writeTrace before prepared after
    (5010+(2500*(P.certificate.M+1)+17685)) 705 join1.1 join1.2.1 writeHead writeLast join1.2.2.1 writeChain join1.2.2.2 writeTime
  refine ⟨joinTrace (joinTrace pointerTrace fieldsTrace) writeTrace,after,preparedValues,join2.1,join2.2.1,join2.2.2.1,?_,
    afterHeader,complete,?_,afterBase,?_,pointerFrame.trans (fieldsFrame.trans writeFrame),
    writeOutput.trans (fieldsOutput.trans pointerOutput),?_⟩
  · calc
      _ ≤ (5010+(2500*(P.certificate.M+1)+17685))+705 := join2.2.2.2
      _ = _ := by ring
  · intro slot control
    have persistent : SolverPersistentSlot slot := by unfold SolverPersistentSlot SolverControlSlot; unfold MatrixInputSlot at control; omega
    exact (preserved slot persistent).trans (keep slot control)
  · have writerSize : writeCurrentEntryCode.length=39 := rfl
    rw [afterPC,preparedPC,fullCellCode,List.length_append,List.length_append,writerSize]
    omega
  · apply RegionMemory.join_trace (joinTrace pointerTrace fieldsTrace) writeTrace before prepared _ join1.2.1
    · intro state member
      exact (memory1 state member).region _ Finset.subset_union_left
    · intro state member
      exact (writeMemory state member).enlarge Finset.subset_union_right

end PDCompute.Solver
