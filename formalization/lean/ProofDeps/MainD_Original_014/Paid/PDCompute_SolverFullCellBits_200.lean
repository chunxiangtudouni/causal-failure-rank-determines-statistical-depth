module

public import Paid.PDCompute_SolverCellFieldsBits_199
public import Paid.PDCompute_SolverEntryWriterBits_182
public import Paid.PDCompute_Nat_RowPointerSetupBits_007
public import Paid.PDCompute_SolverFullCell_119

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000

@[expose] public section

namespace PDCompute.Solver
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame
attribute [local irreducible] fullCellCode cellFieldsCode

/-- COMPLETE original actual cell, all row/tool/penalty branches and
source reads, real pointer generation and dense-prefix growth. One run
carries all original functional/time/space and EVERY-prefix SAME B. -/
theorem fullCell_trace_bits (mode : ReaderMode) (program : Program) (input : List Cell)
    (origin : ℕ) (P : Parameters) (fee penalty : ℚ) (row column : ℕ)
    (before : State) (base n k source budget : ℕ) (values : ℕ → Cell)
    (hpc : before.pc=origin) (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (avoids : EndpointAvoids mode P source base n k)
    (hsourceValue : values 0=.natural source) (hpenalty : values 2=.rational penalty) (hk : values 4=.natural k)
    (hfee : values 5=.rational fee) (last : values 6=.natural P.certificate.M)
    (hrow : values 19=.natural row) (hcolumn : values 20=.natural column) (rowBound : row ≤ n) (columnBound : column ≤ k)
    (prior : DensePrefix before base k (solverEntry P fee penalty k) (row*(k+1)+column))
    (safe : RootD27.Bits.SafeBits before budget) (scalarRoom : 4194304*solverBitScale P fee penalty n k≤budget)
    (natural : ∀ value≤PDCompute.Pack.naturalCap base n k,(.natural value : Cell).bits≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (indexBits : 1+natBits (P.certificate.M+1)≤budget)
    (sourceBits : 1+natBits (source+(1+2*(P.certificate.M+1)))≤budget)
    (counter : natBits (origin+(fullCellCode mode origin).length)≤budget)
    (fetch : FetchesCode program origin (fullCellCode mode origin)) :
    ∃ trace : List State, ∃ after : State, ∃ afterValues : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 2500*(P.certificate.M+1)+23400 ∧ Header after base afterValues ∧
      DensePrefix after base k (solverEntry P fee penalty k) (row*(k+1)+column+1) ∧
      (∀ slot,MatrixInputSlot slot → afterValues slot=values slot) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+(fullCellCode mode origin).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      (∀ state ∈ trace,RegionMemory before state (cellRegion base headerWords ∪ cellRegion (cellBase base k row column) 6)) ∧
      (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  let pointerValues:=rowPointerValues (Function.update values 47 (.natural base)) base k row column
  have literalCode : fullCellCode mode origin=rowPointerSetupCode++cellFieldsCode mode (origin+rowPointerSetupCode.length)++writeCurrentEntryCode := by
    unfold fullCellCode
    rfl
  rw [literalCode] at fetch
  have pointerFetch : FetchesCode program before.pc rowPointerSetupCode := by rw [hpc]; exact fetch.append_left.append_left
  have pointerCounter : natBits (before.pc+rowPointerSetupCode.length)≤budget :=
    (natBits_mono (by rw [hpc];simp only [fullCellCode,List.length_append];omega : before.pc+rowPointerSetupCode.length≤origin+(fullCellCode mode origin).length)).trans counter
  obtain ⟨pointerTrace,pointed,pointerHead,pointerLast,pointerChain,pointerTime,pointedHeader,pointedBase,pointedPC,
    pointerFrame,pointerOutput,pointerResources⟩:=PDCompute.NatControl.rowPointerSetup_trace_bits program input before base n k row column budget values
      header hbase hk hrow hcolumn rowBound columnBound safe natural pointerCounter pointerFetch
  have pointerMemory : ∀ state∈pointerTrace,HeaderMemory before state base := fun state member=>(pointerResources state member).1
  have pointerSafe : ∀ state∈pointerTrace,RootD27.Bits.SafeBits state budget := fun state member=>(pointerResources state member).2
  have pointedAt : pointed.pc=origin+rowPointerSetupCode.length := by rw [pointedPC,hpc]
  have actualPrior:=prior.header (HeaderMemory.trace_last pointerMemory pointerLast)
  have actualSource:=EndpointSource.frame_of_avoids mode input P source base n k before pointed hsource avoids pointerFrame
  have keep (slot : ℕ) (control : MatrixInputSlot slot) : pointerValues slot=values slot :=
    rowPointerValues_inputs values base k row column slot control
  have fieldsFetch : FetchesCode program (origin+rowPointerSetupCode.length)
      (cellFieldsCode mode (origin+rowPointerSetupCode.length)) := fetch.append_left.append_right
  have fieldsCounter : natBits ((origin+rowPointerSetupCode.length)+(cellFieldsCode mode (origin+rowPointerSetupCode.length)).length)≤budget :=
    (natBits_mono (by simp only [fullCellCode,List.length_append];omega :
      (origin+rowPointerSetupCode.length)+(cellFieldsCode mode (origin+rowPointerSetupCode.length)).length≤origin+(fullCellCode mode origin).length)).trans counter
  obtain ⟨fieldsTrace,prepared,preparedValues,fieldsHead,fieldsLast,fieldsChain,fieldsTime,preparedHeader,fields,currentPointer,
    preserved,preparedBase,preparedPC,fieldsFrame,fieldsOutput,fieldsMemory,fieldsSafe⟩:=
    cellFields_trace_bits mode program input (origin+rowPointerSetupCode.length) P fee penalty row column pointed base n k source budget
      pointerValues pointedAt pointedHeader pointedBase actualSource avoids
      ((keep 0 (by decide)).trans hsourceValue) ((keep 2 (by decide)).trans hpenalty)
      ((keep 5 (by decide)).trans hfee) ((keep 6 (by decide)).trans last)
      ((keep 19 (by decide)).trans hrow) ((keep 20 (by decide)).trans hcolumn) rowBound columnBound rfl rfl rfl actualPrior
      (pointerSafe pointed (List.mem_of_getLast? pointerLast)) scalarRoom natural addressBits indexBits sourceBits fieldsCounter fieldsFetch
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
  have endMember:=denseCell_mem_workspace base n k row column 5 rowBound columnBound (by change 5<6;decide)
  obtain ⟨lastOffset,lastInside,lastAddress⟩:=Finset.mem_image.mp endMember
  have lastBound:=Finset.mem_range.mp lastInside
  have pointerCap : cellBase base k row column+6≤PDCompute.Pack.naturalCap base n k := by
    unfold PDCompute.Pack.naturalCap
    omega
  have writeCounter : natBits (prepared.pc+39)≤budget := by
    rw [preparedPC]
    simpa only [fullCellCode,List.length_append,show writeCurrentEntryCode.length=39 from rfl,Nat.add_assoc] using counter
  obtain ⟨writeTrace,after,writeHead,writeLast,writeChain,writeTime,afterHeader,written,afterBase,_,afterPC,
    writeFrame,writeOutput,writeMemory,writeSafe⟩:=writeCurrentEntry_trace_bits program input prepared base (cellBase base k row column) n k budget
      preparedValues (solverEntry P fee penalty k row column) preparedHeader preparedBase currentPointer fields outside regionInside
      (fieldsSafe prepared (List.mem_of_getLast? fieldsLast)) addressBits (natural _ pointerCap) writeCounter writeFetch
  have preparedPrior:=actualPrior.header (HeaderMemory.trace_last fieldsMemory fieldsLast)
  have complete:=preparedPrior.extend columnBound (RegionMemory.trace_last writeMemory writeLast) written
  have join1:=joinTrace_spec program input pointerTrace fieldsTrace before pointed prepared 5010 (2500*(P.certificate.M+1)+17685)
    pointerHead pointerLast fieldsHead fieldsLast pointerChain fieldsChain pointerTime fieldsTime
  have memory1:=joinTrace_memory pointerTrace fieldsTrace before pointed base pointerLast pointerMemory fieldsMemory
  have join2:=joinTrace_spec program input (joinTrace pointerTrace fieldsTrace) writeTrace before prepared after
    (5010+(2500*(P.certificate.M+1)+17685)) 705 join1.1 join1.2.1 writeHead writeLast join1.2.2.1 writeChain join1.2.2.2 writeTime
  refine ⟨joinTrace (joinTrace pointerTrace fieldsTrace) writeTrace,after,preparedValues,join2.1,join2.2.1,join2.2.2.1,?_,
    afterHeader,complete,?_,afterBase,?_,pointerFrame.trans (fieldsFrame.trans writeFrame),
    writeOutput.trans (fieldsOutput.trans pointerOutput),?_,
    PDCompute.Pack.joinTrace_invariant (joinTrace pointerTrace fieldsTrace) writeTrace (fun state=>RootD27.Bits.SafeBits state budget)
      (PDCompute.Pack.joinTrace_invariant pointerTrace fieldsTrace (fun state=>RootD27.Bits.SafeBits state budget) pointerSafe fieldsSafe) writeSafe⟩
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
