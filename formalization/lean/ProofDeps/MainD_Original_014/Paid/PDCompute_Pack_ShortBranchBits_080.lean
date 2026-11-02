module
public import Paid.PDCompute_Pack_ShortWriteBits_079
public import Paid.PDCompute_Pack_ShortBranch_032

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame

theorem shortBranch_trace_safe (program : Program) (input : List Cell) (origin : ℕ) (before : State)
    (base pointer budget : ℕ) (values : ℕ → Cell) (tag observation repairs failure : Cell)
    (code : FetchesCode program origin (serializerCode origin)) (pc : before.pc=origin+140)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hpointer : before.register .old=.natural pointer)
    (htag : values 24=tag) (ho : values 27=observation) (hr : values 28=repairs) (hf : values 29=failure)
    (safe : SafeBits before budget) (addressBits : ∀ slot<headerWords,1+natBits (base+slot) ≤ budget)
    (pointerBits : 1+natBits (pointer+4) ≤ budget) (pcBits : ∀ counter ≤ origin+233,natBits counter ≤ budget)
    (outside : ∀ offset<4,pointer+offset<base ∨ base+headerWords≤pointer+offset) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤450 ∧
      Header after base values ∧ PDLower.CalibrationCompute.HeapList after pointer [tag,observation,repairs,failure] ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural (pointer+4) ∧
      after.pc=origin+201 ∧ after.output=before.output ∧
      (∀ state∈trace,RegionMemory before state (cellRegion pointer 4)) ∧ (∀ state∈trace,SafeBits state budget) := by
  have branchFetch:=fetch_shortBranch program origin code
  unfold shortBranchCode at branchFetch
  have writeFetch : FetchesCode program before.pc (writeSlots [24,27,28,29]) := by
    rw [pc]
    exact branchFetch.append_left
  obtain ⟨writtenTrace,written,hh,hl,hchain,ht,writtenHeader,writtenHeap,writtenBase,writtenPointer,writtenPC,writtenOutput,writtenMemory,writtenBits⟩:=
    short_write_trace_safe program input before base pointer budget values tag observation repairs failure header hbase hpointer
      htag ho hr hf outside safe addressBits pointerBits (pcBits _ (by omega)) writeFetch
  have jumpPC : written.pc=origin+164 := by omega
  have jumpFetch : program[written.pc]?=some (.jump (origin+201)) := by
    rw [jumpPC]
    exact short_entry_jump_fetch program origin code
  let after:State:={written with pc:=origin+201}
  have jump : step program input written=some after := by simp [step,jumpFetch,Instruction.execute,after]
  have joined:=chain_append_control program input writtenTrace written after hchain hl jump
  have nonempty : writtenTrace≠[] := by intro empty; simp only [empty,List.head?_nil,reduceCtorEq] at hh
  have lastMemory:=RegionMemory.trace_last writtenMemory hl
  have afterMemory : RegionMemory before after (cellRegion pointer 4) := lastMemory
  have writtenSafe : SafeBits written budget:=writtenBits written (List.mem_of_getLast? hl)
  have afterSafe : SafeBits after budget:=writtenSafe.withPC _ (pcBits _ (by omega))
  refine ⟨writtenTrace++[after],after,?_,by simp,joined.1,?_,writtenHeader,writtenHeap,writtenBase,writtenPointer,
    rfl,writtenOutput,?_,?_⟩
  · simpa only [List.head?_append_of_ne_nil writtenTrace nonempty] using hh
  · omega
  · intro state member
    rcases List.mem_append.mp member with earlier|last
    · exact writtenMemory state earlier
    · have same : state=after := by simpa only [List.mem_singleton] using last
      subst state
      exact afterMemory

  · intro state member
    rcases List.mem_append.mp member with earlier|last
    · exact writtenBits state earlier
    · have same : state=after:=by simpa only [List.mem_singleton] using last
      subst state
      exact afterSafe

end PDCompute.Pack
