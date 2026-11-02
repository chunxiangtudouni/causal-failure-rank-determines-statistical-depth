module
public import Paid.PDCompute_Pack_Emission_012
public import Paid.PDCompute_Pack_Fetch_005
public import Paid.PDCompute_Pack_Fragments_018

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

/-- The non-test branch includes its REAL post-emission jump to201.
The four stored words are original layout, with both unused words skipped. -/
theorem shortBranch_trace (program : Program) (input : List Cell) (origin : ℕ) (before : State)
    (base pointer : ℕ) (values : ℕ → Cell) (tag observation repairs failure : Cell)
    (code : FetchesCode program origin (serializerCode origin)) (pc : before.pc=origin+140)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hpointer : before.register .old=.natural pointer)
    (htag : values 24=tag) (ho : values 27=observation) (hr : values 28=repairs) (hf : values 29=failure)
    (outside : ∀ offset<4,pointer+offset<base ∨ base+headerWords≤pointer+offset) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤450 ∧
      Header after base values ∧ PDLower.CalibrationCompute.HeapList after pointer [tag,observation,repairs,failure] ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural (pointer+4) ∧
      after.pc=origin+201 ∧ after.output=before.output ∧
      ∀ state∈trace,RegionMemory before state (cellRegion pointer 4) := by
  have branchFetch:=fetch_shortBranch program origin code
  unfold shortBranchCode at branchFetch
  have writeFetch : FetchesCode program before.pc (writeSlots [24,27,28,29]) := by
    rw [pc]
    exact branchFetch.append_left
  obtain ⟨writtenTrace,written,hh,hl,hchain,ht,writtenHeader,writtenHeap,writtenBase,writtenPointer,writtenPC,writtenOutput,writtenMemory⟩:=
    short_write_trace program input before base pointer values tag observation repairs failure header hbase hpointer
      htag ho hr hf outside writeFetch
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
  refine ⟨writtenTrace++[after],after,?_,by simp,joined.1,?_,writtenHeader,writtenHeap,writtenBase,writtenPointer,
    rfl,writtenOutput,?_⟩
  · simpa only [List.head?_append_of_ne_nil writtenTrace nonempty] using hh
  · omega
  · intro state member
    rcases List.mem_append.mp member with earlier|last
    · exact writtenMemory state earlier
    · have same : state=after := by simpa only [List.mem_singleton] using last
      subst state
      exact afterMemory

end PDCompute.Pack
