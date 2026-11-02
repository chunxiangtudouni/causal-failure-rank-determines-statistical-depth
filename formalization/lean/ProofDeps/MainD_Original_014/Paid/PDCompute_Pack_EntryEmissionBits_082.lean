module
public import Paid.PDCompute_Pack_ReadEntryBits_078
public import Paid.PDCompute_Pack_EmitEntryBits_081
public import Paid.PDCompute_Pack_EntryLocal_045

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame

theorem entryEmissionLocal_trace_safe (program : Program) (input : List Cell) (origin : ℕ) (before : State)
    (base source pointer n k budget : ℕ) (entry : MenuEntry) (values : ℕ → Cell)
    (code : FetchesCode program origin (serializerCode origin)) (pc : before.pc=origin+89)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hsource : values sourceCursor=.natural source) (hpointer : values outputCursor=.natural pointer)
    (dense : PDLower.CalibrationCompute.HeapList before source (denseEncodeEntry entry))
    (sourceOutside : ∀ offset<6,source+offset<base ∨ base+headerWords≤source+offset)
    (safe : SafeBits before budget) (addressBits : ∀ slot<headerWords,1+natBits (base+slot) ≤ budget)
    (sourceBits : 1+natBits (source+6) ≤ budget) (twoBits : 1+natBits 2 ≤ budget)
    (pointerBits : 1+natBits (pointer+(encodeEntry entry).length) ≤ budget)
    (pcBits : ∀ counter ≤ origin+233,natBits counter ≤ budget)
    (targetOutside : ∀ offset<6,pointer+offset<base ∨ base+headerWords≤pointer+offset)
    :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤1545 ∧
      Header after base (entryValues entry values source) ∧
      PDLower.CalibrationCompute.HeapList after pointer (encodeEntry entry) ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural (pointer+(encodeEntry entry).length) ∧
      after.pc=origin+201 ∧ after.output=before.output ∧
      (∀ state∈trace,RegionMemory before state (localRegion base pointer (encodeEntry entry).length)) ∧ (∀ state∈trace,SafeBits state budget) := by
  have readFetch : FetchesCode program before.pc readEntryCode := by rw [pc];exact fetch_readEntry program origin code
  obtain ⟨readTrace,read,readHead,readLast,readChain,readTime,readHeader,readBase,readPointer,readTag,readPC,readOutput,readMemory,readBits⟩:=
    readEntry_trace_safe program input before base source pointer n k budget entry values header hbase hsource hpointer dense sourceOutside
      safe addressBits sourceBits twoBits (pcBits _ (by omega)) readFetch
  have branchPC : read.pc=origin+139 := by omega
  let branched:=tagBranchResult read origin entry
  have branchStep : step program input read=some branched := tag_branch_step program input origin read entry code branchPC readTag
  have appended:=chain_append_control program input readTrace read branched readChain readLast branchStep
  have nonempty : readTrace≠[] := by intro empty;simp only [empty,List.head?_nil,reduceCtorEq] at readHead
  have branchHead : (readTrace++[branched]).head?=some before := by
    simpa only [List.head?_append_of_ne_nil readTrace nonempty] using readHead
  have branchLast : (readTrace++[branched]).getLast?=some branched := by simp
  have branchTime : time program (readTrace++[branched])≤900 := by omega
  have lastMemory:=HeaderMemory.trace_last readMemory readLast
  have branchMemory : ∀ state∈readTrace++[branched],HeaderMemory before state base := by
    intro state member
    rcases List.mem_append.mp member with earlier|last
    · exact readMemory state earlier
    · have same : state=branched := by simpa only [List.mem_singleton] using last
      subst state
      exact lastMemory
  have readSafe : SafeBits read budget:=readBits read (List.mem_of_getLast? readLast)
  have branchCounter : emissionPC origin entry ≤ origin+233:=by
    obtain ⟨action,observation,repairs,failure⟩:=entry
    cases action <;> simp only [emissionPC] <;> omega
  have branchSafe : SafeBits branched budget:=readSafe.withPC _ (pcBits _ branchCounter)
  have branchBits : ∀ state∈readTrace++[branched],SafeBits state budget:=by
    intro state member
    rcases List.mem_append.mp member with earlier|last
    · exact readBits state earlier
    · have same : state=branched:=by simpa only [List.mem_singleton] using last
      subst state
      exact branchSafe
  obtain ⟨emission,after,emitHead,emitLast,emitChain,emitTime,afterHeader,heap,afterBase,afterPointer,afterPC,afterOutput,emitMemory,emitBits⟩:=
    emitEntry_trace_safe program input origin branched base pointer source budget entry values code rfl readHeader readBase readPointer
      branchSafe addressBits pointerBits pcBits targetOutside
  have readRegion : ∀ state∈readTrace++[branched],RegionMemory before state (localRegion base pointer (encodeEntry entry).length) := by
    intro state member
    exact headerMemory_local base pointer (encodeEntry entry).length (branchMemory state member)
  have emitRegion : ∀ state∈emission,RegionMemory branched state (localRegion base pointer (encodeEntry entry).length) := by
    intro state member
    exact emissionMemory_local base pointer (encodeEntry entry).length (emitMemory state member)
  have joined:=joinTrace_spec program input (readTrace++[branched]) emission before branched after 900 645
    branchHead branchLast emitHead emitLast appended.1 emitChain branchTime emitTime
  exact ⟨joinTrace (readTrace++[branched]) emission,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    afterHeader,heap,afterBase,afterPointer,afterPC,afterOutput.trans readOutput,
    RegionMemory.join_trace (readTrace++[branched]) emission before branched _ branchLast readRegion emitRegion,
    joinTrace_invariant (readTrace++[branched]) emission (fun state=>SafeBits state budget) branchBits emitBits⟩


end PDCompute.Pack
