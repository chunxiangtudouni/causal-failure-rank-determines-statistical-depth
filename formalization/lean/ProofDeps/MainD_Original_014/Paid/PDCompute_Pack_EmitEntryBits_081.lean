module
public import Paid.PDCompute_Pack_ShortBranchBits_080
public import Paid.PDCompute_Pack_EmitEntry_035

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame

theorem emitEntry_trace_safe (program : Program) (input : List Cell) (origin : ℕ) (before : State)
    (base pointer source budget : ℕ) (entry : MenuEntry) (values : ℕ → Cell)
    (code : FetchesCode program origin (serializerCode origin)) (pc : before.pc=emissionPC origin entry)
    (header : Header before base (entryValues entry values source))
    (hbase : before.register .fresh=.natural base) (hpointer : before.register .old=.natural pointer)
    (safe : SafeBits before budget) (addressBits : ∀ slot<headerWords,1+natBits (base+slot) ≤ budget)
    (pointerBits : 1+natBits (pointer+(encodeEntry entry).length) ≤ budget)
    (pcBits : ∀ counter ≤ origin+233,natBits counter ≤ budget)
    (outside : ∀ offset<6,pointer+offset<base ∨ base+headerWords≤pointer+offset) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤645 ∧
      Header after base (entryValues entry values source) ∧
      PDLower.CalibrationCompute.HeapList after pointer (encodeEntry entry) ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural (pointer+(encodeEntry entry).length) ∧
      after.pc=origin+201 ∧ after.output=before.output ∧
      (∀ state∈trace,RegionMemory before state (cellRegion pointer (encodeEntry entry).length)) ∧ (∀ state∈trace,SafeBits state budget) := by
  have tag:=entryValues_tag entry values source
  have observationValue:=entryValues_observation entry values source
  have repairsValue:=entryValues_repairs entry values source
  have failureValue:=entryValues_failure entry values source
  obtain ⟨action,observation,repairs,failure⟩:=entry
  cases action with
  | finish =>
    obtain ⟨trace,after,hh,hl,hchain,ht,afterHeader,heap,afterBase,afterPointer,afterPC,afterOutput,memory,bits⟩:=
      shortBranch_trace_safe program input origin before base pointer budget _ (.natural 0) (.rational observation) (.rational repairs) (.rational failure)
        code (by simpa only [emissionPC] using pc) header hbase hpointer
        (by simpa only [entryTag] using tag) observationValue repairsValue failureValue safe addressBits (by simpa [encodeEntry,encodeAction] using pointerBits) pcBits
        (fun offset bound=>outside offset (by omega))
    exact ⟨trace,after,hh,hl,hchain,ht.trans (by decide),afterHeader,heap,afterBase,afterPointer,afterPC,afterOutput,memory,bits⟩
  | abandon =>
    obtain ⟨trace,after,hh,hl,hchain,ht,afterHeader,heap,afterBase,afterPointer,afterPC,afterOutput,memory,bits⟩:=
      shortBranch_trace_safe program input origin before base pointer budget _ (.natural 1) (.rational observation) (.rational repairs) (.rational failure)
        code (by simpa only [emissionPC] using pc) header hbase hpointer
        (by simpa only [entryTag] using tag) observationValue repairsValue failureValue safe addressBits (by simpa [encodeEntry,encodeAction] using pointerBits) pcBits
        (fun offset bound=>outside offset (by omega))
    exact ⟨trace,after,hh,hl,hchain,ht.trans (by decide),afterHeader,heap,afterBase,afterPointer,afterPC,afterOutput,memory,bits⟩
  | test level bad =>
    let entry : MenuEntry:=⟨.test level bad,observation,repairs,failure⟩
    have beforePC : before.pc=origin+165 := by simpa only [emissionPC] using pc
    have fetched : FetchesCode program before.pc (denseWriteBlockCode entryStart (denseEncodeEntry entry).length) := by
      rw [beforePC,denseEncodeEntry_length]
      simpa only [testBranchCode,test_write_code,entryStart,entryWords] using fetch_testBranch program origin code
    have contents : ∀ (offset : ℕ) (inside : offset<(denseEncodeEntry entry).length),
        entryValues entry values source (entryStart+offset)=(denseEncodeEntry entry)[offset] := by
      intro offset inside
      have bound : offset<6 := by simpa only [denseEncodeEntry_length,entryWords] using inside
      exact entryValues_loaded_slot entry values source offset bound
    have targetOutside : ∀ offset<(denseEncodeEntry entry).length,pointer+offset<base ∨ base+headerWords≤pointer+offset := by
      simpa only [denseEncodeEntry_length,entryWords] using outside
    obtain ⟨trace,after,hh,hl,hchain,ht,afterHeader,heap,afterBase,afterPointer,afterPC,afterOutput,memory,bits⟩:=
      denseWriteBlock_trace_safe program input (denseEncodeEntry entry) before base entryStart pointer budget _ header
        (by rw [denseEncodeEntry_length];change 30≤48;decide) hbase hpointer contents targetOutside safe addressBits
        (by simpa [entry,denseEncodeEntry,encodeEntry,encodeAction] using pointerBits)
        (pcBits _ (by rw [beforePC,denseEncodeEntry_length];unfold entryWords;omega)) fetched
    have timeBound : time program trace≤645 := by simpa only [denseEncodeEntry_length,entryWords] using ht
    have pcBound : after.pc=before.pc+36 := by simpa only [denseEncodeEntry_length,entryWords] using afterPC
    refine ⟨trace,after,hh,hl,hchain,timeBound,afterHeader,?_,afterBase,?_,?_,afterOutput,?_,bits⟩
    · simpa only [entry,denseEncodeEntry,encodeEntry,encodeAction] using heap
    · simpa [entry,denseEncodeEntry,encodeEntry,encodeAction] using afterPointer
    · omega
    · simpa [entry,denseEncodeEntry,encodeEntry,encodeAction] using memory


end PDCompute.Pack
