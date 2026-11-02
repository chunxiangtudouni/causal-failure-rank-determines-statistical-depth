module

public import Paid.PDCompute_SolverEntryLoadBits_159
public import Paid.PDCompute_SolverBadChoiceBits_167
public import Paid.PDCompute_SolverLoadedBad_107

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame

theorem loadedBad_trace_bits (program : Program) (input : List Cell) (origin : ℕ)
    (P : Parameters) (fee penalty : ℚ) (previous : MenuRow) (tools pointer : ℕ) (before : State) (base n k budget S L T : ℕ) (values : ℕ → Cell)
    (hpc : before.pc=origin) (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hpointer : values 36=.natural pointer) (hfee : values 5=.rational fee) (hpenalty : values 2=.rational penalty)
    (source : PDLower.CalibrationCompute.HeapList before pointer (denseEncodeEntry (previous.getD tools abandonEntry)))
    (outside : ∀ offset<6,pointer+offset<base ∨ base+headerWords≤pointer+offset)
    (safe : RootD27.Bits.SafeBits before budget)
    (observation : ratEncodingBits (previous.getD tools abandonEntry).observation≤S)
    (repairs : ratEncodingBits (previous.getD tools abandonEntry).repairs≤S) (failure : ratEncodingBits (previous.getD tools abandonEntry).failure≤S)
    (feeBits : ratEncodingBits fee≤L) (penaltyBits : ratEncodingBits penalty≤T) (room : 1+16*(2*(S+3)+L+T+1)≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (pointerBits : 1+natBits (pointer+6)≤budget)
    (counter : natBits (origin+(loadedBadCode origin).length)≤budget) (fetch : FetchesCode program origin (loadedBadCode origin)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤4305 ∧
      Header after base (loadedBadValues values fee penalty (previous.getD tools abandonEntry)) ∧
      after.heap (base+31)=.rational (P.menuBadBranch fee penalty previous (tools+1)).2.observation ∧
      after.heap (base+32)=.rational (P.menuBadBranch fee penalty previous (tools+1)).2.repairs ∧
      after.heap (base+33)=.rational (P.menuBadBranch fee penalty previous (tools+1)).2.failure ∧
      after.heap (base+34)=.natural (if (P.menuBadBranch fee penalty previous (tools+1)).1=.repair then 1 else 0) ∧
      after.heap (base+22)=.rational ((P.menuBadBranch fee penalty previous (tools+1)).2.objective fee penalty) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+(loadedBadCode origin).length ∧ Frame before after base n k ∧ after.output=before.output ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  let entry:=previous.getD tools abandonEntry
  let loadedValues:=denseReadHeaderValues (denseEncodeEntry entry) 13 values
  have loadFetch : FetchesCode program before.pc (loadDenseEntryCode 36 13) := by rw [hpc]; exact fetch.append_left
  have loadCounter : natBits (before.pc+39)≤budget :=
    (natBits_mono (by rw [hpc,loadedBadCode,List.length_append,loadDenseEntryCode_length]; omega : before.pc+39≤origin+(loadedBadCode origin).length)).trans counter
  obtain ⟨loadTrace,loaded,loadHead,loadLast,loadChain,loadTime,loadedHeader,loadedBase,_,loadedPC,loadFrame,loadOutput,loadMemory,loadSafe⟩:=
    loadDenseEntry_trace_bits program input before base 36 13 pointer n k budget values entry header fresh (by decide) (by decide) hpointer source outside safe
      addressBits pointerBits loadCounter loadFetch
  have actualPC : loaded.pc=origin+(loadDenseEntryCode 36 13).length := by rw [loadedPC,hpc,loadDenseEntryCode_length]
  have loadedFee : loadedValues 5=.rational fee :=
    (denseReadHeaderValues_preserves (denseEncodeEntry entry) 13 5 values (Or.inl (by decide))).trans hfee
  have loadedPenalty : loadedValues 2=.rational penalty :=
    (denseReadHeaderValues_preserves (denseEncodeEntry entry) 13 2 values (Or.inl (by decide))).trans hpenalty
  have stats:=denseReadHeaderValues_repair_stats entry values
  have loadedBound:=loadSafe loaded (List.mem_of_getLast? loadLast)
  have badCounter : natBits ((origin+(loadDenseEntryCode 36 13).length)+(positiveBadCode (origin+(loadDenseEntryCode 36 13).length)).length)≤budget := by
    simpa only [loadedBadCode,List.length_append,Nat.add_assoc] using counter
  obtain ⟨badTrace,after,badHead,badLast,badChain,badTime,afterHeader,ho,hr,hf,hb,objective,afterBase,afterPC,badFrame,badOutput,badMemory,badSafe⟩:=
    positiveBadCode_trace_bits program input (origin+(loadDenseEntryCode 36 13).length) P previous tools fee penalty loaded base n k budget S L T loadedValues
      actualPC loadedHeader loadedBase loadedFee loadedPenalty stats.1 stats.2.1 stats.2.2 loadedBound observation repairs failure feeBits penaltyBits room addressBits badCounter fetch.append_right
  have joined:=joinTrace_spec program input loadTrace badTrace before loaded after 705 3600 loadHead loadLast badHead badLast loadChain badChain loadTime badTime
  refine ⟨joinTrace loadTrace badTrace,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,afterHeader,ho,hr,hf,hb,objective,afterBase,?_,
    loadFrame.trans badFrame,badOutput.trans loadOutput,joinTrace_memory loadTrace badTrace before loaded base loadLast loadMemory badMemory,
    PDCompute.Pack.joinTrace_invariant loadTrace badTrace (fun state=>RootD27.Bits.SafeBits state budget) loadSafe badSafe⟩
  simpa only [loadedBadCode,List.length_append,Nat.add_assoc] using afterPC

end PDCompute.Solver
