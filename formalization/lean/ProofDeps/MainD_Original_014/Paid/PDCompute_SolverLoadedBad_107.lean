module

public import Paid.PDCompute_SolverEntryLoader_090
public import Paid.PDCompute_SolverBadBranchRuntime_078

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

def loadedBadCode (origin : ℕ) : List Instruction :=
  loadDenseEntryCode 36 13++positiveBadCode (origin+(loadDenseEntryCode 36 13).length)

def loadedBadValues (values : ℕ → Cell) (fee penalty : ℚ) (entry : MenuEntry) : ℕ → Cell :=
  positiveBadValues (denseReadHeaderValues (denseEncodeEntry entry) 13 values) fee penalty entry

/-- The positive-tools branch reads the REAL previous-tools dense entry,
then executes the original repaired-versus-abandon strict comparison. -/
theorem loadedBad_trace_memory (program : Program) (input : List Cell) (origin : ℕ)
    (P : Parameters) (fee penalty : ℚ) (previous : MenuRow) (tools pointer : ℕ)
    (before : State) (base n k : ℕ) (values : ℕ → Cell)
    (hpc : before.pc=origin) (header : Header before base values)
    (hbase : before.register .fresh=.natural base) (hpointer : values 36=.natural pointer)
    (hfee : values 5=.rational fee) (hpenalty : values 2=.rational penalty)
    (source : PDLower.CalibrationCompute.HeapList before pointer (denseEncodeEntry (previous.getD tools abandonEntry)))
    (outside : ∀ offset < 6,pointer+offset < base ∨ base+headerWords ≤ pointer+offset)
    (fetch : FetchesCode program origin (loadedBadCode origin)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 4305 ∧
      Header after base (loadedBadValues values fee penalty (previous.getD tools abandonEntry)) ∧
      after.heap (base+31)=.rational (P.menuBadBranch fee penalty previous (tools+1)).2.observation ∧
      after.heap (base+32)=.rational (P.menuBadBranch fee penalty previous (tools+1)).2.repairs ∧
      after.heap (base+33)=.rational (P.menuBadBranch fee penalty previous (tools+1)).2.failure ∧
      after.heap (base+34)=.natural (if (P.menuBadBranch fee penalty previous (tools+1)).1=.repair then 1 else 0) ∧
      after.heap (base+22)=.rational ((P.menuBadBranch fee penalty previous (tools+1)).2.objective fee penalty) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+(loadedBadCode origin).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace,HeaderMemory before state base := by
  let entry:=previous.getD tools abandonEntry
  let loadedValues:=denseReadHeaderValues (denseEncodeEntry entry) 13 values
  have loadFetch : FetchesCode program before.pc (loadDenseEntryCode 36 13) := by
    rw [hpc]
    exact fetch.append_left
  obtain ⟨loadTrace,loaded,loadHead,loadLast,loadChain,loadTime,loadedHeader,loadedBase,_,loadedPC,loadFrame,loadOutput,loadMemory⟩:=
    loadDenseEntry_trace_memory program input before base 36 13 pointer n k values entry header hbase (by decide) (by decide)
      hpointer source outside loadFetch
  have actualPC : loaded.pc=origin+(loadDenseEntryCode 36 13).length := by rw [loadedPC,hpc,loadDenseEntryCode_length]
  have badFetch : FetchesCode program (origin+(loadDenseEntryCode 36 13).length)
      (positiveBadCode (origin+(loadDenseEntryCode 36 13).length)) := fetch.append_right
  have loadedFee : loadedValues 5=.rational fee :=
    (denseReadHeaderValues_preserves (denseEncodeEntry entry) 13 5 values (Or.inl (by decide))).trans hfee
  have loadedPenalty : loadedValues 2=.rational penalty :=
    (denseReadHeaderValues_preserves (denseEncodeEntry entry) 13 2 values (Or.inl (by decide))).trans hpenalty
  have stats:=denseReadHeaderValues_repair_stats entry values
  obtain ⟨badTrace,after,badHead,badLast,badChain,badTime,afterHeader,ho,hr,hf,hb,objective,afterBase,afterPC,
    badFrame,badOutput,badMemory⟩:=
    positiveBadCode_trace_memory program input (origin+(loadDenseEntryCode 36 13).length) P previous tools fee penalty
      loaded base n k loadedValues actualPC loadedHeader loadedBase loadedFee loadedPenalty stats.1 stats.2.1 stats.2.2 badFetch
  have joined:=joinTrace_spec program input loadTrace badTrace before loaded after 705 3600
    loadHead loadLast badHead badLast loadChain badChain loadTime badTime
  refine ⟨joinTrace loadTrace badTrace,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    afterHeader,ho,hr,hf,hb,objective,afterBase,?_,loadFrame.trans badFrame,badOutput.trans loadOutput,
    joinTrace_memory loadTrace badTrace before loaded base loadLast loadMemory badMemory⟩
  rw [afterPC,loadedBadCode,List.length_append]
  exact Nat.add_assoc _ _ _

end PDCompute.Solver
