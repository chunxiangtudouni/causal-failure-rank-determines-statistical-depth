module
public import Paid.PDCompute_Pack_InitializeHeaderBits_069
public import Paid.PDCompute_Pack_WordStreamBits_074
public import Paid.PDCompute_Pack_Initialize_042

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

theorem initialize_trace_budget (program : Program) (input : List Cell) (origin : ℕ) (before : State)
    (base n k : ℕ) (values : ℕ → Cell)
    (code : FetchesCode program origin (serializerCode origin)) (pc : before.pc=origin)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hn : values 3=.natural n) (hk : values 4=.natural k) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 1020 ∧
      Header after base (initializedValues values base n k) ∧
      HeapList after (resultBase base n k) [.natural (n+1)] ∧ after.register .fresh=.natural base ∧
      after.pc=origin+63 ∧ after.output=before.output ∧
      (∀ state∈trace,RegionMemory before state (writeRegion base n k)) ∧
      (∀ state∈trace,SafeBits state (serializerBudget before n k origin)) := by
  let budget:=serializerBudget before n k origin
  have naturalBound : ∀ value ≤ naturalCap base n k,1+natBits value ≤ budget:=
    fun value bound=>serializerBudget_natural before base n k origin value hbase bound
  have addressBits (slot : ℕ) (inside : slot<headerWords) : 1+natBits (base+slot) ≤ budget:=
    naturalBound _ (naturalCap_header_address base n k slot inside)
  have initFetch : FetchesCode program before.pc initializeHeaderCode := by rw [pc];exact fetch_initializeHeader program origin code
  obtain ⟨initTrace,initHead,initLast,initChain,initTime,initMemory,initBits⟩:=
    initializeHeader_trace_budget program input before base n k origin values header hbase hn hk pc initFetch
  have initHeader:=initializeHeader_header before base n k values header
  have initFields:=initializeHeader_fields before base n k
  have initBase : (initializeHeaderResult before base n k).register .fresh=.natural base:=initFields.1.trans hbase
  have initPC : (initializeHeaderResult before base n k).pc=before.pc+51:=initFields.2.1
  have initOutput : (initializeHeaderResult before base n k).output=before.output:=initFields.2.2
  let ready:=initializeHeaderResult before base n k
  have readyPC : ready.pc=before.pc+51:=initPC
  have readyPointer : initializeHeaderValues values base n k outputStart=.natural (resultBase base n k) := by
    simp [initializeHeaderValues,pointerValues,sourceCursor,outputCursor,outputStart]
  have readyRows : initializeHeaderValues values base n k rowRemaining=.natural (n+1) := by
    simp [initializeHeaderValues,pointerValues,counterValues,sourceCursor,outputCursor,outputStart,rowRemaining,columnsPerRow]
  have wordFetch : FetchesCode program ready.pc (wordStreamCode outputStart rowRemaining) := by
    rw [initPC,pc,←tableLength_stream]
    exact fetch_tableLength program origin code
  have outside : base+headerWords ≤ resultBase base n k := result_after_header base n k
  have capacity : resultBase base n k+1 ≤ resultBase base n k+resultCapacity n k := by
    simp only [resultCapacity]
    omega
  have readySafe : SafeBits ready budget:=initBits ready (List.mem_of_getLast? initLast)
  have pointerBits : 1+natBits (resultBase base n k+1) ≤ budget:=naturalBound _ (by rw [←naturalCap_result_end];exact capacity)
  have wordCounter : natBits (ready.pc+12) ≤ budget:=
    serializerBudget_pc before n k origin _ (by rw [readyPC,pc];omega)
  obtain ⟨wordTrace,after,wordHead,wordLast,wordChain,wordTime,afterHeader,heap,afterBase,afterPC,afterOutput,wordMemory,wordBits⟩:=
    wordStreamLocal_trace_safe program input ready base (resultBase base n k) outputStart rowRemaining budget _ initHeader
      (by decide) (by decide) initBase readyPointer (Or.inr outside) readySafe addressBits pointerBits wordCounter wordFetch
  have finalPC : after.pc=origin+63 := by omega
  have initialRegion : ∀ state∈initTrace,RegionMemory before state (writeRegion base n k):=
    fun state member=>headerMemory_region base n k (initMemory state member)
  have joined:=joinTrace_spec program input initTrace wordTrace before ready after 780 240
    initHead initLast wordHead wordLast initChain wordChain initTime wordTime
  refine ⟨joinTrace initTrace wordTrace,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    afterHeader,?_,afterBase,finalPC,afterOutput.trans initOutput,
    RegionMemory.join_trace initTrace wordTrace before ready _ initLast initialRegion
      (fun state member=>(wordMemory state member).enlarge (localRegion_write_subset base n k (resultBase base n k) 1 (le_refl _) capacity)),
    joinTrace_invariant initTrace wordTrace (fun state=>SafeBits state budget) initBits wordBits⟩
  simpa only [readyRows] using heap


end PDCompute.Pack
