module
public import Paid.PDCompute_Pack_WordStream_040
public import Paid.PDCompute_Pack_InitializeTrace_024

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation  PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

theorem tableLength_stream : tableLengthCode=wordStreamCode outputStart rowRemaining := rfl

def initializedValues (values : ℕ → Cell) (base n k : ℕ) : ℕ → Cell :=
  Function.update (initializeHeaderValues values base n k) outputCursor (.natural (resultBase base n k+1))

/-- All63 original initialization instructions really execute, including
the first actual output word for the table length. -/
theorem initialize_trace (program : Program) (input : List Cell) (origin : ℕ) (before : State)
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
      ∀ state∈trace,RegionMemory before state (writeRegion base n k) := by
  have initFetch : FetchesCode program before.pc initializeHeaderCode := by rw [pc];exact fetch_initializeHeader program origin code
  obtain ⟨initTrace,initHead,initLast,initChain,initTime,initHeader,initBase,initPC,initOutput,initMemory⟩:=
    initializeHeader_trace program input before base n k values header hbase hn hk initFetch
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
  obtain ⟨wordTrace,after,wordHead,wordLast,wordChain,wordTime,afterHeader,heap,afterBase,afterPC,afterOutput,wordMemory⟩:=
    wordStream_trace program input ready base (resultBase base n k) outputStart rowRemaining n k _ initHeader
      (by decide) (by decide) initBase readyPointer (Or.inr outside) (le_refl _) capacity wordFetch
  have finalPC : after.pc=origin+63 := by omega
  have initialRegion : ∀ state∈initTrace,RegionMemory before state (writeRegion base n k):=
    fun state member=>headerMemory_region base n k (initMemory state member)
  have joined:=joinTrace_spec program input initTrace wordTrace before ready after 780 240
    initHead initLast wordHead wordLast initChain wordChain initTime wordTime
  refine ⟨joinTrace initTrace wordTrace,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    afterHeader,?_,afterBase,finalPC,afterOutput.trans initOutput,
    RegionMemory.join_trace initTrace wordTrace before ready _ initLast initialRegion wordMemory⟩
  simpa only [readyRows] using heap

end PDCompute.Pack
