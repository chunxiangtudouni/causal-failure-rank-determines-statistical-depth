module
public import Paid.PDCompute_Pack_SmallBits_060
public import Paid.PDCompute_Pack_ReadTailTrace_028

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult storeSlot storeSlotResult)

theorem readTail_prefix_safe (input : List Cell) (before after : State) (base source pointer tag budget count : ℕ)
    (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base) (hsource : before.register .old=.natural source)
    (hpointer : values outputCursor=.natural pointer) (htag : values entryStart=.natural tag)
    (safe : SafeBits before budget) (addressBits : ∀ slot<headerWords,1+natBits (base+slot) ≤ budget)
    (twoBits : 1+natBits 2 ≤ budget) (counter : natBits (before.pc+11) ≤ budget) (bound : count ≤ 11)
    (execute : linearExecute input (readTailCode.take count) before=some after) : SafeBits after budget := by
  have header1 : Header (sourceSaved before base) base (readTailValues values source) := by
    have h:=header_store_result header sourceCursor .old
    rw [hsource] at h
    exact h
  have header2 : Header (outputLoaded before base) base (readTailValues values source) := header1.loadSlot_preserves outputCursor .old
  have header3 : Header (tagLoaded before base) base (readTailValues values source) := header2.loadSlot_preserves entryStart .value
  have base1 : (sourceSaved before base).register .fresh=.natural base := by simp [sourceSaved,storeSlotResult,hbase]
  have base2 : (outputLoaded before base).register .fresh=.natural base :=
    (loadSlotResult_fresh (sourceSaved before base) base outputCursor .old (by decide)).trans base1
  have base3 : (tagLoaded before base).register .fresh=.natural base :=
    (loadSlotResult_fresh (outputLoaded before base) base entryStart .value (by decide)).trans base2
  have pointed : readTailValues values source outputCursor=.natural pointer := by
    simpa [readTailValues,sourceCursor,outputCursor] using hpointer
  have tagged : readTailValues values source entryStart=.natural tag := by
    simpa [readTailValues,sourceCursor,entryStart] using htag
  have value3 : (tagLoaded before base).register .value=.natural tag :=
    (header2.loadSlot_execute input entryStart .value (by decide) base2).2.trans tagged
  have run1 : linearExecute input (storeSlot sourceCursor .old) before=some (sourceSaved before base) :=
    PDLower.CalibrationCompute.storeSlot_execute input before base sourceCursor .old hbase (by decide)
  have run2 : linearExecute input (loadSlot outputCursor .old) (sourceSaved before base)=some (outputLoaded before base) :=
    (header1.loadSlot_execute input outputCursor .old (by decide) base1).1
  have run3 : linearExecute input (loadSlot entryStart .value) (outputLoaded before base)=some (tagLoaded before base) :=
    (header2.loadSlot_execute input entryStart .value (by decide) base2).1
  have pc1 : natBits (before.pc+3) ≤ budget:=(natBits_mono (by omega : before.pc+3 ≤ before.pc+11)).trans counter
  have pc2 : natBits ((sourceSaved before base).pc+3) ≤ budget:=by
    change natBits (before.pc+3+3) ≤ budget
    exact (natBits_mono (by omega : before.pc+3+3 ≤ before.pc+11)).trans counter
  have pc3 : natBits ((outputLoaded before base).pc+3) ≤ budget:=by
    change natBits (before.pc+3+3+3) ≤ budget
    exact (natBits_mono (by omega : before.pc+3+3+3 ≤ before.pc+11)).trans counter
  have pc4 : natBits ((tagLoaded before base).pc+2) ≤ budget:=by
    change natBits (before.pc+3+3+3+2) ≤ budget
    simpa only [Nat.add_assoc] using counter
  have safe1 : SafeBits (sourceSaved before base) budget:=storeSlotResult_safe before base sourceCursor budget .old safe (addressBits sourceCursor (by decide)) pc1
  have safe2 : SafeBits (outputLoaded before base) budget:=loadSlotResult_safe (sourceSaved before base) base outputCursor budget .old safe1
    (header1.live outputCursor (by decide)) (addressBits outputCursor (by decide)) pc2
  have safe3 : SafeBits (tagLoaded before base) budget:=loadSlotResult_safe (outputLoaded before base) base entryStart budget .value safe2
    (header2.live entryStart (by decide)) (addressBits entryStart (by decide)) pc3
  have prefix1 : ∀ take ≤ (storeSlot sourceCursor .old).length,∀ state,
      linearExecute input ((storeSlot sourceCursor .old).take take) before=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact storeSlot_prefix_safe input before state base sourceCursor budget take .old safe hbase (by decide)
      (addressBits sourceCursor (by decide)) pc1 takeBound run
  have prefix2 : ∀ take ≤ (loadSlot outputCursor .old).length,∀ state,
      linearExecute input ((loadSlot outputCursor .old).take take) (sourceSaved before base)=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact loadSlot_prefix_safe input (sourceSaved before base) state base outputCursor budget take .old safe1 base1
      (header1.live outputCursor (by decide)) (addressBits outputCursor (by decide)) pc2 takeBound run
  have prefix3 : ∀ take ≤ (loadSlot entryStart .value).length,∀ state,
      linearExecute input ((loadSlot entryStart .value).take take) (outputLoaded before base)=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact loadSlot_prefix_safe input (outputLoaded before base) state base entryStart budget take .value safe2 base2
      (header2.live entryStart (by decide)) (addressBits entryStart (by decide)) pc3 takeBound run
  have prefix4 : ∀ take ≤ tagDifferenceCode.length,∀ state,
      linearExecute input (tagDifferenceCode.take take) (tagLoaded before base)=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact tagDifference_prefix_safe input (tagLoaded before base) state tag budget take safe3 value3 twoBits pc4 takeBound run
  have tail:=invariant_prefix_append input (loadSlot entryStart .value) tagDifferenceCode (outputLoaded before base)
    (tagLoaded before base) run3 (fun state=>SafeBits state budget) prefix3 prefix4
  have middle:=invariant_prefix_append input (loadSlot outputCursor .old) (loadSlot entryStart .value++tagDifferenceCode)
    (sourceSaved before base) (outputLoaded before base) run2 (fun state=>SafeBits state budget) prefix2 tail
  have combined:=invariant_prefix_append input (storeSlot sourceCursor .old)
    (loadSlot outputCursor .old++(loadSlot entryStart .value++tagDifferenceCode)) before (sourceSaved before base)
    run1 (fun state=>SafeBits state budget) prefix1 middle
  have allPrefixes : ∀ take ≤ readTailCode.length,∀ state,
      linearExecute input (readTailCode.take take) before=some state → SafeBits state budget:=by
    simpa only [readTailCode,List.append_assoc] using combined
  exact allPrefixes count bound after execute

theorem readTail_trace_safe (program : Program) (input : List Cell) (before : State) (base source pointer tag budget : ℕ)
    (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base) (hsource : before.register .old=.natural source)
    (hpointer : values outputCursor=.natural pointer) (htag : values entryStart=.natural tag)
    (safe : SafeBits before budget) (addressBits : ∀ slot<headerWords,1+natBits (base+slot) ≤ budget)
    (twoBits : 1+natBits 2 ≤ budget) (counter : natBits (before.pc+11) ≤ budget)
    (fetched : FetchesCode program before.pc readTailCode) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (readTailResult before base tag) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤180 ∧
      Header (readTailResult before base tag) base (readTailValues values source) ∧
      (readTailResult before base tag).register .fresh=.natural base ∧
      (readTailResult before base tag).register .old=.natural pointer ∧
      (readTailResult before base tag).register .value=.natural (2-tag) ∧
      (readTailResult before base tag).pc=before.pc+11 ∧ (readTailResult before base tag).output=before.output ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,SafeBits state budget) := by
  have facts:=readTail_run_memory input before base source pointer tag values header hbase hsource hpointer htag
  obtain ⟨trace,hh,hl,hchain,ht,invariant⟩:=linearExecute_trace_invariant program input readTailCode readTail_straight before _ fetched facts.1
    (fun state=>HeaderMemory before state base ∧ SafeBits state budget) (by
      intro count bound state executed
      have countBound : count ≤ 11:=by simpa only [readTailCode_length] using bound
      exact ⟨facts.2.2.2.2.2 count bound state executed,
        readTail_prefix_safe input before state base source pointer tag budget count values header hbase hsource hpointer htag
          safe addressBits twoBits counter countBound executed⟩)
  refine ⟨trace,hh,hl,hchain,?_,facts.2.1,facts.2.2.1,facts.2.2.2.1,facts.2.2.2.2.1,
    readTail_pc before base tag,readTail_output before base tag,
    fun state member=>(invariant state member).1,fun state member=>(invariant state member).2⟩
  simpa only [readTailCode_length] using ht

end PDCompute.Pack
