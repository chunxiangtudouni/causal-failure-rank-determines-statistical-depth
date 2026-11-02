module
public import Paid.PDCompute_Pack_CounterBackBits_083
public import Paid.PDCompute_Pack_SlotBitTrace_064
public import Paid.PDCompute_Pack_EntryAdvance_037

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (storeSlot storeSlotResult)

theorem entryAdvance_trace_safe (program : Program) (input : List Cell) (origin : ℕ) (before : State)
    (base pointer count budget : ℕ) (values : ℕ → Cell)
    (code : FetchesCode program origin (serializerCode origin)) (pc : before.pc=origin+201)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hpointer : before.register .old=.natural pointer) (hcount : values columnRemaining=.natural count)
    (safe : SafeBits before budget) (addressBits : ∀ slot<headerWords,1+natBits (base+slot) ≤ budget)
    (oneBits : 1+natBits 1 ≤ budget) (pcBits : ∀ counter ≤ origin+233,natBits counter ≤ budget) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 210 ∧
      Header after base (entryAdvanceValues values pointer count) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+85 ∧ after.output=before.output ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,SafeBits state budget) := by
  have fetched:=fetch_entryAdvance program origin code
  unfold entryAdvanceCode at fetched
  simp only [List.append_assoc] at fetched
  have fetchSave : FetchesCode program before.pc (storeSlot outputCursor .old) := by
    rw [pc]
    exact fetched.append_left
  obtain ⟨saveTrace,saveHead,saveLast,saveChain,saveTime,saveMemory,saveBits⟩:=
    storeSlot_trace_safe program input before base outputCursor budget .old values header (by decide) hbase (by decide)
      safe (addressBits outputCursor (by decide)) (pcBits _ (by omega)) fetchSave
  let saved:=storeSlotResult before base outputCursor .old
  have savedHeader : Header saved base (Function.update values outputCursor (.natural pointer)) := by
    simpa only [hpointer] using header_store_result header outputCursor .old
  have savedBase : saved.register .fresh=.natural base := by simp [saved,storeSlotResult,hbase]
  have savedPC : saved.pc=before.pc+3 := rfl
  have savedOutput : saved.output=before.output := rfl
  have savedCount : (Function.update values outputCursor (.natural pointer)) columnRemaining=.natural count := by
    simpa only [Function.update_of_ne (by decide : columnRemaining≠outputCursor)] using hcount
  have fetchBack : FetchesCode program saved.pc (counterBackCode columnRemaining (origin+85)) := by
    rw [savedPC,pc]
    simpa only [counterBackCode,storeSlot,List.length_cons,List.length_nil] using fetched.append_right
  have savedSafe : SafeBits saved budget:=saveBits saved (List.mem_of_getLast? saveLast)
  obtain ⟨backTrace,after,backHead,backLast,backChain,backTime,afterHeader,afterBase,afterPC,afterOutput,backMemory,backBits⟩:=
    counterBack_trace_safe program input saved base columnRemaining count (origin+85) budget _ savedHeader (by decide) savedBase savedCount
      savedSafe (addressBits columnRemaining (by decide)) oneBits (pcBits _ (by rw [savedPC];omega)) (pcBits _ (by omega)) fetchBack
  have joined:=joinTrace_spec program input saveTrace backTrace before saved after 60 150
    saveHead saveLast backHead backLast saveChain backChain saveTime backTime
  exact ⟨joinTrace saveTrace backTrace,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    afterHeader,afterBase,afterPC,afterOutput.trans savedOutput,
    joinTrace_memory saveTrace backTrace before saved base saveLast saveMemory backMemory,joinTrace_invariant saveTrace backTrace (fun state=>SafeBits state budget) saveBits backBits⟩


end PDCompute.Pack
