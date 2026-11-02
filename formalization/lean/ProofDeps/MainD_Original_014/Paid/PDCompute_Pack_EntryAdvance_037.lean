module
public import Paid.PDCompute_Pack_CounterBack_033
public import Paid.PDCompute_Pack_PointerMemory_017
public import Paid.PDCompute_Pack_Fragments_018
public import Paid.PDCompute_SolverMemoryJoin_062

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (storeSlot storeSlotResult)

def entryAdvanceValues (values : ℕ → Cell) (pointer count : ℕ) : ℕ → Cell :=
  Function.update (Function.update values outputCursor (.natural pointer)) columnRemaining (.natural (count-1))

/-- Real cursor save, real column decrement, and real back-edge to85. -/
theorem entryAdvance_trace (program : Program) (input : List Cell) (origin : ℕ) (before : State)
    (base pointer count : ℕ) (values : ℕ → Cell)
    (code : FetchesCode program origin (serializerCode origin)) (pc : before.pc=origin+201)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hpointer : before.register .old=.natural pointer) (hcount : values columnRemaining=.natural count) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 210 ∧
      Header after base (entryAdvanceValues values pointer count) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+85 ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base := by
  have fetched:=fetch_entryAdvance program origin code
  unfold entryAdvanceCode at fetched
  simp only [List.append_assoc] at fetched
  have fetchSave : FetchesCode program before.pc (storeSlot outputCursor .old) := by
    rw [pc]
    exact fetched.append_left
  obtain ⟨saveTrace,saveHead,saveLast,saveChain,saveTime,saveMemory⟩:=
    header.storeSlot_trace_memory program input outputCursor .old (by decide) hbase (by decide) fetchSave
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
  obtain ⟨backTrace,after,backHead,backLast,backChain,backTime,afterHeader,afterBase,afterPC,afterOutput,backMemory⟩:=
    counterBack_trace program input saved base columnRemaining count (origin+85) _ savedHeader (by decide) savedBase savedCount fetchBack
  have joined:=joinTrace_spec program input saveTrace backTrace before saved after 60 150
    saveHead saveLast backHead backLast saveChain backChain saveTime backTime
  exact ⟨joinTrace saveTrace backTrace,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    afterHeader,afterBase,afterPC,afterOutput.trans savedOutput,
    joinTrace_memory saveTrace backTrace before saved base saveLast saveMemory backMemory⟩

end PDCompute.Pack
