module

public import Paid.PDROC_CalibrationRow_Init_002
public import Paid.PDLower_CalibrationCompute_Increment_028

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

def initStorePrefixCode : List Instruction :=
  loadSlot 9 .old ++ [.natOp .add .address .old .index]

theorem initStoreLead_decompose :
    initStoreLeadCode=initStorePrefixCode++[.store .address .value] := rfl

theorem initStoreLead_prefix_frames (input : List Cell) (before : State) (base M cursor : ℕ)
    (fresh : before.register .fresh=.natural base)
    (live : base+9 ∈ before.live) (read : before.heap (base+9)=.natural (firstRow base))
    (index : before.register .index=.natural cursor) (inside : cursor<rowWidth M) :
    LinearFrames (region base M) input initStoreLeadCode before := by
  rw [initStoreLead_decompose]
  apply single_last_frames (region base M) input initStorePrefixCode (.store .address .value)
    before (initStoreLeadResult before base cursor)
  · intro instruction member state
    simp only [initStorePrefixCode,loadSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with (h|h|h)|h <;> subst instruction <;> trivial
  · rw [←initStoreLead_decompose]
    exact initStoreLead_execute input before base cursor fresh live read index
  · exact initStoreLead_frame before base M cursor inside

def initStoreResult (before : State) (base cursor : ℕ) : State :=
  incrementSlotResult (initStoreLeadResult before base cursor) base 7 cursor

theorem initStore_body : (basicBlock Label.initStore).body=initStoreLeadCode++incrementSlot 7 := rfl

theorem initStore_execute (input : List Cell) (before : State) (base cursor : ℕ)
    (fresh : before.register .fresh=.natural base)
    (readLive : base+9 ∈ before.live) (read : before.heap (base+9)=.natural (firstRow base))
    (cursorLive : base+7 ∈ before.live) (cursorValue : before.heap (base+7)=.natural cursor)
    (index : before.register .index=.natural cursor) :
    linearExecute input (basicBlock .initStore).body before=some (initStoreResult before base cursor) := by
  rw [initStore_body,linearExecute_append,initStoreLead_execute input before base cursor fresh readLive read index,
    Option.bind_some]
  have fields := initStoreLead_fields before base cursor
  apply incrementSlot_execute input _ base 7 cursor (fields.2.2.1.trans fresh)
  · rw [fields.2.1]
    exact Finset.mem_insert_of_mem cursorLive
  · rw [fields.1,Function.update_of_ne (by unfold firstRow; omega : base+7≠firstRow base+cursor)]
    exact cursorValue

theorem initStore_fields (before : State) (base cursor : ℕ) :
    (initStoreResult before base cursor).heap=
      Function.update (Function.update before.heap (firstRow base+cursor) (before.register .value))
        (base+7) (.natural (cursor+1)) ∧
    (initStoreResult before base cursor).live=insert (base+7) (insert (firstRow base+cursor) before.live) ∧
    (initStoreResult before base cursor).register .fresh=before.register .fresh ∧
    (initStoreResult before base cursor).register .index=.natural (cursor+1) ∧
    (initStoreResult before base cursor).pc=before.pc+13 ∧
    (initStoreResult before base cursor).output=before.output := by
  simp [initStoreResult,incrementSlotResult,incrementSlotLoaded,storeSlotResult,loadSlotResult,
    initStoreLeadResult,writeCell,State.set,Nat.add_assoc]

theorem initStore_frame (before : State) (base M cursor : ℕ) (inside : cursor<rowWidth M) :
    MemoryFrame (region base M) before (initStoreResult before base cursor) := by
  apply (initStoreLead_frame before base M cursor inside).trans
  apply frame_of_one_update (region base M) (initStoreLeadResult before base cursor)
    (initStoreResult before base cursor) (base+7) (.natural (cursor+1))
    (header_mem_region base M 7 (by decide) (by decide))
  · simp [initStoreResult,incrementSlotResult,incrementSlotLoaded,storeSlotResult,loadSlotResult]
  · rfl

def initIncrementPrefixCode (offset : ℕ) : List Instruction :=
  loadSlot offset .index ++ [.constant .flag (.natural 1),.natOp .add .index .index .flag,
    .constant .address (.natural offset),.natOp .add .address .fresh .address]

/-- Only the framing proof is new; execution uses the original frozen
incrementSlot_execute macro rather than another increment implementation. -/
theorem incrementSlot_prefix_frames (region : Finset ℕ) (input : List Cell) (before : State)
    (base offset cursor : ℕ)
    (fresh : before.register .fresh=.natural base)
    (live : base+offset ∈ before.live) (value : before.heap (base+offset)=.natural cursor)
    (inside : base+offset ∈ region) :
    LinearFrames region input (incrementSlot offset) before := by
  have code : incrementSlot offset=initIncrementPrefixCode offset++[.store .address .index] := rfl
  rw [code]
  apply single_last_frames region input (initIncrementPrefixCode offset) (.store .address .index)
    before (incrementSlotResult before base offset cursor)
  · intro instruction member state
    simp only [initIncrementPrefixCode,loadSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with (h|h|h)|(h|h|h|h) <;> subst instruction <;> trivial
  · rw [←code]
    exact incrementSlot_execute input before base offset cursor fresh live value
  · apply frame_of_one_update region before _ (base+offset) (.natural (cursor+1)) inside
    · simp [incrementSlotResult,incrementSlotLoaded,storeSlotResult,loadSlotResult]
    · rfl

theorem initIncrement_prefix_frames (input : List Cell) (before : State) (base M cursor : ℕ)
    (fresh : before.register .fresh=.natural base)
    (live : base+7 ∈ before.live) (value : before.heap (base+7)=.natural cursor) :
    LinearFrames (region base M) input (incrementSlot 7) before :=
  incrementSlot_prefix_frames (region base M) input before base 7 cursor fresh live value
    (header_mem_region base M 7 (by decide) (by decide))

theorem initStore_prefix_frames (input : List Cell) (before : State) (base M cursor : ℕ)
    (fresh : before.register .fresh=.natural base)
    (readLive : base+9 ∈ before.live) (read : before.heap (base+9)=.natural (firstRow base))
    (cursorLive : base+7 ∈ before.live) (cursorValue : before.heap (base+7)=.natural cursor)
    (index : before.register .index=.natural cursor) (inside : cursor<rowWidth M) :
    LinearFrames (region base M) input (basicBlock .initStore).body before := by
  rw [initStore_body]
  have lead := initStoreLead_execute input before base cursor fresh readLive read index
  apply LinearFrames.append (region base M) input initStoreLeadCode (incrementSlot 7)
    before (initStoreLeadResult before base cursor) lead
    (initStoreLead_prefix_frames input before base M cursor fresh readLive read index inside)
  have fields := initStoreLead_fields before base cursor
  apply initIncrement_prefix_frames input _ base M cursor (fields.2.2.1.trans fresh)
  · rw [fields.2.1]
    exact Finset.mem_insert_of_mem cursorLive
  · rw [fields.1,Function.update_of_ne (by unfold firstRow; omega : base+7≠firstRow base+cursor)]
    exact cursorValue

theorem initStore_delta_prefix (P : Parameters) (before : State) (base level cursor : ℕ)
    (inside : cursor<2*level+1)
    (prefixRow : RowPrefix before (firstRow base) (P.walkRow level true 0) cursor)
    (source : before.register .value=.rational (if cursor=level then 1 else 0)) :
    RowPrefix (initStoreResult before base cursor) (firstRow base) (P.walkRow level true 0) (cursor+1) := by
  have stored := initStoreLead_delta_prefix P before base level cursor inside prefixRow source
  apply RowPrefix.transport (initStoreLeadResult before base cursor) (initStoreResult before base cursor)
    (firstRow base) (P.walkRow level true 0) (cursor+1) stored
  · change (initStoreLeadResult before base cursor).live ⊆
      insert (base+7) (initStoreLeadResult before base cursor).live
    exact fun _ member => Finset.mem_insert_of_mem member
  · intro i bound
    change (Function.update (initStoreLeadResult before base cursor).heap (base+7) _)
      (firstRow base+i)=(initStoreLeadResult before base cursor).heap (firstRow base+i)
    exact Function.update_of_ne (by unfold firstRow; omega) _ _

theorem initStore_header (P : Parameters) (before : State) (base level cursor : ℕ)
    (header : Header P base level before) (inside : cursor<rowWidth P.certificate.M) :
    Header P base level (initStoreResult before base cursor) := by
  apply Header.transport P base level before (initStoreResult before base cursor) header
    (initStore_frame before base P.certificate.M cursor inside)
  · rw [(initStore_fields before base cursor).2.1]
    exact fun _ member => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem member)
  · exact (initStore_fields before base cursor).2.2.1

def initStoreNext (origin : ℕ) (before : State) (base cursor : ℕ) : State :=
  {initStoreResult before base cursor with pc:=labelAddress origin .initGate}

theorem initStore_control_execute (origin : ℕ) (input : List Cell) (before : State) (base cursor : ℕ) :
    (controlInstruction origin (basicBlock .initStore).control).execute input
      (initStoreResult before base cursor)=some (initStoreNext origin before base cursor) := rfl

theorem initStore_trace (origin : ℕ) (input : List Cell) (before : State) (base cursor : ℕ)
    (position : before.pc=labelAddress origin .initStore)
    (fresh : before.register .fresh=.natural base)
    (readLive : base+9 ∈ before.live) (read : before.heap (base+9)=.natural (firstRow base))
    (cursorLive : base+7 ∈ before.live) (cursorValue : before.heap (base+7)=.natural cursor)
    (index : before.register .index=.natural cursor) :
    ∃ trace : List State,trace.head?=some before ∧
      trace.getLast?=some (initStoreNext origin before base cursor) ∧ trace.length=15 ∧
      trace.IsChain (fun a b => step (locatedBlock origin (kernel origin)) input a=some b) ∧
      time (locatedBlock origin (kernel origin)) trace≤225 ∧
      ∀ state∈trace,state.output=before.output ∧ state.register .fresh=before.register .fresh := by
  exact row_block_trace origin input .initStore (by rfl) before (initStoreResult before base cursor)
    (initStoreNext origin before base cursor) position
    (initStore_execute input before base cursor fresh readLive read cursorLive cursorValue index)
    (initStore_control_execute origin input before base cursor)

end PDROC.CalibrationRow
