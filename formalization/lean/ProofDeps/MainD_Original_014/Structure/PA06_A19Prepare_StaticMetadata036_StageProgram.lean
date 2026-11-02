module

public import Structure.PA06_A19Prepare_StaticMetadata036_StageSemantics

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Genuine fixed202-op stage×node×tool controller. CB22=stage,
CB19=node, CB20=tool, CB23=streaming equality flag, CB24=raw stage bit.
All raw stage reads and022 node queries are executed; no dense matrix is
created. Ordinary stage output is written after DP, before037/033. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (loadRel storeRel setRel incrementRel)

def stageInitialize : List PackingOp := setRel 22 0

def stageRowInitialize : List PackingOp :=
  loadRel .old 22 ++ [.base (.base (.constant .value 0))] ++ storeField .stage ++ setRel 19 0

def stageNodeInitialize : List PackingOp := setRel 23 1 ++ setRel 20 0

def stageRead : List PackingOp :=
  loadRel .total 22 ++ loadRel .value 1 ++ [.arithmetic .multiply .total .total .value] ++
    loadRel .fresh 20 ++ [.base (.base (.add .total .total .fresh)),
      .base (.base (.constant .index 2)), .base (.base (.add .index .total .index)),
      .base (.base (.loadROM .input .value .index))] ++ storeRel .value 24

def stageCompare : List PackingOp :=
  loadRel .total 24 ++ [.base (.subtract .flag .value .total), .base (.subtract .total .total .value),
    .base (.base (.add .flag .flag .total))] ++ loadRel .total 23 ++
    [.base (.base (.constant .index 0)), .base (.base (.select .total .flag .index .total))] ++ storeRel .total 23

def stageNodeWriteTest (skip : Nat) : List PackingOp :=
  loadRel .value 23 ++ [.base (.base (.constant .index (5 * skip))), .jumpIfZero .value .index]

def stageRecord : List PackingOp := loadRel .old 22 ++ loadRel .value 19 ++
  [.base (.base (.constant .total 1)), .base (.base (.add .value .value .total))] ++ storeField .stage

def stageToolTail (start : Nat) : List PackingOp := incrementRel 20 ++ jumpTo (start + 51)
def stageNodeTail (start : Nat) : List PackingOp := incrementRel 19 ++ jumpTo (start + 34)
def stageOuterTail (start : Nat) : List PackingOp := incrementRel 22 ++ jumpTo (start + 4)

def stageProgramAt (start : Nat) : List PackingOp :=
  stageInitialize ++ scanBoundedTest 0 22 (start + 202) ++ stageRowInitialize ++
    scanBoundedTest 2 19 (start + 191) ++ stageNodeInitialize ++ scanBoundedTest 1 20 (start + 154) ++
    stageRead ++ scanArguments ++ PA06A19PrepareBankNodeBit022.programAt (start + 83) ++
    stageCompare ++ stageToolTail start ++ stageNodeWriteTest (start + 180) ++
    stageRecord ++ stageNodeTail start ++ stageOuterTail start

theorem stageProgramAt_length (start : Nat) : (stageProgramAt start).length = 202 := rfl

theorem stageRead_effect (rom : PhysicalROM) (CB stage tool q : Nat) (state : NatState)
    (hCB : state.register .address = CB) (hs : state.heap (CB + 22) = stage)
    (ht : state.heap (CB + 20) = tool) (hq : state.heap (CB + 1) = q)
    (hrom : rom.semantic.read .input 1 = q) :
    let after := runOps rom stageRead state
    after.register .address = CB ∧ after.heap = Function.update state.heap (CB + 24) (rawStageBit rom stage tool) := by
  simp [stageRead, loadRel, storeRel, rawStageBit, runOps, natExecuteOp, natArithmetic,
    Op.execute, Instruction.execute, hCB, hs, ht, hq, hrom, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem stageCompare_effect (rom : PhysicalROM) (CB oldMatch stageBit : Nat) (state : NatState)
    (hCB : state.register .address = CB) (hm : state.heap (CB + 23) = oldMatch)
    (hs : state.heap (CB + 24) = stageBit) :
    let after := runOps rom stageCompare state
    after.register .address = CB ∧ after.heap = Function.update state.heap (CB + 23)
      (if state.register .value = stageBit then oldMatch else 0) := by
  simp [stageCompare, loadRel, storeRel, runOps, natExecuteOp,
    Op.execute, Instruction.execute, hCB, hm, hs];
    split_ifs <;> congr 1 <;> omega

inductive StageChunk where
  | initialize | stageTest | rowInitialize | nodeTest | nodeInitialize | toolTest
  | read | arguments | compare | toolTail | writeTest | record | nodeTail | outerTail
  deriving DecidableEq

def stageChunkCode (start : Nat) : StageChunk → List PackingOp
  | .initialize => stageInitialize
  | .stageTest => scanBoundedTest 0 22 (start + 202)
  | .rowInitialize => stageRowInitialize
  | .nodeTest => scanBoundedTest 2 19 (start + 191)
  | .nodeInitialize => stageNodeInitialize
  | .toolTest => scanBoundedTest 1 20 (start + 154)
  | .read => stageRead
  | .arguments => scanArguments
  | .compare => stageCompare
  | .toolTail => stageToolTail start
  | .writeTest => stageNodeWriteTest (start + 180)
  | .record => stageRecord
  | .nodeTail => stageNodeTail start
  | .outerTail => stageOuterTail start

def stageChunkOffset : StageChunk → Nat
  | .initialize => 0 | .stageTest => 4 | .rowInitialize => 13 | .nodeTest => 34
  | .nodeInitialize => 43 | .toolTest => 51 | .read => 60 | .arguments => 77
  | .compare => 129 | .toolTail => 143 | .writeTest => 154 | .record => 159
  | .nodeTail => 180 | .outerTail => 191

def stageChunkLength : StageChunk → Nat
  | .initialize => 4 | .stageTest => 9 | .rowInitialize => 21 | .nodeTest => 9
  | .nodeInitialize => 8 | .toolTest => 9 | .read => 17 | .arguments => 6
  | .compare => 14 | .toolTail => 11 | .writeTest => 5 | .record => 21
  | .nodeTail => 11 | .outerTail => 11

def stageChunkLead (start : Nat) (chunk : StageChunk) : List PackingOp :=
  (stageChunkCode start chunk).take (stageChunkLength chunk - 1)
def stageChunkLast (start : Nat) (chunk : StageChunk) : PackingOp :=
  (stageChunkCode start chunk).getD (stageChunkLength chunk - 1) scanPaddingOp

theorem stage_chunk_length (start : Nat) (chunk : StageChunk) :
    (stageChunkCode start chunk).length = stageChunkLength chunk := by cases chunk <;> rfl

theorem stage_chunk_span (chunk : StageChunk) : stageChunkOffset chunk + stageChunkLength chunk ≤ 202 := by
  cases chunk <;> decide

theorem stage_chunk_lead_length (start : Nat) (chunk : StageChunk) :
    (stageChunkLead start chunk).length + 1 = stageChunkLength chunk := by cases chunk <;> rfl

theorem stage_chunk_split (start : Nat) (chunk : StageChunk) :
    stageChunkCode start chunk = stageChunkLead start chunk ++ [stageChunkLast start chunk] := by cases chunk <;> rfl

private def stageBlocks (start : Nat) : List (List PackingOp) :=
  [stageChunkCode start .initialize, stageChunkCode start .stageTest,
   stageChunkCode start .rowInitialize, stageChunkCode start .nodeTest,
   stageChunkCode start .nodeInitialize, stageChunkCode start .toolTest,
   stageChunkCode start .read, stageChunkCode start .arguments,
   PA06A19PrepareBankNodeBit022.programAt (start + 83),
   stageChunkCode start .compare, stageChunkCode start .toolTail,
   stageChunkCode start .writeTest, stageChunkCode start .record,
   stageChunkCode start .nodeTail, stageChunkCode start .outerTail]

private def stageChunkIndex : StageChunk → Nat
  | .initialize => 0 | .stageTest => 1 | .rowInitialize => 2 | .nodeTest => 3
  | .nodeInitialize => 4 | .toolTest => 5 | .read => 6 | .arguments => 7
  | .compare => 9 | .toolTail => 10 | .writeTest => 11 | .record => 12
  | .nodeTail => 13 | .outerTail => 14

private def stageChunkBefore (start : Nat) (chunk : StageChunk) : List PackingOp :=
  ((stageBlocks start).take (stageChunkIndex chunk)).flatten

private def stageChunkAfter (start : Nat) (chunk : StageChunk) : List PackingOp :=
  ((stageBlocks start).drop (stageChunkIndex chunk + 1)).flatten

private theorem stage_chunk_decomposition (start : Nat) (chunk : StageChunk) :
    stageProgramAt start =
      stageChunkBefore start chunk ++ stageChunkCode start chunk ++ stageChunkAfter start chunk := by
  cases chunk <;>
    simp only [stageProgramAt, stageChunkBefore, stageChunkAfter, stageChunkIndex,
      stageBlocks, stageChunkCode, List.take_succ_cons, List.take_zero,
      List.drop_succ_cons, List.drop_zero, List.flatten_cons, List.flatten_nil,
      List.nil_append, List.append_nil, List.append_assoc]

private theorem stage_chunk_before_length (start : Nat) (chunk : StageChunk) :
    (stageChunkBefore start chunk).length = stageChunkOffset chunk := by
  cases chunk <;>
    simp only [stageChunkBefore, stageChunkIndex, stageBlocks,
      List.take_succ_cons, List.take_zero, List.flatten_cons, List.flatten_nil,
      List.length_append, List.length_nil, stage_chunk_length, stageChunkLength,
      stageChunkOffset, PA06A19PrepareBankNodeBit022.programAt_length]

private theorem stage_getD_middle (left middle right : List PackingOp) (position : Nat)
    (hp : position < middle.length) :
    (left ++ middle ++ right).getD (left.length + position) scanPaddingOp =
      middle.getD position scanPaddingOp := by
  rw [List.getD_append (left ++ middle) right scanPaddingOp _
      (by simp only [List.length_append]; omega),
    List.getD_append_right left middle scanPaddingOp _ (by omega), Nat.add_sub_cancel_left]

theorem stage_chunk_slice (start : Nat) (chunk : StageChunk) (position : Nat) (hp : position < stageChunkLength chunk) :
    (stageProgramAt start).getD (stageChunkOffset chunk + position) scanPaddingOp =
      (stageChunkCode start chunk).getD position scanPaddingOp := by
  rw [stage_chunk_decomposition start chunk, ← stage_chunk_before_length start chunk]
  exact stage_getD_middle (stageChunkBefore start chunk) (stageChunkCode start chunk)
    (stageChunkAfter start chunk) position (by rw [stage_chunk_length]; exact hp)

theorem stage_chunk_lead_noJump (start : Nat) (chunk : StageChunk) :
    ∀ op ∈ stageChunkLead start chunk, NoJump op := by
  cases chunk <;>
    simp [stageChunkLead, stageChunkCode, stageChunkLength, stageInitialize, scanBoundedTest,
      stageRowInitialize, stageNodeInitialize, stageRead, scanArguments, stageCompare,
      stageToolTail, stageNodeWriteTest, stageRecord, stageNodeTail, stageOuterTail,
      loadRel, storeRel, setRel, incrementRel, jumpTo, storeField, fieldPointer,
      fieldPointerLead, fieldPointerExtra, NoJump]

def StageCodeAt (containing : List PackingOp) (start : Nat) : Prop :=
  start + 202 ≤ containing.length ∧ ∀ position < 202,
    containing.getD (start + position) scanPaddingOp = (stageProgramAt start).getD position scanPaddingOp

theorem stage_append_code (left right : List PackingOp) :
    StageCodeAt (left ++ stageProgramAt left.length ++ right) left.length := by
  constructor
  · simp only [List.length_append, stageProgramAt_length]
    omega
  · intro position hp
    rw [List.getD_append (left ++ stageProgramAt left.length) right scanPaddingOp _
      (by simp only [List.length_append, stageProgramAt_length]; omega),
      List.getD_append_right left (stageProgramAt left.length) scanPaddingOp _ (by omega),
      Nat.add_sub_cancel_left]

private theorem stage_query_slice (start position : Nat) (hp : position < 46) :
    (stageProgramAt start).getD (83 + position) scanPaddingOp =
      (PA06A19PrepareBankNodeBit022.programAt (start + 83)).getD position scanPaddingOp := by
  let leading := ((stageBlocks start).take 8).flatten
  let trailing := ((stageBlocks start).drop 9).flatten
  have leadingLength : leading.length = 83 := by
    simp only [leading, stageBlocks, List.take_succ_cons, List.take_zero,
      List.flatten_cons, List.flatten_nil, List.length_append, List.length_nil,
      stage_chunk_length, stageChunkLength]
  have layout : stageProgramAt start =
      leading ++ PA06A19PrepareBankNodeBit022.programAt (start + 83) ++ trailing := by
    simp only [stageProgramAt, leading, trailing, stageBlocks, stageChunkCode,
      List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
      List.flatten_cons, List.flatten_nil, List.append_nil,
      List.append_assoc]
  have selected := stage_getD_middle leading
    (PA06A19PrepareBankNodeBit022.programAt (start + 83)) trailing position
    (by rw [PA06A19PrepareBankNodeBit022.programAt_length]; exact hp)
  rw [← layout, leadingLength] at selected
  exact selected

theorem stage_query_code (containing : List PackingOp) (start : Nat) (code : StageCodeAt containing start) :
    ScanQueryCodeAt containing (start + 83) := by
  constructor
  · have h := code.1
    omega
  · intro position hp
    have h := code.2 (83 + position) (by omega)
    have hs := stage_query_slice start position hp
    have he : start + (83 + position) = start + 83 + position := by omega
    rw [he] at h
    exact h.trans hs

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
