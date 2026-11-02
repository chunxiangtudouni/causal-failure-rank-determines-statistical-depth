module

public import Structure.PA06_A19Prepare_StaticMetadata036_ScanQuery

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Fixed191-op full node×tool leaf/tool producer. Runtime counters are
producer CB19=node, CB20=tool, CB21=current card. Every node starts with a
real zero leaf store; every pair uses frozen022 on the original raw ROM.
Only the genuine card1/bit1 branch performs the matched double store. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (preparedSize mass loadRel storeRel setRel incrementRel)

def scanInitialize : List PackingOp := setRel 19 0

def scanBoundedTest (bound counter exit : Nat) : List PackingOp :=
  loadRel .value bound ++ loadRel .total counter ++
    [.base (.subtract .flag .value .total), .base (.base (.constant .index (5 * exit))),
     .jumpIfZero .flag .index]

def scanRowInitialize : List PackingOp :=
  loadRel .old 19 ++ [.base (.base (.constant .value 0))] ++ storeField .leaf ++
    cardProgram ++ storeRel .value 21 ++ setRel 20 0

def scanArguments : List PackingOp := loadRel .old 19 ++ loadRel .fresh 20

def scanScoreLead (skip : Nat) : List PackingOp :=
  loadRel .total 21 ++ [.base (.base (.constant .flag 1)), .base (.subtract .index .total .flag),
    .base (.subtract .flag .flag .total), .base (.base (.add .flag .flag .index)),
    .base (.base (.constant .index 0)), .base (.base (.select .value .flag .index .value)),
    .base (.base (.constant .index (5 * skip)))]

def scanScore (skip : Nat) : List PackingOp := scanScoreLead skip ++ [.jumpIfZero .value .index]

def scanInnerTail (start : Nat) : List PackingOp := incrementRel 20 ++ jumpTo (start + 51)
def scanOuterTail (start : Nat) : List PackingOp := incrementRel 19 ++ jumpTo (start + 4)

def leafToolProgramAt (start : Nat) : List PackingOp :=
  scanInitialize ++ scanBoundedTest 2 19 (start + 191) ++ scanRowInitialize ++
    scanBoundedTest 1 20 (start + 180) ++ scanArguments ++
    PA06A19PrepareBankNodeBit022.programAt (start + 66) ++ scanScore (start + 169) ++
    recordSingleton ++ scanInnerTail start ++ scanOuterTail start

theorem leafToolProgramAt_length (start : Nat) : (leafToolProgramAt start).length = 191 := rfl

theorem scanScore_value (rom : PhysicalROM) (CB card skip : Nat) (state : NatState)
    (hCB : state.register .address = CB) (hcard : state.heap (CB + 21) = card) :
    (runOps rom (scanScore skip) state).register .value =
      if card = 1 then state.register .value else 0 := by
  simp [scanScore, scanScoreLead, loadRel, runOps, natExecuteOp,
    Op.execute, Instruction.execute, hCB, hcard]; split_ifs <;> omega

theorem scanScore_pc (rom : PhysicalROM) (CB card skip : Nat) (state : NatState)
    (hCB : state.register .address = CB) (hcard : state.heap (CB + 21) = card) :
    (runOps rom (scanScore skip) state).pc =
      if card = 1 ∧ state.register .value ≠ 0 then state.pc + 55 else 5 * skip := by
  simp [scanScore, scanScoreLead, loadRel, runOps, natExecuteOp,
    Op.execute, Instruction.execute, hCB, hcard]; split_ifs <;> omega

inductive ScanChunk where
  | initialize | outerTest | rowInitialize | innerTest | arguments | score | matched | innerTail | outerTail
  deriving DecidableEq

def scanChunkCode (start : Nat) : ScanChunk → List PackingOp
  | .initialize => scanInitialize
  | .outerTest => scanBoundedTest 2 19 (start + 191)
  | .rowInitialize => scanRowInitialize
  | .innerTest => scanBoundedTest 1 20 (start + 180)
  | .arguments => scanArguments
  | .score => scanScore (start + 169)
  | .matched => recordSingleton
  | .innerTail => scanInnerTail start
  | .outerTail => scanOuterTail start

def scanChunkOffset : ScanChunk → Nat
  | .initialize => 0 | .outerTest => 4 | .rowInitialize => 13 | .innerTest => 51
  | .arguments => 60 | .score => 112 | .matched => 123 | .innerTail => 169 | .outerTail => 180

def scanChunkLength : ScanChunk → Nat
  | .initialize => 4 | .outerTest => 9 | .rowInitialize => 38 | .innerTest => 9
  | .arguments => 6 | .score => 11 | .matched => 46 | .innerTail => 11 | .outerTail => 11

def scanPaddingOp : PackingOp := .base (.base (.constant .value 0))
def scanChunkLead (start : Nat) (chunk : ScanChunk) : List PackingOp :=
  (scanChunkCode start chunk).take (scanChunkLength chunk - 1)
def scanChunkLast (start : Nat) (chunk : ScanChunk) : PackingOp :=
  (scanChunkCode start chunk).getD (scanChunkLength chunk - 1) scanPaddingOp

theorem scan_chunk_length (start : Nat) (chunk : ScanChunk) :
    (scanChunkCode start chunk).length = scanChunkLength chunk := by cases chunk <;> rfl

theorem scan_chunk_span (chunk : ScanChunk) : scanChunkOffset chunk + scanChunkLength chunk ≤ 191 := by
  cases chunk <;> decide

theorem scan_chunk_lead_length (start : Nat) (chunk : ScanChunk) :
    (scanChunkLead start chunk).length + 1 = scanChunkLength chunk := by cases chunk <;> rfl

theorem scan_chunk_split (start : Nat) (chunk : ScanChunk) :
    scanChunkCode start chunk = scanChunkLead start chunk ++ [scanChunkLast start chunk] := by cases chunk <;> rfl

theorem scan_chunk_slice (start : Nat) (chunk : ScanChunk) (position : Nat) (hp : position < scanChunkLength chunk) :
    (leafToolProgramAt start).getD (scanChunkOffset chunk + position) scanPaddingOp =
      (scanChunkCode start chunk).getD position scanPaddingOp := by
  cases chunk <;> dsimp only [scanChunkLength] at hp <;> interval_cases position <;> rfl

theorem scan_chunk_lead_noJump (start : Nat) (chunk : ScanChunk) :
    ∀ op ∈ scanChunkLead start chunk, NoJump op := by
  cases chunk <;>
    simp [scanChunkLead, scanChunkCode, scanChunkLength, scanInitialize, scanBoundedTest,
      scanRowInitialize, scanArguments, scanScore, scanScoreLead, recordSingleton,
      scanInnerTail, scanOuterTail, loadRel, storeRel, setRel, incrementRel, jumpTo,
      storeField, fieldPointer, fieldPointerLead, fieldPointerExtra, cardProgram, NoJump]

def LeafToolCodeAt (containing : List PackingOp) (start : Nat) : Prop :=
  start + 191 ≤ containing.length ∧ ∀ position < 191,
    containing.getD (start + position) scanPaddingOp = (leafToolProgramAt start).getD position scanPaddingOp

theorem leafTool_append_code (left right : List PackingOp) :
    LeafToolCodeAt (left ++ leafToolProgramAt left.length ++ right) left.length := by
  constructor
  · simp only [List.length_append, leafToolProgramAt_length]
    omega
  · intro position hp
    rw [List.getD_append (left ++ leafToolProgramAt left.length) right scanPaddingOp _
      (by simp only [List.length_append, leafToolProgramAt_length]; omega),
      List.getD_append_right left (leafToolProgramAt left.length) scanPaddingOp _ (by omega),
      Nat.add_sub_cancel_left]

theorem scan_chunk_run_prefix (rom : PhysicalROM) (containing : List PackingOp) (start : Nat)
    (code : LeafToolCodeAt containing start) (chunk : ScanChunk) (state : NatState)
    (hpc : state.pc = 5 * (start + scanChunkOffset chunk)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ scanChunkLength chunk) :
    natRun rom containing count state = runOps rom ((scanChunkCode start chunk).take count) state := by
  rw [scan_chunk_split start chunk]
  refine natRun_segment_prefix rom containing (scanChunkLead start chunk) (scanChunkLast start chunk)
    (start + scanChunkOffset chunk)
    (by have hs := scan_chunk_span chunk; have hl := scan_chunk_lead_length start chunk; have hb := code.1; omega)
    ?_ ?_ (scan_chunk_lead_noJump start chunk) state hpc ha count
    (by have hl := scan_chunk_lead_length start chunk; omega)
  · intro position hp
    have hlen := scan_chunk_lead_length start chunk
    have hpos : position < scanChunkLength chunk := by omega
    have hh := (code.2 (scanChunkOffset chunk + position) (by have hs := scan_chunk_span chunk; omega)).trans
      (scan_chunk_slice start chunk position hpos)
    rw [List.getD_eq_getElem _ _ (by have hs := scan_chunk_span chunk; have hb := code.1; omega),
      List.getD_eq_getElem _ _ (by rw [scan_chunk_length]; exact hpos)] at hh
    simpa only [Nat.add_assoc, scanChunkLead, List.getElem_take] using hh
  · have hlen := scan_chunk_lead_length start chunk
    have hpos : (scanChunkLead start chunk).length < scanChunkLength chunk := by omega
    have hh := (code.2 (scanChunkOffset chunk + (scanChunkLead start chunk).length)
      (by have hs := scan_chunk_span chunk; omega)).trans (scan_chunk_slice start chunk _ hpos)
    rw [List.getD_eq_getElem _ _ (by have hs := scan_chunk_span chunk; have hb := code.1; omega)] at hh
    have heq : (scanChunkLead start chunk).length = scanChunkLength chunk - 1 := by omega
    simpa only [Nat.add_assoc, heq, scanChunkLast] using hh

theorem scan_chunk_run (rom : PhysicalROM) (containing : List PackingOp) (start : Nat)
    (code : LeafToolCodeAt containing start) (chunk : ScanChunk) (state : NatState)
    (hpc : state.pc = 5 * (start + scanChunkOffset chunk)) (ha : state.halted = false) :
    natRun rom containing (scanChunkLength chunk) state = runOps rom (scanChunkCode start chunk) state := by
  rw [scan_chunk_run_prefix rom containing start code chunk state hpc ha _ le_rfl,
    List.take_of_length_le (by rw [scan_chunk_length])]

theorem scan_query_code (containing : List PackingOp) (start : Nat) (code : LeafToolCodeAt containing start) :
    ScanQueryCodeAt containing (start + 66) := by
  constructor
  · have h := code.1
    omega
  · intro position hp
    have h := code.2 (66 + position) (by omega)
    have hs : (leafToolProgramAt start).getD (66 + position) scanPaddingOp =
        (PA06A19PrepareBankNodeBit022.programAt (start + 66)).getD position scanPaddingOp := by
      interval_cases position <;> rfl
    have he : start + (66 + position) = start + 66 + position := by omega
    rw [he] at h
    exact h.trans hs

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
