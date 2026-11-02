module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeRead_007a
public import PaperProofs.Structure.PSTR_HD_StaticFieldsSafety_023
public import PaperProofs.Structure.PA17_QueryBudget_015
public import PaperProofs.Structure.PA17_A19QueryBridge_Numeric_006b
import Mathlib.Tactic.IntervalCases

/-! One fixed straight Word header block. The current stage is read from
the ORIGINAL persistent stage word, never from a new input/ROM field.
The stage=N lookahead is exactly the first original toolNodes word;
positive q makes this a valid read, and a real select discards its value.
All four header words are actually stored; incoming scratch/registers are
arbitrary. Only the original metadata and raw N/q are read. -/

@[expose] public section
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeHeader011

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PSTRStaticLayout PSTRStaticHeap

def readStage : List PackingOp :=
  [.base (.base (.constant .address 2)),
   .base (.base (.loadHeap .total .address)),
   .base (.base (.constant .flag 4)),
   .base (.base (.add .address .total .flag)),
   .base (.base (.loadHeap .index .address))]

def prepareRow : List PackingOp :=
  [.base (.base (.constant .address 0)),
   .base (.base (.loadROM .input .total .address)),
   .base (.subtract .flag .total .index),
   .base (.base (.constant .total 0)),
   .base (.base (.constant .fresh 1)),
   .base (.base (.select .fresh .flag .fresh .total)),
   .base (.base (.select .value .fresh .value .total)),
   .base (.base (.add .old .index .fresh)),
   .base (.base (.constant .address 1)),
   .base (.base (.loadROM .input .flag .address)),
   .base (.base (.constant .address 2)),
   .base (.base (.add .flag .flag .address)),
   .arithmetic .multiply .old .old .flag,
   .base (.base (.constant .address 0)),
   .base (.base (.loadHeap .flag .address)),
   .base (.base (.constant .address 1)),
   .base (.base (.add .flag .flag .address)),
   .arithmetic .multiply .old .old .flag,
   .base (.base (.select .old .fresh .old .total))]

def locate : List PackingOp := PSTRCountWorkspace.program ++ PA17A19RuntimeRead007.headerFinish

def writeHeader : List PackingOp :=
  [.base (.base (.storeHeap .address .old)),
   .base (.base (.constant .flag 1)),
   .base (.base (.add .address .address .flag)),
   .base (.base (.storeHeap .address .value)),
   .base (.base (.add .address .address .flag)),
   .base (.base (.storeHeap .address .fresh)),
   .base (.base (.add .address .address .flag)),
   .base (.base (.storeHeap .address .index)),
   .base (.base (.constant .flag 3)),
   .base (.subtract .address .address .flag)]

def program : List PackingOp :=
  readStage ++ PSTRStaticFields.program ⟨7, by decide⟩ ++ prepareRow ++ locate ++ writeHeader

theorem readStage_length : readStage.length = 5 := rfl
theorem prepareRow_length : prepareRow.length = 19 := rfl
theorem locate_length : locate.length = 26 := rfl
theorem writeHeader_length : writeHeader.length = 10 := rfl
theorem program_length : program.length = 82 := rfl

theorem readStage_straight : StraightProgram readStage := by simp [readStage, StraightProgram, StraightOp]
theorem prepareRow_straight : StraightProgram prepareRow := by simp [prepareRow, StraightProgram, StraightOp]
theorem locate_straight : StraightProgram locate := by
  intro op ho
  rcases List.mem_append.mp ho with ho | ho
  · exact PSTRCountWorkspace.program_straight op ho
  · exact PA17A19RuntimeRead007.headerFinish_straight op ho
theorem writeHeader_straight : StraightProgram writeHeader := by simp [writeHeader, StraightProgram, StraightOp]
theorem program_straight : StraightProgram program := by
  intro op ho
  simp only [program, List.mem_append] at ho
  rcases ho with (((ho | ho) | ho) | ho) | ho
  · exact readStage_straight op ho
  · exact PSTRStaticFields.program_straight _ op ho
  · exact prepareRow_straight op ho
  · exact locate_straight op ho
  · exact writeHeader_straight op ho

theorem code_fit {bits : Nat} (hb : 9 ≤ bits) : WordsFit bits (packingCode program) := by
  have hpow : 512 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb
  intro value hv
  have hs : value < 512 := by
    simp [packingCode, program, readStage, PSTRStaticFields.program, prepareRow,
      locate, PSTRCountWorkspace.program, PA17A19RuntimeRead007.headerFinish, writeHeader,
      PSTRStaticFields.treeFactor, PSTRStaticFields.edgeFactor,
      PSTRStaticFields.fixedOffset, PSTRStaticFields.stageFactor,
      PackingOp.encode, Op.encodeWords, Instruction.encodeWords,
      PackingPrimitive.word, Register.word, Region.word, haltWords] at hv
    omega
  exact hs.trans_le hpow

theorem pc_fit {bits : Nat} (hb : 9 ≤ bits) : Fits bits (5 * program.length) := by
  have hpow : 512 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb
  change 410 < 2 ^ bits
  omega

theorem execute_readStage {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap) :
    (executeOps (callInput q full command) readStage state).register .index =
      BitVec.ofNat bits configuration.stage ∧
    (executeOps (callInput q full command) readStage state).heap = state.heap := by
  have hh := (headers full configuration capWords state.heap rep).2.2.1
  have hs := (stage_failed full configuration capWords state.heap hq rep).1
  simp +decide [readStage, executeOps, packingExecuteOp, wordOp, wordInstruction,
    hh, BitVec.ofNat_add_ofNat, Nat.add_comm]
  simpa only [physicalHeaderWords] using hs

/-- The terminal lookahead is within ORIGINAL metadata because field8 has q
words and q is positive. No hypothetical sentinel or cached answer is used. -/
theorem stage_address_in_bounds {q : Nat} (full : List (Finset (Fin q)))
    (hq : 0 < q) (stage : Nat) (hs : stage ≤ full.length) :
    offset q full 7 + stage < (staticMetadata q full).length := by
  rw [metadata_length q full hq]
  simp only [offset]
  omega

theorem stage_address_terminal {q : Nat} (full : List (Finset (Fin q))) :
    offset q full 7 + full.length = offset q full 8 := rfl

/-- Address formation of the EXISTING fixed field7 getter. This lemma also
covers the legal terminal lookahead; it does not assume a field7 value. -/
theorem execute_stage_address {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (position : Nat) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hi : state.register .index = BitVec.ofNat bits position) :
    let result := executeOps (callInput q full command) (PSTRStaticFields.program ⟨7, by decide⟩) state
    result.register .address = BitVec.ofNat bits (metadataAddress q capWords bits (offset q full 7 + position)) ∧
    result.register .index = state.register .index ∧ result.heap = state.heap := by
  have hpow : 256 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb
  have ht : (state.heap (BitVec.ofNat bits 0)).toNat = (prepareNormalization q full).indexed.nodes.size := by
    simpa only [treeSize, ne_of_gt hq, ite_false] using rep.1
  have hpacked := (headers full configuration capWords state.heap rep).2.2.1
  have hen := chunk_toNat full configuration capWords state.heap hq rep 0 0 (by decide) (by simp [chunks])
  have he : (state.heap (BitVec.ofNat bits (packedCapacityWords q capWords bits + 6))).toNat =
      edgeCount q full := by
    have haddr : metadataAddress q capWords bits (offset q full 0 + 0) = packedCapacityWords q capWords bits + 6 := by
      simp only [metadataAddress, physicalHeaderWords, offset]
      omega
    rw [haddr] at hen
    exact hen
  have hc (n : Nat) (hn : n ≤ 6) : (BitVec.ofNat bits n).toNat = n :=
    Nat.mod_eq_of_lt (by omega)
  dsimp only
  simp +decide only [PSTRStaticFields.program, PSTRStaticFields.treeFactor,
    PSTRStaticFields.edgeFactor, PSTRStaticFields.fixedOffset, PSTRStaticFields.stageFactor,
    executeOps, packingExecuteOp, wordOp, wordInstruction, packingArithmetic,
    Function.update_apply, ↓reduceIte, hpacked, hi, ht, hc 5 (by omega),
    hc 1 (by omega), hc 0 (by omega), BitVec.ofNat_add_ofNat, and_true]
  congr 1
  simp only [metadataAddress, physicalHeaderWords, offset]
  rw [he]
  ring

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeHeader011

