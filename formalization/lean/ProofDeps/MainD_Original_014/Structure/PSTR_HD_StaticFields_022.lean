module

public import Structure.PSTR_HD_StaticRead_021
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-! Fixed field readers establish the metadata offset with real arithmetic.
The field class is one of nine fixed call sites, never task data. Tree size,
packed size and edge count are read from the ORIGINAL persistent heap; N is
read from the ORIGINAL raw callInput. No leafBitmap/tree ROM is supplied. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PSTRStaticFields

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine PSTRStaticLayout PSTRStaticHeap

def treeFactor (field : Fin 9) : Nat := match field.val with
  | 0 | 1 => 0 | 2 => 1 | 3 | 4 => 2 | 5 => 3 | 6 => 4 | _ => 5
def edgeFactor (field : Fin 9) : Nat := if 4 ≤ field.val then 1 else 0
def stageFactor (field : Fin 9) : Nat := if field.val = 8 then 1 else 0
def fixedOffset (field : Fin 9) : Nat := if field.val = 0 then 0 else 1

theorem coefficient_bounds (field : Fin 9) :
    treeFactor field ≤ 5 ∧ edgeFactor field ≤ 1 ∧ stageFactor field ≤ 1 ∧ fixedOffset field ≤ 1 := by
  rcases field with ⟨field, hf⟩
  interval_cases field <;> simp [treeFactor, edgeFactor, stageFactor, fixedOffset]

theorem offset_formula (q : Nat) (full : List (Finset (Fin q))) (field : Fin 9) :
    offset q full field.val = fixedOffset field + treeFactor field * (prepareNormalization q full).indexed.nodes.size +
      edgeFactor field * edgeCount q full + stageFactor field * full.length := by
  rcases field with ⟨field, hf⟩
  interval_cases field <;>
    simp [offset, treeFactor, edgeFactor, stageFactor, fixedOffset,
      Nat.add_assoc, Nat.add_comm]

def program (field : Fin 9) : List PackingOp :=
  [.base (.base (.constant .address 0)),
   .base (.base (.loadHeap .fresh .address)),
   .base (.base (.constant .address 2)),
   .base (.base (.loadHeap .total .address)),
   .base (.base (.constant .old 6)),
   .base (.base (.add .address .total .old)),
   .base (.base (.loadHeap .old .address)),
   .base (.base (.constant .flag (treeFactor field))),
   .arithmetic .multiply .fresh .fresh .flag,
   .base (.base (.constant .value (edgeFactor field))),
   .arithmetic .multiply .old .old .value,
   .base (.base (.add .address .address .fresh)),
   .base (.base (.add .address .address .old)),
   .base (.base (.constant .value (fixedOffset field))),
   .base (.base (.add .address .address .value)),
   .base (.base (.add .address .address .index)),
   .base (.base (.constant .value 0)),
   .base (.base (.loadROM .input .value .value)),
   .base (.base (.constant .flag (stageFactor field))),
   .arithmetic .multiply .value .value .flag,
   .base (.base (.add .address .address .value)),
   .base (.base (.loadHeap .value .address))]

theorem program_length (field : Fin 9) : (program field).length = 22 := rfl

theorem program_straight (field : Fin 9) : StraightProgram (program field) := by
  simp [program, StraightProgram, StraightOp]

theorem code_fit {bits : Nat} (field : Fin 9) (hb : 8 ≤ bits) : WordsFit bits (packingCode (program field)) := by
  have hpow : 256 ≤ 2 ^ bits := (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  have hc := coefficient_bounds field
  intro value hv
  have hs : value < 256 := by
    simp [packingCode, program, PackingOp.encode, Op.encodeWords, Instruction.encodeWords,
      PackingPrimitive.word, Register.word, Region.word, haltWords] at hv
    omega
  exact hs.trans_le hpow

theorem pc_fit {bits : Nat} (field : Fin 9) (hb : 8 ≤ bits) : Fits bits (5 * (program field).length) := by
  have hpow : 256 ≤ 2 ^ bits := (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  change 110 < 2 ^ bits
  omega

theorem execute_field {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (field : Fin 9) (position : Nat) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hN : Fits bits full.length)
    (hp : position < (chunks q full hq)[field.val].length)
    (hi : state.register .index = BitVec.ofNat bits position) :
    let result := executeOps (callInput q full command) (program field) state
    result.register .value = BitVec.ofNat bits (chunks q full hq)[field.val][position] ∧
    result.register .address = BitVec.ofNat bits (metadataAddress q capWords bits (offset q full field.val + position)) ∧
    result.register .index = state.register .index ∧ result.heap = state.heap := by
  have hpow : 256 ≤ 2 ^ bits := (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  have coeff (value : Nat) (hv : value ≤ 5) : (BitVec.ofNat bits value).toNat = value := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hc := coefficient_bounds field
  have htree := (headers full configuration capWords state.heap rep).1
  have htree' : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits (prepareNormalization q full).indexed.nodes.size := by
    simpa only [treeSize, ne_of_gt hq, ite_false] using htree
  have ht : (BitVec.ofNat bits (prepareNormalization q full).indexed.nodes.size).toNat =
      (prepareNormalization q full).indexed.nodes.size := by
    rw [← htree']
    simpa only [treeSize, ne_of_gt hq, ite_false] using rep.1
  have hpacked := (headers full configuration capWords state.heap rep).2.2.1
  have hedge := child_count_word full configuration capWords state.heap hq rep
  have hen := chunk_toNat full configuration capWords state.heap hq rep 0 0 (by decide) (by simp [chunks])
  have he : (BitVec.ofNat bits (edgeCount q full)).toNat = edgeCount q full := by
    rw [← hedge]
    simpa [chunks, offset] using hen
  have hbase : BitVec.ofNat bits (packedCapacityWords q capWords bits) + BitVec.ofNat bits 6 =
      BitVec.ofNat bits (metadataAddress q capWords bits 0) := by
    rw [BitVec.ofNat_add_ofNat]
    congr 1
    unfold metadataAddress physicalHeaderWords
    omega
  have hedge' : state.heap (BitVec.ofNat bits (packedCapacityWords q capWords bits) + BitVec.ofNat bits 6) =
      BitVec.ofNat bits (edgeCount q full) := by rw [hbase]; exact hedge
  have hraw : ((callInput q full command).words .input).getD 0 0 = full.length := rfl
  have hn : (BitVec.ofNat bits full.length).toNat = full.length := Nat.mod_eq_of_lt hN
  have h0 : (BitVec.ofNat bits 0).toNat = 0 := by simp
  have ha : BitVec.ofNat bits (packedCapacityWords q capWords bits) + BitVec.ofNat bits 6 +
      BitVec.ofNat bits ((prepareNormalization q full).indexed.nodes.size * treeFactor field) +
      BitVec.ofNat bits (edgeCount q full * edgeFactor field) + BitVec.ofNat bits (fixedOffset field) +
      BitVec.ofNat bits position + BitVec.ofNat bits (full.length * stageFactor field) =
        BitVec.ofNat bits (metadataAddress q capWords bits (offset q full field.val + position)) := by
    simp only [BitVec.ofNat_add_ofNat]
    congr 1
    rw [offset_formula]
    unfold metadataAddress physicalHeaderWords
    ring
  have hv := metadata_word full configuration capWords state.heap hq rep _
    (chunk_in_bounds q full hq field.val position field.isLt hp)
  have hget := metadata_chunk_getD q full hq field.val position field.isLt hp
  rw [List.getD_eq_getElem _ _ (chunk_in_bounds q full hq field.val position field.isLt hp)] at hget
  rw [hget] at hv
  simp +decide only [program, executeOps, packingExecuteOp, wordOp, wordInstruction,
    packingArithmetic, Function.update_apply, ↓reduceIte, htree', hpacked, hedge', hi,
    ht, he, hn, h0, hraw, coeff _ hc.1, coeff _ (hc.2.1.trans (by decide)),
    coeff _ (hc.2.2.1.trans (by decide)), ha, hv]
  exact ⟨rfl, True.intro⟩

end PaperProofs.Structure.LaminarTree.PSTRStaticFields
