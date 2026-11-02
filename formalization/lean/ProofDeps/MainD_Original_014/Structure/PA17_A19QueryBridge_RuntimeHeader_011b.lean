module

public import Structure.PA17_A19QueryBridge_RuntimeHeader_011a

@[expose] public section
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeHeader011

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PSTRStaticLayout PSTRStaticHeap

theorem execute_prepareRow {bits : Nat} (rom : PhysicalROM) (N q size stage : Nat)
    (state : WordState bits) (hb : 8 ≤ bits)
    (hN : Fits bits N) (hs : stage ≤ N)
    (hq : Fits bits (q + 2)) (ht : Fits bits (size + 1))
    (hr : Fits bits ((stage + 1) * (q + 2)))
    (hin0 : (rom.words .input).getD 0 0 = N)
    (hin1 : (rom.words .input).getD 1 0 = q)
    (hh : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hi : state.register .index = BitVec.ofNat bits stage) :
    let after := executeOps rom prepareRow state
    after.register .old = BitVec.ofNat bits (PA17QueryHeader009.rowPointer N q size stage) ∧
    after.register .fresh = BitVec.ofNat bits (PA17QueryHeader009.active N stage) ∧
    after.register .value = (if stage < N then state.register .value else BitVec.ofNat bits 0) ∧
    after.register .index = state.register .index ∧ after.heap = state.heap := by
  have hpow : 256 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb
  have hc (n : Nat) (hn : n ≤ 3) : (BitVec.ofNat bits n).toNat = n := Nat.mod_eq_of_lt (by omega)
  have hsf : Fits bits stage := hs.trans_lt hN
  have hd : Fits bits (N - stage) := (Nat.sub_le N stage).trans_lt hN
  have hsq : Fits bits (stage + 1) := by
    have hm : stage + 1 ≤ (stage + 1) * (q + 2) := Nat.le_mul_of_pos_right _ (by omega)
    exact hm.trans_lt hr
  have hnz : ((BitVec.ofNat bits (N - stage)).toNat = 0) ↔ ¬stage < N := by
    rw [show (BitVec.ofNat bits (N - stage)).toNat = N - stage from Nat.mod_eq_of_lt hd]
    omega
  have hraw0 : (rom.words .input)[0]?.getD 0 = N := hin0
  have hraw1 : (rom.words .input)[1]?.getD 0 = q := hin1
  have hhword : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size := by
    rw [← hh]
    simp
  by_cases ha : stage < N
  · simp +decide [prepareRow, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingArithmetic, hi, hc, hraw0, hraw1, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hN, Nat.mod_eq_of_lt hsf, Nat.mod_eq_of_lt hd,
      Nat.mod_eq_of_lt hsq, Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt ht,
      Nat.mod_eq_of_lt hr, BitVec.ofNat_add_ofNat, hhword,
      show N - stage ≠ 0 by omega, PA17QueryHeader009.rowPointer,
      PA17QueryHeader009.active, PA17QueryHeader009.stride, ha, Nat.mul_comm, Nat.mul_left_comm]
  · have he : stage = N := by omega
    subst stage
    simp +decide [prepareRow, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingArithmetic, hi, hc, hraw0, hraw1, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hN, BitVec.ofNat_add_ofNat,
      PA17QueryHeader009.rowPointer, PA17QueryHeader009.active]

theorem finish_payload {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    let after := executeOps rom PA17A19RuntimeRead007.headerFinish state
    after.register .old = state.register .old ∧ after.register .fresh = state.register .fresh ∧
    after.register .value = state.register .value ∧ after.register .index = state.register .index ∧
    after.heap = state.heap := by
  simp +decide [PA17A19RuntimeRead007.headerFinish, executeOps, packingExecuteOp, wordOp, wordInstruction]

theorem execute_locate {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap) :
    let after := executeOps (callInput q full command) locate state
    after.register .address = BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)) ∧
    after.register .old = state.register .old ∧
    after.register .fresh = state.register .fresh ∧
    after.register .value = state.register .value ∧
    after.register .index = state.register .index ∧ after.heap = state.heap := by
  let located := executeOps (callInput q full command) PSTRCountWorkspace.program state
  have hl := PSTRCountWorkspace.execute_base full command configuration capWords state hb hq rep
  have ha := PA17A19RuntimeRead007.headerFinish_address (callInput q full command)
    (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) located hb
    (by rw [hl.2.2.2.2.2.1]; exact rep.1)
    (hl.1.trans (congrArg (BitVec.ofNat bits) (PSTRCountWorkspace.base_metadata_end q full hq capWords bits)))
  have hf := finish_payload (callInput q full command) located
  dsimp only
  rw [locate, executeOps_append]
  exact ⟨ha, hf.1.trans hl.2.2.2.1, hf.2.1.trans hl.2.2.2.2.1,
    hf.2.2.1.trans hl.2.1, hf.2.2.2.1.trans hl.2.2.1,
    hf.2.2.2.2.trans hl.2.2.2.2.2.1⟩

def storedHeap {bits : Nat} (heap : BitVec bits → BitVec bits) (header : Nat)
    (row node active stage : BitVec bits) : BitVec bits → BitVec bits :=
  Function.update (Function.update (Function.update (Function.update heap
    (BitVec.ofNat bits header) row) (BitVec.ofNat bits (header + 1)) node)
      (BitVec.ofNat bits (header + 2)) active) (BitVec.ofNat bits (header + 3)) stage

theorem execute_writeHeader {bits : Nat} (rom : PhysicalROM) (header : Nat)
    (state : WordState bits) (hb : 8 ≤ bits) (hf : Fits bits (header + 3))
    (ha : state.register .address = BitVec.ofNat bits header) :
    let after := executeOps rom writeHeader state
    after.register .address = BitVec.ofNat bits header ∧
    after.heap = storedHeap state.heap header (state.register .old) (state.register .value)
      (state.register .fresh) (state.register .index) := by
  have hpow : 256 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb
  have hc (n : Nat) (hn : n ≤ 3) : (BitVec.ofNat bits n).toNat = n := Nat.mod_eq_of_lt (by omega)
  simp +decide [writeHeader, storedHeap, executeOps, packingExecuteOp, wordOp, wordInstruction,
    ha, BitVec.ofNat_add_ofNat, Nat.add_assoc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf,
    hc, show header + 3 - 3 = header by omega]

theorem execute_node {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (stage : Fin (full.length + 1)) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hN : Fits bits full.length)
    (hi : state.register .index = BitVec.ofNat bits stage.val) :
    (if stage.val < full.length then
      (executeOps (callInput q full command) (PSTRStaticFields.program ⟨7, by decide⟩) state).register .value
      else BitVec.ofNat bits 0) =
      BitVec.ofNat bits (encodedNode (prepareNormalization q full).indexed
        (PA17QueryBudget015.node full hq stage)) := by
  by_cases hs : stage.val < full.length
  · have hf := (PSTRStaticFields.execute_field full command configuration capWords state
      ⟨7, by decide⟩ stage.val hb hq rep hN (by simp [chunks]; exact hs) hi).1
    simp only [hs, ↓reduceIte]
    rw [hf]
    change BitVec.ofNat bits (((List.finRange full.length).map
      (fun other => encodedNode (prepareNormalization q full).indexed
        ((IndexedStaticMetadata.buildPositive q full hq).stageNodes.get other)))[stage.val]'(by simp; exact hs)) = _
    rw [mapped_finRange_get _ ⟨stage.val, hs⟩]
    simp only [PA17QueryBudget015.node, hs, dite_true, IndexedQuery.storedStageNode]
  · simp [PA17QueryBudget015.node, hs, encodedNode]

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeHeader011

