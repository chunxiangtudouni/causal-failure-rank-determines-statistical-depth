module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_010b

/-! Local Word execution of the fixed tests control and address primitives.
The scalar value/register at a reader return is consumed as returned; no
incidence, flag, rank or capacity-answer ROM is introduced. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM

theorem slots_eq_iff {bits : Nat} (header left right : Nat)
    (hf : Fits bits (header + 16)) (hl : left ≤ 16) (hr : right ≤ 16) :
    BitVec.ofNat bits (header + left) = BitVec.ofNat bits (header + right) ↔ left = right := by
  rw [ofNat_injective_of_fit _ _ ((show header + left ≤ header + 16 by omega).trans_lt hf)
    ((show header + right ≤ header + 16 by omega).trans_lt hf)]
  omega

theorem slot_ne_zero {bits : Nat} (header offset : Nat)
    (hf : Fits bits (header + 16)) (ho : 0 < offset) (hl : offset ≤ 16) :
    BitVec.ofNat bits (header + offset) ≠ BitVec.ofNat bits 0 := by
  intro heq
  have he := (ofNat_injective_of_fit _ _ ((show header + offset ≤ header + 16 by omega).trans_lt hf)
    (by unfold Fits at *; omega)).mp heq
  omega

theorem execute_counterTest {bits : Nat} (rom : PhysicalROM)
    (slot target header remaining : Nat) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hr : state.heap (BitVec.ofNat bits (header + slot)) = BitVec.ofNat bits remaining)
    (hf : Fits bits remaining) :
    let after := executeOps rom (counterTest slot target) state
    after.register .total = BitVec.ofNat bits remaining ∧
      after.register .address = BitVec.ofNat bits header ∧ after.heap = state.heap ∧
      after.pc = (if remaining = 0 then BitVec.ofNat bits target else state.pc + BitVec.ofNat bits 25) := by
  simp +decide [counterTest, counterLead, loadSlot, executeOps,
    packingExecuteOp, wordOp, wordInstruction, hh, hr, BitVec.ofNat_add_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf, BitVec.add_assoc]

theorem execute_back {bits : Nat} (rom : PhysicalROM) (target : Nat) (state : WordState bits) :
    let after := executeOps rom (back target) state
    after.pc = BitVec.ofNat bits target ∧ after.heap = state.heap ∧
      after.register .address = state.register .address := by
  simp +decide [back, backLead, executeOps, packingExecuteOp, wordOp, wordInstruction]

theorem execute_setup {bits : Nat} (rom : PhysicalROM) (header q : Nat) (state : WordState bits)
    (h1 : Fits bits 1) (hq : (rom.words .input).getD 1 0 = q)
    (hh : state.register .address = BitVec.ofNat bits header) :
    let after := executeOps rom setup state
    after.heap = Function.update state.heap (BitVec.ofNat bits (header + 8)) (BitVec.ofNat bits (q + 2)) ∧
      after.register .address = BitVec.ofNat bits header := by
  change (rom.words .input)[1]?.getD 0 = q at hq
  simp +decide [setup, storeSlot, executeOps, packingExecuteOp, wordOp,
    wordInstruction, hh, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, hq, BitVec.ofNat_add_ofNat]

theorem execute_countsLocator {bits : Nat} (rom : PhysicalROM) (workspace size : Nat)
    (state : WordState bits) (hb : 2 ≤ bits)
    (hroom : Fits bits (PSTRQueryLayout.header workspace size))
    (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hh : state.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size)) :
    let after := executeOps rom countsLocator state
    after.register .total = BitVec.ofNat bits (PSTRQueryLayout.countsBase workspace) ∧
      after.register .old = BitVec.ofNat bits 1 ∧
      after.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size) ∧
      after.register .value = state.register .value ∧ after.heap = state.heap := by
  have hsmall : 2 < 2 ^ bits := by
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb
    omega
  have hmul : Fits bits (size * 2 + 1) := by
    apply (show size * 2 + 1 ≤ PSTRQueryLayout.header workspace size from ?_).trans_lt hroom
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    omega
  have he : PSTRQueryLayout.header workspace size - (size * 2 + 1) = PSTRQueryLayout.countsBase workspace := by
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    omega
  simp +decide [countsLocator, executeOps, packingExecuteOp, wordOp, wordInstruction,
    packingArithmetic, hsize, hh, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hsmall, BitVec.ofNat_add_ofNat, Nat.mod_eq_of_lt hroom,
    Nat.mod_eq_of_lt hmul, he]

theorem execute_tagTail {bits : Nat} (rom : PhysicalROM) (header : Nat) (state : WordState bits)
    (hroom : Fits bits (header + 16)) (hh : state.register .address = BitVec.ofNat bits header) :
    let after := executeOps rom tagTail state
    let flag : BitVec bits := BitVec.ofNat bits (if (state.register .value).toNat = 0 then 0 else 1)
    after.heap = Function.update
      (Function.update state.heap (BitVec.ofNat bits (header + 10)) flag)
      (BitVec.ofNat bits (header + 9)) (state.heap (BitVec.ofNat bits 0)) ∧
      after.register .address = BitVec.ofNat bits header := by
  have hz : BitVec.ofNat bits 0 ≠ BitVec.ofNat bits (header + 10) :=
    (slot_ne_zero header 10 hroom (by decide) (by decide)).symm
  simp +decide [tagTail, storeSlot, executeOps, packingExecuteOp,
    wordOp, wordInstruction, hh, BitVec.ofNat_add_ofNat, hz]
  split_ifs <;> rfl

theorem execute_nodeReadSuffix {bits : Nat} (rom : PhysicalROM) (header countsBase node : Nat)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (hb : state.register .total = BitVec.ofNat bits countsBase)
    (hn : state.heap (BitVec.ofNat bits (header + 9)) = BitVec.ofNat bits node) :
    let after := executeOps rom nodeReadSuffix state
    after.register .old = state.heap (BitVec.ofNat bits (countsBase + node)) ∧
      after.register .value = state.register .value ∧
      after.register .address = BitVec.ofNat bits header ∧ after.heap = state.heap := by
  simp +decide [nodeReadSuffix, loadSlot, executeOps, packingExecuteOp,
    wordOp, wordInstruction, hh, hb, hn, BitVec.ofNat_add_ofNat]

theorem execute_ancestorReadSuffix {bits : Nat} (rom : PhysicalROM) (header countsBase encoded : Nat)
    (state : WordState bits) (h1 : Fits bits 1) (hf : Fits bits encoded)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hb : state.register .total = BitVec.ofNat bits countsBase)
    (ho : state.register .old = BitVec.ofNat bits 1)
    (hn : state.heap (BitVec.ofNat bits (header + 11)) = BitVec.ofNat bits encoded) :
    let after := executeOps rom ancestorReadSuffix state
    after.register .old = state.heap (BitVec.ofNat bits (countsBase + (encoded - 1))) ∧
      after.register .value = state.register .value ∧
      after.register .address = BitVec.ofNat bits header ∧ after.heap = state.heap := by
  simp +decide [ancestorReadSuffix, loadSlot, executeOps, packingExecuteOp,
    wordOp, wordInstruction, hh, hb, ho, hn, BitVec.ofNat_add_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hf]

theorem execute_nodeCountRead {bits : Nat} (rom : PhysicalROM) (workspace size node : Nat)
    (state : WordState bits) (hb : 2 ≤ bits)
    (hroom : Fits bits (PSTRQueryLayout.header workspace size))
    (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hh : state.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size))
    (hn : state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 9)) = BitVec.ofNat bits node) :
    let after := executeOps rom nodeCountRead state
    after.register .old = state.heap (BitVec.ofNat bits (PSTRQueryLayout.countsBase workspace + node)) ∧
      after.register .value = state.register .value ∧
      after.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size) ∧ after.heap = state.heap := by
  let located := executeOps rom countsLocator state
  have hl := execute_countsLocator rom workspace size state hb hroom hsize hh
  have hs := execute_nodeReadSuffix rom (PSTRQueryLayout.header workspace size)
    (PSTRQueryLayout.countsBase workspace) node located hl.2.2.1 hl.1
    (by rw [hl.2.2.2.2]; exact hn)
  simpa only [nodeCountRead, executeOps_append, located, hl.2.2.2.2, hl.2.2.2.1] using hs

theorem execute_ancestorCountRead {bits : Nat} (rom : PhysicalROM) (workspace size encoded : Nat)
    (state : WordState bits) (hb : 2 ≤ bits) (hf : Fits bits encoded)
    (hroom : Fits bits (PSTRQueryLayout.header workspace size))
    (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hh : state.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size))
    (hn : state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 11)) = BitVec.ofNat bits encoded) :
    let after := executeOps rom ancestorCountRead state
    after.register .old = state.heap (BitVec.ofNat bits (PSTRQueryLayout.countsBase workspace + (encoded - 1))) ∧
      after.register .value = state.register .value ∧
      after.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size) ∧ after.heap = state.heap := by
  let located := executeOps rom countsLocator state
  have h1 : Fits bits 1 := (show 1 ≤ PSTRQueryLayout.header workspace size from by
    unfold PSTRQueryLayout.header; omega).trans_lt hroom
  have hl := execute_countsLocator rom workspace size state hb hroom hsize hh
  have hs := execute_ancestorReadSuffix rom (PSTRQueryLayout.header workspace size)
    (PSTRQueryLayout.countsBase workspace) encoded located h1 hf hl.2.2.1 hl.1 hl.2.1
    (by rw [hl.2.2.2.2]; exact hn)
  simpa only [ancestorCountRead, executeOps_append, located, hl.2.2.2.2, hl.2.2.2.1] using hs

theorem execute_nodeLead {bits : Nat} (rom : PhysicalROM) (header remaining entryBase : Nat)
    (state : WordState bits) (hroom : Fits bits (header + 16))
    (hr : Fits bits (remaining + 1)) (hh : state.register .address = BitVec.ofNat bits header)
    (hc : state.register .total = BitVec.ofNat bits (remaining + 1))
    (he : state.heap (BitVec.ofNat bits (header + 13)) = BitVec.ofNat bits entryBase) :
    let after := executeOps rom nodeLead state
    after.heap = Function.update state.heap (BitVec.ofNat bits (header + 9)) (BitVec.ofNat bits remaining) ∧
      after.register .value = BitVec.ofNat bits (entryBase + 1 + remaining) ∧
      after.register .address = BitVec.ofNat bits header := by
  have h1 : Fits bits 1 := (show 1 ≤ header + 16 by omega).trans_lt hroom
  have hne : BitVec.ofNat bits (header + 13) ≠ BitVec.ofNat bits (header + 9) := by
    intro heq
    have heq' := (slots_eq_iff header 13 9 hroom (by decide) (by decide)).mp heq
    omega
  simp +decide [nodeLead, loadSlot, storeSlot, executeOps, packingExecuteOp,
    wordOp, wordInstruction, hh, hc, he, hne, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hr, BitVec.ofNat_add_ofNat, Nat.add_assoc, Nat.add_comm]

theorem execute_ancestorLead {bits : Nat} (rom : PhysicalROM) (header remaining entryBase encoded : Nat)
    (state : WordState bits) (hroom : Fits bits (header + 16))
    (hr : Fits bits (remaining + 1)) (hn : Fits bits encoded)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hc : state.register .total = BitVec.ofNat bits (remaining + 1))
    (he : state.heap (BitVec.ofNat bits (header + 13)) = BitVec.ofNat bits entryBase)
    (ha : state.heap (BitVec.ofNat bits (header + 11)) = BitVec.ofNat bits encoded) :
    let after := executeOps rom ancestorLead state
    after.heap = Function.update state.heap (BitVec.ofNat bits (header + 12)) (BitVec.ofNat bits remaining) ∧
      after.register .value = BitVec.ofNat bits (entryBase + 1 + (encoded - 1)) ∧
      after.register .address = BitVec.ofNat bits header := by
  have h1 : Fits bits 1 := (show 1 ≤ header + 16 by omega).trans_lt hroom
  have hne13 : BitVec.ofNat bits (header + 13) ≠ BitVec.ofNat bits (header + 12) := by
    intro heq
    have heq' := (slots_eq_iff header 13 12 hroom (by decide) (by decide)).mp heq
    omega
  have hne11 : BitVec.ofNat bits (header + 11) ≠ BitVec.ofNat bits (header + 12) := by
    intro heq
    have heq' := (slots_eq_iff header 11 12 hroom (by decide) (by decide)).mp heq
    omega
  simp +decide [ancestorLead, loadSlot, storeSlot, executeOps, packingExecuteOp,
    wordOp, wordInstruction, hh, hc, he, ha, hne13, hne11, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hn,
    BitVec.ofNat_add_ofNat, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem execute_budgetLead {bits : Nat} (rom : PhysicalROM) (header remaining rowBase size : Nat)
    (state : WordState bits) (hroom : Fits bits (header + 16))
    (hr : Fits bits (remaining + 1)) (ht : Fits bits (size + 1))
    (hh : state.register .address = BitVec.ofNat bits header)
    (hc : state.register .total = BitVec.ofNat bits (remaining + 1))
    (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hrow : state.heap (BitVec.ofNat bits header) = BitVec.ofNat bits rowBase) :
    let after := executeOps rom budgetLead state
    let scalar := rowBase + remaining * (size + 1)
    after.heap = Function.update
      (Function.update state.heap (BitVec.ofNat bits (header + 8)) (BitVec.ofNat bits remaining))
      (BitVec.ofNat bits (header + 13)) (BitVec.ofNat bits scalar) ∧
      after.register .value = BitVec.ofNat bits scalar ∧
      after.register .address = BitVec.ofNat bits header := by
  have h1 : Fits bits 1 := (show 1 ≤ header + 16 by omega).trans_lt hroom
  have hrf : Fits bits remaining := (show remaining ≤ remaining + 1 by omega).trans_lt hr
  have hz : BitVec.ofNat bits 0 ≠ BitVec.ofNat bits (header + 8) :=
    (slot_ne_zero header 8 hroom (by decide) (by decide)).symm
  have hne : BitVec.ofNat bits header ≠ BitVec.ofNat bits (header + 8) := by
    simpa only [Nat.add_zero] using (show BitVec.ofNat bits (header + 0) ≠ BitVec.ofNat bits (header + 8) from by
      intro heq
      have heq' := (slots_eq_iff header 0 8 hroom (by decide) (by decide)).mp heq
      omega)
  simp +decide [budgetLead, loadSlot, storeSlot, executeOps, packingExecuteOp,
    wordOp, wordInstruction, packingArithmetic, hh, hc, hsize, hrow,
    hz, hne, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hr,
    Nat.mod_eq_of_lt hrf, Nat.mod_eq_of_lt ht, BitVec.ofNat_add_ofNat]

theorem execute_parentTail {bits : Nat} (rom : PhysicalROM) (workspace size encoded : Nat)
    (state : WordState bits) (hb : 1 ≤ bits)
    (hroom : Fits bits (PSTRQueryLayout.header workspace size))
    (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hh : state.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size))
    (ha : state.register .fresh = BitVec.ofNat bits encoded) :
    let after := executeOps rom parentTail state
    after.heap = Function.update state.heap
      (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 11))
      (state.heap (BitVec.ofNat bits (PSTRQueryLayout.parentsBase workspace size + encoded))) ∧
      after.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size) := by
  have hsmall : 1 < 2 ^ bits := by
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb
    omega
  have hmul : Fits bits (size + 1) := by
    apply (show size + 1 ≤ PSTRQueryLayout.header workspace size from ?_).trans_lt hroom
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    omega
  have he : PSTRQueryLayout.header workspace size - (size + 1) = PSTRQueryLayout.parentsBase workspace size := by
    unfold PSTRQueryLayout.header
    omega
  simp +decide [parentTail, storeSlot, executeOps, packingExecuteOp,
    wordOp, wordInstruction, hsize, hh, ha, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hsmall, BitVec.ofNat_add_ofNat, Nat.mod_eq_of_lt hroom,
    Nat.mod_eq_of_lt hmul, he]

theorem execute_budgetFinish {bits : Nat} (rom : PhysicalROM) (header q budget : Nat)
    (state : WordState bits) (h1 : Fits bits 1)
    (hq : (rom.words .input).getD 1 0 = q)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hc : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits budget) :
    let after := executeOps rom budgetFinish state
    after.heap = Function.update state.heap (BitVec.ofNat bits (header + 16 + (q + 2) + budget))
      (state.heap (BitVec.ofNat bits (header + 14))) ∧
      after.register .address = BitVec.ofNat bits header := by
  change (rom.words .input)[1]?.getD 0 = q at hq
  simp +decide [budgetFinish, loadSlot, executeOps, packingExecuteOp,
    wordOp, wordInstruction, hq, hh, hc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
    BitVec.ofNat_add_ofNat, Nat.add_assoc, Nat.add_comm]
  congr 2; omega

theorem execute_goodStore {bits : Nat} (rom : PhysicalROM) (header budget : Nat)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (hc : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits budget) :
    let after := executeOps rom goodStore state
    after.heap = Function.update state.heap (BitVec.ofNat bits (header + 16 + budget))
      (state.heap (BitVec.ofNat bits (header + 10))) ∧
      after.register .flag = state.heap (BitVec.ofNat bits (header + 10)) ∧
      after.register .address = BitVec.ofNat bits header := by
  simp +decide [goodStore, loadSlot, executeOps, packingExecuteOp,
    wordOp, wordInstruction, hh, hc, BitVec.ofNat_add_ofNat]

theorem execute_ancestorInit {bits : Nat} (rom : PhysicalROM) (header : Nat)
    (state : WordState bits) (hroom : Fits bits (header + 16))
    (hh : state.register .address = BitVec.ofNat bits header) :
    let after := executeOps rom ancestorInit state
    let encoded := state.heap (BitVec.ofNat bits (header + 1))
    let flag := if encoded.toNat = 0 then BitVec.ofNat bits 0 else state.register .flag
    after.heap = Function.update
      (Function.update
        (Function.update state.heap (BitVec.ofNat bits (header + 11)) encoded)
        (BitVec.ofNat bits (header + 14)) flag)
      (BitVec.ofNat bits (header + 12)) (state.heap (BitVec.ofNat bits 0)) ∧
      after.register .address = BitVec.ofNat bits header := by
  have hz11 : BitVec.ofNat bits 0 ≠ BitVec.ofNat bits (header + 11) :=
    (slot_ne_zero header 11 hroom (by decide) (by decide)).symm
  have hz14 : BitVec.ofNat bits 0 ≠ BitVec.ofNat bits (header + 14) :=
    (slot_ne_zero header 14 hroom (by decide) (by decide)).symm
  simp +decide [ancestorInit, loadSlot, storeSlot, executeOps, packingExecuteOp,
    wordOp, wordInstruction, hh, BitVec.ofNat_add_ofNat, hz11, hz14]

theorem execute_acceptCompare {bits : Nat} (rom : PhysicalROM) (header : Nat) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header) :
    let after := executeOps rom acceptCompare state
    let flag := if (state.register .old).toNat ≤ (state.register .value).toNat
      then state.heap (BitVec.ofNat bits (header + 10)) else BitVec.ofNat bits 0
    after.heap = Function.update state.heap (BitVec.ofNat bits (header + 10)) flag ∧
      after.register .address = BitVec.ofNat bits header := by
  have hd : (state.register .old).toNat - (state.register .value).toNat < 2 ^ bits :=
    (Nat.sub_le _ _).trans_lt (BitVec.isLt _)
  simp +decide [acceptCompare, loadSlot, storeSlot, executeOps,
    packingExecuteOp, wordOp, wordInstruction, hh, BitVec.ofNat_add_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd, Nat.sub_eq_zero_iff_le]

theorem execute_extensionCompare {bits : Nat} (rom : PhysicalROM) (header : Nat) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header) :
    let after := executeOps rom extensionCompare state
    let flag := if (state.heap (BitVec.ofNat bits (header + 11))).toNat = 0 then
        state.heap (BitVec.ofNat bits (header + 14))
      else if (state.register .old).toNat < (state.register .value).toNat then
        state.heap (BitVec.ofNat bits (header + 14)) else BitVec.ofNat bits 0
    after.heap = Function.update state.heap (BitVec.ofNat bits (header + 14)) flag ∧
      after.register .fresh = state.heap (BitVec.ofNat bits (header + 11)) ∧
      after.register .address = BitVec.ofNat bits header := by
  have hd : (state.register .value).toNat - (state.register .old).toNat < 2 ^ bits :=
    (Nat.sub_le _ _).trans_lt (BitVec.isLt _)
  simp +decide [extensionCompare, loadSlot, storeSlot, executeOps,
    packingExecuteOp, wordOp, wordInstruction, hh, BitVec.ofNat_add_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd, Nat.sub_eq_zero_iff_le]
  split_ifs <;> simp_all; omega

theorem execute_nodeTail {bits : Nat} (rom : PhysicalROM) (workspace size node : Nat)
    (state : WordState bits) (hb : 2 ≤ bits)
    (hroom : Fits bits (PSTRQueryLayout.header workspace size))
    (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hh : state.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size))
    (hn : state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 9)) = BitVec.ofNat bits node) :
    let after := executeOps rom nodeTail state
    let flag := if (state.heap (BitVec.ofNat bits (PSTRQueryLayout.countsBase workspace + node))).toNat ≤
        (state.register .value).toNat
      then state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 10)) else BitVec.ofNat bits 0
    after.heap = Function.update state.heap
      (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 10)) flag ∧
      after.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size) := by
  let counted := executeOps rom nodeCountRead state
  have hc := execute_nodeCountRead rom workspace size node state hb hroom hsize hh hn
  have hs := execute_acceptCompare rom (PSTRQueryLayout.header workspace size) counted hc.2.2.1
  simpa only [nodeTail, executeOps_append, counted, hc.1, hc.2.1, hc.2.2.2] using hs

theorem execute_ancestorTail {bits : Nat} (rom : PhysicalROM) (workspace size encoded : Nat)
    (state : WordState bits) (hb : 2 ≤ bits)
    (hroom : Fits bits (PSTRQueryLayout.header workspace size + 16))
    (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hh : state.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size))
    (hn : state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 11)) = BitVec.ofNat bits encoded)
    (he : encoded ≤ size) :
    let header := PSTRQueryLayout.header workspace size
    let after := executeOps rom ancestorTail state
    let flag := if encoded = 0 then state.heap (BitVec.ofNat bits (header + 14))
      else if (state.heap (BitVec.ofNat bits (PSTRQueryLayout.countsBase workspace + (encoded - 1)))).toNat <
          (state.register .value).toNat
        then state.heap (BitVec.ofNat bits (header + 14)) else BitVec.ofNat bits 0
    after.heap = Function.update (Function.update state.heap (BitVec.ofNat bits (header + 14)) flag)
      (BitVec.ofNat bits (header + 11))
      (state.heap (BitVec.ofNat bits (PSTRQueryLayout.parentsBase workspace size + encoded))) ∧
      after.register .address = BitVec.ofNat bits header := by
  let header := PSTRQueryLayout.header workspace size
  let counted := executeOps rom ancestorCountRead state
  let compared := executeOps rom extensionCompare counted
  have hn' : state.heap (BitVec.ofNat bits (header + 11)) = BitVec.ofNat bits encoded := hn
  have hheader : Fits bits header := (Nat.le_add_right header 16).trans_lt hroom
  have henc : Fits bits encoded := (show encoded ≤ header by
    unfold header PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    omega).trans_lt hheader
  have hc := execute_ancestorCountRead rom workspace size encoded state hb henc hheader hsize hh hn
  have hx := execute_extensionCompare rom header counted hc.2.2.1
  have hxheap : compared.heap = Function.update state.heap (BitVec.ofNat bits (header + 14))
      (if encoded = 0 then state.heap (BitVec.ofNat bits (header + 14))
      else if (state.heap (BitVec.ofNat bits (PSTRQueryLayout.countsBase workspace + (encoded - 1)))).toNat <
          (state.register .value).toNat
        then state.heap (BitVec.ofNat bits (header + 14)) else BitVec.ofNat bits 0) := by
    simpa only [compared, counted, hc.1, hc.2.1, hc.2.2.2, hn',
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt henc] using hx.1
  have hxaddress : compared.register .address = BitVec.ofNat bits header := hx.2.2
  have hxfresh : compared.register .fresh = BitVec.ofNat bits encoded := by
    simpa only [counted, hc.2.2.2] using hx.2.1.trans hn
  have hz : BitVec.ofNat bits 0 ≠ BitVec.ofNat bits (header + 14) :=
    (slot_ne_zero header 14 hroom (by decide) (by decide)).symm
  have hparent : PSTRQueryLayout.parentsBase workspace size + encoded < header := by
    unfold header PSTRQueryLayout.header
    omega
  have hparentNe : BitVec.ofNat bits (PSTRQueryLayout.parentsBase workspace size + encoded) ≠
      BitVec.ofNat bits (header + 14) := by
    intro hh'
    have heq := (ofNat_injective_of_fit _ _ (hparent.trans hheader)
      ((show header + 14 ≤ header + 16 by omega).trans_lt hroom)).mp hh'
    omega
  have hs := execute_parentTail rom workspace size encoded compared (by omega) hheader
    (by rw [hxheap, Function.update_of_ne hz]; exact hsize) hxaddress hxfresh
  simpa only [ancestorTail, executeOps_append, compared, counted, hxheap,
    Function.update_of_ne hparentNe] using hs

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010

