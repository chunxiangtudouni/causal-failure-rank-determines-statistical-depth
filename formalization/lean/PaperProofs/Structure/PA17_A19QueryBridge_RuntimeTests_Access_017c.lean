module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Access_017b

/-! Indirect counts/parents access from the real fixed arithmetic locator,
including the actual parent zero sentinel. No precomputed parent is input. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsAccess017
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM PA17A19RuntimeTests010

theorem parentTail_access {bits : Nat} (rom : PhysicalROM) (workspace size encoded heapWords : Nat)
    (state : WordState bits) (hb : 1 ≤ bits)
    (hroom : Fits bits (PSTRQueryLayout.header workspace size))
    (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hh : state.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size))
    (he : state.register .fresh = BitVec.ofNat bits encoded) (hencoded : encoded ≤ size)
    (halloc : PSTRQueryLayout.header workspace size + 15 < heapWords)
    (count : Nat) (hc : count < parentTail.length) :
    packingAccessFits rom heapWords (executeOps rom (parentTail.take count) state) parentTail[count] := by
  have hsmall : 1 < 2 ^ bits := by
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb
    omega
  have hmul : Fits bits (size + 1) := by
    apply (show size + 1 ≤ PSTRQueryLayout.header workspace size from ?_).trans_lt hroom
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    omega
  have hd : PSTRQueryLayout.header workspace size - (size + 1) =
      PSTRQueryLayout.parentsBase workspace size := by
    unfold PSTRQueryLayout.header
    omega
  have hparent : PSTRQueryLayout.parentsBase workspace size + encoded < heapWords := by
    unfold PSTRQueryLayout.header at halloc
    omega
  change count < 10 at hc
  interval_cases count <;> try exact True.intro
  all_goals simp +decide [parentTail, storeSlot, executeOps, packingExecuteOp,
    wordOp, wordInstruction, packingAccessFits, AccessFits, hsize, hh, he,
    Nat.mod_eq_of_lt hsmall, BitVec.ofNat_add_ofNat, Nat.mod_eq_of_lt hroom,
    Nat.mod_eq_of_lt hmul, hd]
  all_goals try apply (Nat.mod_le _ _).trans_lt
  all_goals omega

theorem nodeCountRead_access {bits : Nat} (rom : PhysicalROM) (workspace size node heapWords : Nat)
    (state : WordState bits) (hb : 2 ≤ bits)
    (hroom : Fits bits (PSTRQueryLayout.header workspace size))
    (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hh : state.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size))
    (hn : state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 9)) = BitVec.ofNat bits node)
    (hnode : node < size) (halloc : PSTRQueryLayout.header workspace size + 15 < heapWords) :
    ∀ count (hc : count < nodeCountRead.length), packingAccessFits rom heapWords
      (executeOps rom (nodeCountRead.take count) state) nodeCountRead[count] := by
  let located := executeOps rom countsLocator state
  have hl := execute_countsLocator rom workspace size state hb hroom hsize hh
  have hcount : PSTRQueryLayout.countsBase workspace + node < heapWords := by
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase at halloc
    omega
  exact PA17A19RuntimeRead007.access_append rom heapWords countsLocator nodeReadSuffix state
    (countsLocator_access rom heapWords state (by omega))
    (nodeReadSuffix_access rom (PSTRQueryLayout.header workspace size)
      (PSTRQueryLayout.countsBase workspace) node heapWords located hl.2.2.1 hl.1
      (by rw [show located.heap = state.heap from hl.2.2.2.2]; exact hn) (by omega) hcount)

theorem ancestorCountRead_access {bits : Nat} (rom : PhysicalROM) (workspace size encoded heapWords : Nat)
    (state : WordState bits) (hb : 2 ≤ bits)
    (hroom : Fits bits (PSTRQueryLayout.header workspace size))
    (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hh : state.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size))
    (hn : state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 11)) = BitVec.ofNat bits encoded)
    (ht : 0 < size) (he : encoded ≤ size)
    (halloc : PSTRQueryLayout.header workspace size + 15 < heapWords) :
    ∀ count (hc : count < ancestorCountRead.length), packingAccessFits rom heapWords
      (executeOps rom (ancestorCountRead.take count) state) ancestorCountRead[count] := by
  let located := executeOps rom countsLocator state
  have h1 : Fits bits 1 := (show 1 ≤ PSTRQueryLayout.header workspace size from by
    unfold PSTRQueryLayout.header; omega).trans_lt hroom
  have henc : Fits bits encoded := (show encoded ≤ PSTRQueryLayout.header workspace size from by
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase; omega).trans_lt hroom
  have hl := execute_countsLocator rom workspace size state hb hroom hsize hh
  have hcount : PSTRQueryLayout.countsBase workspace + (encoded - 1) < heapWords := by
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase at halloc
    omega
  exact PA17A19RuntimeRead007.access_append rom heapWords countsLocator ancestorReadSuffix state
    (countsLocator_access rom heapWords state (by omega))
    (ancestorReadSuffix_access rom (PSTRQueryLayout.header workspace size)
      (PSTRQueryLayout.countsBase workspace) encoded heapWords located h1 henc hl.2.2.1 hl.1 hl.2.1
      (by rw [show located.heap = state.heap from hl.2.2.2.2]; exact hn) (by omega) hcount)

theorem nodeTail_access {bits : Nat} (rom : PhysicalROM) (workspace size node heapWords : Nat)
    (state : WordState bits) (hb : 2 ≤ bits)
    (hroom : Fits bits (PSTRQueryLayout.header workspace size))
    (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hh : state.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size))
    (hn : state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 9)) = BitVec.ofNat bits node)
    (hnode : node < size) (halloc : PSTRQueryLayout.header workspace size + 15 < heapWords) :
    ∀ count (hc : count < PA17A19RuntimeTests010.nodeTail.length), packingAccessFits rom heapWords
      (executeOps rom (PA17A19RuntimeTests010.nodeTail.take count) state) PA17A19RuntimeTests010.nodeTail[count] := by
  have counted := execute_nodeCountRead rom workspace size node state hb hroom hsize hh hn
  exact PA17A19RuntimeRead007.access_append rom heapWords nodeCountRead acceptCompare state
    (nodeCountRead_access rom workspace size node heapWords state hb hroom hsize hh hn hnode halloc)
    (acceptCompare_access rom _ heapWords _ counted.2.2.1 halloc)

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsAccess017
