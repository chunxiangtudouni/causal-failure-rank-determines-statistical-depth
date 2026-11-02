module

public import Structure.PA17_A19QueryBridge_RuntimeTests_Access_017c

/-! Complete real nonreader composite phases. The iterator/encoded-parent
values and zero-sentinel load remain actual heap values in this same run. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsAccess017
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM PA17A19RuntimeTests010

theorem ancestorTail_access {bits : Nat} (rom : PhysicalROM) (workspace size encoded heapWords : Nat)
    (state : WordState bits) (hb : 2 ≤ bits)
    (hroom : Fits bits (PSTRQueryLayout.header workspace size + 16))
    (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hh : state.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size))
    (hn : state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 11)) = BitVec.ofNat bits encoded)
    (ht : 0 < size) (he : encoded ≤ size)
    (halloc : PSTRQueryLayout.header workspace size + 15 < heapWords) :
    ∀ count (hc : count < ancestorTail.length), packingAccessFits rom heapWords
      (executeOps rom (ancestorTail.take count) state) ancestorTail[count] := by
  let header := PSTRQueryLayout.header workspace size
  let counted := executeOps rom ancestorCountRead state
  let compared := executeOps rom extensionCompare counted
  have hheader : Fits bits header := (Nat.le_add_right header 16).trans_lt hroom
  have henc : Fits bits encoded := (show encoded ≤ header from by
    unfold header PSTRQueryLayout.header PSTRQueryLayout.parentsBase; omega).trans_lt hheader
  have hc := execute_ancestorCountRead rom workspace size encoded state hb henc hheader hsize hh hn
  have hx := execute_extensionCompare rom header counted hc.2.2.1
  have hxfresh : compared.register .fresh = BitVec.ofNat bits encoded := by
    simpa only [counted, hc.2.2.2] using hx.2.1.trans hn
  have hz : BitVec.ofNat bits 0 ≠ BitVec.ofNat bits (header + 14) :=
    (slot_ne_zero header 14 hroom (by decide) (by decide)).symm
  have hsizeCompared : (compared.heap (BitVec.ofNat bits 0)).toNat = size := by
    rw [show compared.heap = _ from hx.1, Function.update_of_ne hz,
      show counted.heap = state.heap from hc.2.2.2]
    exact hsize
  apply PA17A19RuntimeRead007.access_append rom heapWords (ancestorCountRead ++ extensionCompare) parentTail state
  · exact PA17A19RuntimeRead007.access_append rom heapWords ancestorCountRead extensionCompare state
      (ancestorCountRead_access rom workspace size encoded heapWords state hb hheader hsize hh hn ht he halloc)
      (extensionCompare_access rom header heapWords counted hc.2.2.1 halloc)
  · simpa only [executeOps_append] using
      parentTail_access rom workspace size encoded heapWords compared (by omega) hheader
        hsizeCompared hx.2.2 hxfresh he halloc

theorem acceptFinish_access {bits : Nat} (rom : PhysicalROM) (header budget heapWords : Nat)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (hb : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits budget)
    (halloc : header + 16 + budget < heapWords) :
    ∀ count (hc : count < acceptFinish.length), packingAccessFits rom heapWords
      (executeOps rom (acceptFinish.take count) state) acceptFinish[count] := by
  have stored := execute_goodStore rom header budget state hh hb
  exact PA17A19RuntimeRead007.access_append rom heapWords goodStore ancestorInit state
    (goodStore_access rom header budget heapWords state hh hb halloc)
    (ancestorInit_access rom header heapWords _ stored.2.2 (by omega))

theorem budgetFooter_access {bits : Nat} (rom : PhysicalROM) (origin header q budget heapWords : Nat)
    (state : WordState bits) (h1 : Fits bits 1) (hinput : 1 < rom.input.length)
    (hq : (rom.words .input).getD 1 0 = q)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hb : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits budget)
    (halloc : header + q + 18 + budget < heapWords) :
    ∀ count (hc : count < (budgetFooter origin).length), packingAccessFits rom heapWords
      (executeOps rom ((budgetFooter origin).take count) state) (budgetFooter origin)[count] := by
  exact PA17A19RuntimeRead007.access_append rom heapWords budgetFinish (back (5 * (origin + 7))) state
    (budgetFinish_access rom header q budget heapWords state h1 hinput hq hh hb halloc)
    (back_access rom _ heapWords _)

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsAccess017
