module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Access_017a

/-! Fixed tests control and indirect array loads. The assumptions are actual
saved field values and bounds on the particular arrays used by the code. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsAccess017
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM PA17A19RuntimeTests010

theorem setup_access {bits : Nat} (rom : PhysicalROM) (header heapWords : Nat)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (halloc : header + 8 < heapWords) (hinput : 1 < rom.input.length)
    (count : Nat) (hc : count < setup.length) :
    packingAccessFits rom heapWords (executeOps rom (setup.take count) state) setup[count] := by
  change count < 7 at hc
  interval_cases count <;> try exact True.intro
  all_goals simp +decide [setup, storeSlot, executeOps, packingExecuteOp, wordOp, wordInstruction, packingAccessFits, AccessFits, hh, BitVec.ofNat_add_ofNat]
  all_goals apply (Nat.mod_le _ _).trans_lt
  · exact hinput
  · exact halloc

theorem counterTest_access {bits : Nat} (rom : PhysicalROM) (slot target header heapWords : Nat)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (halloc : header + slot < heapWords) (count : Nat) (hc : count < (counterTest slot target).length) :
    packingAccessFits rom heapWords (executeOps rom ((counterTest slot target).take count) state)
      (counterTest slot target)[count] := by
  change count < 5 at hc
  interval_cases count <;> try exact True.intro
  simp +decide [counterTest, counterLead, loadSlot, executeOps, packingExecuteOp, wordOp, wordInstruction, packingAccessFits, AccessFits, hh, BitVec.ofNat_add_ofNat]
  exact (Nat.mod_le _ _).trans_lt halloc

theorem back_access {bits : Nat} (rom : PhysicalROM) (target heapWords : Nat)
    (state : WordState bits) (count : Nat) (hc : count < (back target).length) :
    packingAccessFits rom heapWords (executeOps rom ((back target).take count) state)
      (back target)[count] := by
  change count < 3 at hc
  interval_cases count <;> exact True.intro

theorem countsLocator_access {bits : Nat} (rom : PhysicalROM) (heapWords : Nat)
    (state : WordState bits) (halloc : 0 < heapWords)
    (count : Nat) (hc : count < countsLocator.length) :
    packingAccessFits rom heapWords (executeOps rom (countsLocator.take count) state) countsLocator[count] := by
  change count < 7 at hc
  interval_cases count <;> try exact True.intro
  simpa +decide [countsLocator, executeOps, packingExecuteOp, wordOp, wordInstruction, packingAccessFits, AccessFits] using halloc

theorem nodeReadSuffix_access {bits : Nat} (rom : PhysicalROM) (header countsBase node heapWords : Nat)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (hb : state.register .total = BitVec.ofNat bits countsBase)
    (hn : state.heap (BitVec.ofNat bits (header + 9)) = BitVec.ofNat bits node)
    (hslot : header + 9 < heapWords) (hcounts : countsBase + node < heapWords)
    (count : Nat) (hc : count < nodeReadSuffix.length) :
    packingAccessFits rom heapWords (executeOps rom (nodeReadSuffix.take count) state) nodeReadSuffix[count] := by
  change count < 5 at hc
  interval_cases count <;> try exact True.intro
  all_goals simp +decide [nodeReadSuffix, loadSlot, executeOps, packingExecuteOp, wordOp, wordInstruction, packingAccessFits, AccessFits, hh, hb, hn, BitVec.ofNat_add_ofNat]
  all_goals apply (Nat.mod_le _ _).trans_lt
  · exact hslot
  · exact hcounts

theorem ancestorReadSuffix_access {bits : Nat} (rom : PhysicalROM) (header countsBase encoded heapWords : Nat)
    (state : WordState bits) (h1 : Fits bits 1) (hf : Fits bits encoded)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hb : state.register .total = BitVec.ofNat bits countsBase)
    (ho : state.register .old = BitVec.ofNat bits 1)
    (hn : state.heap (BitVec.ofNat bits (header + 11)) = BitVec.ofNat bits encoded)
    (hslot : header + 11 < heapWords) (hcounts : countsBase + (encoded - 1) < heapWords)
    (count : Nat) (hc : count < ancestorReadSuffix.length) :
    packingAccessFits rom heapWords (executeOps rom (ancestorReadSuffix.take count) state) ancestorReadSuffix[count] := by
  change count < 6 at hc
  interval_cases count <;> try exact True.intro
  all_goals simp +decide [ancestorReadSuffix, loadSlot, executeOps, packingExecuteOp, wordOp, wordInstruction, packingAccessFits, AccessFits, hh, hb, ho, hn, BitVec.ofNat_add_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hf]
  all_goals apply (Nat.mod_le _ _).trans_lt
  · exact hslot
  · exact hcounts

theorem goodStore_access {bits : Nat} (rom : PhysicalROM) (header budget heapWords : Nat)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (hb : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits budget)
    (halloc : header + 16 + budget < heapWords)
    (count : Nat) (hc : count < goodStore.length) :
    packingAccessFits rom heapWords (executeOps rom (goodStore.take count) state) goodStore[count] := by
  change count < 10 at hc
  interval_cases count <;> try exact True.intro
  all_goals simp +decide [goodStore, loadSlot, executeOps, packingExecuteOp, wordOp, wordInstruction, packingAccessFits, AccessFits, hh, hb, BitVec.ofNat_add_ofNat]
  all_goals apply (Nat.mod_le _ _).trans_lt
  all_goals omega

theorem budgetFinish_access {bits : Nat} (rom : PhysicalROM) (header q budget heapWords : Nat)
    (state : WordState bits) (h1 : Fits bits 1) (hinput : 1 < rom.input.length)
    (hq : (rom.words .input).getD 1 0 = q)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hb : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits budget)
    (halloc : header + q + 18 + budget < heapWords)
    (count : Nat) (hc : count < budgetFinish.length) :
    packingAccessFits rom heapWords (executeOps rom (budgetFinish.take count) state) budgetFinish[count] := by
  have hq' : ((rom.words .input)[1]?).getD 0 = q := hq
  change count < 13 at hc
  interval_cases count <;> try exact True.intro
  all_goals simp +decide [budgetFinish, loadSlot, executeOps, packingExecuteOp, wordOp, wordInstruction, packingAccessFits, AccessFits, hh, hb, BitVec.ofNat_add_ofNat, Nat.mod_eq_of_lt h1, hq']
  all_goals try exact hinput
  all_goals apply (Nat.mod_le _ _).trans_lt
  all_goals omega

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsAccess017
