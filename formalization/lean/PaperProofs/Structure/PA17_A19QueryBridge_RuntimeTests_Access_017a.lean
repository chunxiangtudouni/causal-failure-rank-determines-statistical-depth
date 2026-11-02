module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_010c

/-! Actual fixed tests scratch-phase access bounds. These lemmas inspect each
literal instruction prefix and require no incoming scratch value or safe-run
oracle. Scalar readers and indirect count/parent reads are separate. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsAccess017
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM PA17A19RuntimeTests010

theorem budgetLead_access {bits : Nat} (rom : PhysicalROM) (header heapWords : Nat)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (halloc : header + 15 < heapWords) (count : Nat) (hc : count < budgetLead.length) :
    packingAccessFits rom heapWords (executeOps rom (budgetLead.take count) state) budgetLead[count] := by
  change count < 17 at hc
  interval_cases count <;> try exact True.intro
  all_goals simp +decide [budgetLead, loadSlot, storeSlot, packingArithmetic, executeOps, packingExecuteOp, wordOp, wordInstruction, packingAccessFits, AccessFits, hh, BitVec.ofNat_add_ofNat]
  all_goals try apply (Nat.mod_le _ _).trans_lt
  all_goals omega

theorem tagTail_access {bits : Nat} (rom : PhysicalROM) (header heapWords : Nat)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (halloc : header + 15 < heapWords) (count : Nat) (hc : count < tagTail.length) :
    packingAccessFits rom heapWords (executeOps rom (tagTail.take count) state) tagTail[count] := by
  change count < 11 at hc
  interval_cases count <;> try exact True.intro
  all_goals simp +decide [tagTail, storeSlot, executeOps, packingExecuteOp, wordOp, wordInstruction, packingAccessFits, AccessFits, hh, BitVec.ofNat_add_ofNat]
  all_goals try apply (Nat.mod_le _ _).trans_lt
  all_goals omega

theorem nodeLead_access {bits : Nat} (rom : PhysicalROM) (header heapWords : Nat)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (halloc : header + 15 < heapWords) (count : Nat) (hc : count < nodeLead.length) :
    packingAccessFits rom heapWords (executeOps rom (nodeLead.take count) state) nodeLead[count] := by
  change count < 11 at hc
  interval_cases count <;> try exact True.intro
  all_goals simp +decide [nodeLead, loadSlot, storeSlot, executeOps, packingExecuteOp, wordOp, wordInstruction, packingAccessFits, AccessFits, hh, BitVec.ofNat_add_ofNat]
  all_goals try apply (Nat.mod_le _ _).trans_lt
  all_goals omega

theorem ancestorLead_access {bits : Nat} (rom : PhysicalROM) (header heapWords : Nat)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (halloc : header + 15 < heapWords) (count : Nat) (hc : count < ancestorLead.length) :
    packingAccessFits rom heapWords (executeOps rom (ancestorLead.take count) state) ancestorLead[count] := by
  change count < 15 at hc
  interval_cases count <;> try exact True.intro
  all_goals simp +decide [ancestorLead, loadSlot, storeSlot, executeOps, packingExecuteOp, wordOp, wordInstruction, packingAccessFits, AccessFits, hh, BitVec.ofNat_add_ofNat]
  all_goals try apply (Nat.mod_le _ _).trans_lt
  all_goals omega

theorem acceptCompare_access {bits : Nat} (rom : PhysicalROM) (header heapWords : Nat)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (halloc : header + 15 < heapWords) (count : Nat) (hc : count < acceptCompare.length) :
    packingAccessFits rom heapWords (executeOps rom (acceptCompare.take count) state) acceptCompare[count] := by
  change count < 9 at hc
  interval_cases count <;> try exact True.intro
  all_goals simp +decide [acceptCompare, loadSlot, storeSlot, executeOps, packingExecuteOp, wordOp, wordInstruction, packingAccessFits, AccessFits, hh, BitVec.ofNat_add_ofNat]
  all_goals try apply (Nat.mod_le _ _).trans_lt
  all_goals omega

theorem extensionCompare_access {bits : Nat} (rom : PhysicalROM) (header heapWords : Nat)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (halloc : header + 15 < heapWords) (count : Nat) (hc : count < extensionCompare.length) :
    packingAccessFits rom heapWords (executeOps rom (extensionCompare.take count) state) extensionCompare[count] := by
  change count < 13 at hc
  interval_cases count <;> try exact True.intro
  all_goals simp +decide [extensionCompare, loadSlot, storeSlot, executeOps, packingExecuteOp, wordOp, wordInstruction, packingAccessFits, AccessFits, hh, BitVec.ofNat_add_ofNat]
  all_goals try apply (Nat.mod_le _ _).trans_lt
  all_goals omega

theorem ancestorInit_access {bits : Nat} (rom : PhysicalROM) (header heapWords : Nat)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (halloc : header + 15 < heapWords) (count : Nat) (hc : count < ancestorInit.length) :
    packingAccessFits rom heapWords (executeOps rom (ancestorInit.take count) state) ancestorInit[count] := by
  change count < 16 at hc
  interval_cases count <;> try exact True.intro
  all_goals simp +decide [ancestorInit, loadSlot, storeSlot, executeOps, packingExecuteOp, wordOp, wordInstruction, packingAccessFits, AccessFits, hh, BitVec.ofNat_add_ofNat]
  all_goals try apply (Nat.mod_le _ _).trans_lt
  all_goals omega

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsAccess017
