module

public import Structure.PA17_A19QueryBridge_RuntimeTests_010a
public import Structure.PA17_A19QueryBridge_RuntimeRead_007c

/-! One fixed355-op tests kernel. Every dimension is runtime data. The sole
assembler parameter is the containing-code origin. H8..H14 are initialized
by real stores before use; H15 is unused. Three copies of the fixed58-op
reader occur in the finite code, never q*t copies. No HALT is inserted. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM

def setup : List PackingOp :=
  [.base (.base (.constant .index 1)), .base (.base (.loadROM .input .total .index)),
   .base (.base (.constant .fresh 2)), .base (.base (.add .total .total .fresh))] ++
  storeSlot 8 .total

def counterLead (slot target : Nat) : List PackingOp :=
  loadSlot slot .total ++ [.base (.base (.constant .old target))]

def counterTest (slot target : Nat) : List PackingOp :=
  counterLead slot target ++ [.jumpIfZero .total .old]

def backLead (target : Nat) : List PackingOp :=
  [.base (.base (.constant .old target)), .base (.base (.constant .fresh 0))]

def back (target : Nat) : List PackingOp := backLead target ++ [.jumpIfZero .fresh .old]

def budgetLead : List PackingOp :=
  [.base (.base (.constant .old 1)), .base (.subtract .total .total .old)] ++
  storeSlot 8 .total ++
  [.base (.base (.constant .index 0)), .base (.base (.loadHeap .old .index)),
   .base (.base (.constant .fresh 1)), .base (.base (.add .old .old .fresh)),
   .arithmetic .multiply .total .total .old] ++
  loadSlot 0 .value ++ [.base (.base (.add .value .value .total))] ++ storeSlot 13 .value

def tagTail : List PackingOp :=
  [.base (.base (.constant .fresh 0)), .base (.base (.constant .flag 1)),
   .base (.base (.select .flag .value .flag .fresh))] ++ storeSlot 10 .flag ++
  [.base (.base (.constant .index 0)), .base (.base (.loadHeap .total .index))] ++ storeSlot 9 .total

def nodeLead : List PackingOp :=
  [.base (.base (.constant .old 1)), .base (.subtract .total .total .old)] ++ storeSlot 9 .total ++
  loadSlot 13 .value ++
  [.base (.base (.constant .old 1)), .base (.base (.add .value .value .total)),
   .base (.base (.add .value .value .old))]

def countsLocator : List PackingOp :=
  [.base (.base (.constant .index 0)), .base (.base (.loadHeap .total .index)),
   .base (.base (.constant .old 2)), .arithmetic .multiply .total .total .old,
   .base (.base (.constant .old 1)), .base (.base (.add .total .total .old)),
   .base (.subtract .total .address .total)]

def acceptCompare : List PackingOp := [.base (.subtract .old .old .value)] ++ loadSlot 10 .flag ++
  [.base (.base (.constant .fresh 0)), .base (.base (.select .flag .old .fresh .flag))] ++
  storeSlot 10 .flag

def nodeReadSuffix : List PackingOp := loadSlot 9 .fresh ++
  [.base (.base (.add .total .total .fresh)), .base (.base (.loadHeap .old .total))]

def nodeCountRead : List PackingOp := countsLocator ++ nodeReadSuffix

def nodeTail : List PackingOp := nodeCountRead ++ acceptCompare

def goodStore : List PackingOp := loadSlot 10 .flag ++ loadSlot 8 .total ++
  [.base (.base (.constant .old 16)), .base (.base (.add .old .address .old)),
   .base (.base (.add .old .old .total)), .base (.base (.storeHeap .old .flag))]

def ancestorInit : List PackingOp := loadSlot 1 .fresh ++ storeSlot 11 .fresh ++
  [.base (.base (.constant .old 0)), .base (.base (.select .flag .fresh .flag .old))] ++
  storeSlot 14 .flag ++
  [.base (.base (.constant .index 0)), .base (.base (.loadHeap .total .index))] ++ storeSlot 12 .total

def acceptFinish : List PackingOp := goodStore ++ ancestorInit

def ancestorLead : List PackingOp :=
  [.base (.base (.constant .old 1)), .base (.subtract .total .total .old)] ++ storeSlot 12 .total ++
  loadSlot 11 .fresh ++
  [.base (.base (.constant .old 1)), .base (.subtract .fresh .fresh .old)] ++
  loadSlot 13 .value ++
  [.base (.base (.add .value .value .fresh)), .base (.base (.add .value .value .old))]

def extensionCompare : List PackingOp := [.base (.subtract .value .value .old)] ++
  loadSlot 14 .total ++
  [.base (.base (.constant .old 0)), .base (.base (.select .flag .value .total .old))] ++
  loadSlot 11 .fresh ++ [.base (.base (.select .flag .fresh .flag .total))] ++ storeSlot 14 .flag

def parentTail : List PackingOp :=
  [.base (.base (.constant .index 0)), .base (.base (.loadHeap .total .index)),
   .base (.base (.constant .old 1)), .base (.base (.add .total .total .old)),
   .base (.subtract .total .address .total), .base (.base (.add .total .total .fresh)),
   .base (.base (.loadHeap .fresh .total))] ++ storeSlot 11 .fresh

def ancestorReadSuffix : List PackingOp := loadSlot 11 .fresh ++
  [.base (.subtract .fresh .fresh .old), .base (.base (.add .total .total .fresh)),
   .base (.base (.loadHeap .old .total))]

def ancestorCountRead : List PackingOp := countsLocator ++ ancestorReadSuffix

def ancestorTail : List PackingOp := ancestorCountRead ++ extensionCompare ++ parentTail

def budgetFinish : List PackingOp := loadSlot 14 .flag ++ loadSlot 8 .total ++
  [.base (.base (.constant .index 1)), .base (.base (.loadROM .input .old .index)),
   .base (.base (.constant .fresh 18)), .base (.base (.add .old .old .fresh)),
   .base (.base (.add .old .address .old)), .base (.base (.add .old .old .total)),
   .base (.base (.storeHeap .old .flag))]

def programAt (origin : Nat) : List PackingOp :=
  setup ++ counterTest 8 (5 * (origin + 355)) ++
  budgetLead ++ PA17A19RuntimeRead007.cachedProgram ++ tagTail ++
  counterTest 9 (5 * (origin + 196)) ++
  nodeLead ++ PA17A19RuntimeRead007.cachedProgram ++ nodeTail ++ back (5 * (origin + 98)) ++
  acceptFinish ++ counterTest 12 (5 * (origin + 339)) ++
  ancestorLead ++ PA17A19RuntimeRead007.cachedProgram ++ ancestorTail ++ back (5 * (origin + 222)) ++
  budgetFinish ++ back (5 * (origin + 7))

def budgetInit : List PackingOp := budgetLead ++ PA17A19RuntimeRead007.cachedProgram ++ tagTail
def nodeBodyLead (origin : Nat) : List PackingOp :=
  nodeLead ++ PA17A19RuntimeRead007.cachedProgram ++ nodeTail ++ backLead (5 * (origin + 98))
def nodeBody (origin : Nat) : List PackingOp := nodeBodyLead origin ++ [.jumpIfZero .fresh .old]
def ancestorBodyLead (origin : Nat) : List PackingOp :=
  ancestorLead ++ PA17A19RuntimeRead007.cachedProgram ++ ancestorTail ++ backLead (5 * (origin + 222))
def ancestorBody (origin : Nat) : List PackingOp := ancestorBodyLead origin ++ [.jumpIfZero .fresh .old]
def budgetFooterLead (origin : Nat) : List PackingOp := budgetFinish ++ backLead (5 * (origin + 7))
def budgetFooter (origin : Nat) : List PackingOp := budgetFooterLead origin ++ [.jumpIfZero .fresh .old]

def steps (q size : Nat) : Nat := 12 + (q + 2) * (143 + 215 * size)

theorem setup_length : setup.length = 7 := rfl
theorem counterLead_length (slot target : Nat) : (counterLead slot target).length = 4 := rfl
theorem counterTest_length (slot target : Nat) : (counterTest slot target).length = 5 := rfl
theorem backLead_length (target : Nat) : (backLead target).length = 2 := rfl
theorem back_length (target : Nat) : (back target).length = 3 := rfl
theorem budgetLead_length : budgetLead.length = 17 := rfl
theorem tagTail_length : tagTail.length = 11 := rfl
theorem nodeLead_length : nodeLead.length = 11 := rfl
theorem countsLocator_length : countsLocator.length = 7 := rfl
theorem acceptCompare_length : acceptCompare.length = 9 := rfl
theorem nodeCountRead_length : nodeCountRead.length = 12 := rfl
theorem nodeTail_length : nodeTail.length = 21 := rfl
theorem goodStore_length : goodStore.length = 10 := rfl
theorem ancestorInit_length : ancestorInit.length = 16 := rfl
theorem acceptFinish_length : acceptFinish.length = 26 := rfl
theorem ancestorLead_length : ancestorLead.length = 15 := rfl
theorem extensionCompare_length : extensionCompare.length = 13 := rfl
theorem parentTail_length : parentTail.length = 10 := rfl
theorem ancestorCountRead_length : ancestorCountRead.length = 13 := rfl
theorem ancestorTail_length : ancestorTail.length = 36 := rfl
theorem budgetFinish_length : budgetFinish.length = 13 := rfl
theorem programAt_length (origin : Nat) : (programAt origin).length = 355 := by
  simp only [programAt, List.length_append, setup_length, counterTest_length,
    budgetLead_length, PA17A19RuntimeRead007.cachedProgram_length, tagTail_length,
    nodeLead_length, nodeTail_length, back_length, acceptFinish_length,
    ancestorLead_length, ancestorTail_length, budgetFinish_length]
theorem budgetInit_length : budgetInit.length = 86 := rfl
theorem nodeBodyLead_length (origin : Nat) : (nodeBodyLead origin).length = 92 := rfl
theorem nodeBody_length (origin : Nat) : (nodeBody origin).length = 93 := rfl
theorem ancestorBodyLead_length (origin : Nat) : (ancestorBodyLead origin).length = 111 := rfl
theorem ancestorBody_length (origin : Nat) : (ancestorBody origin).length = 112 := rfl
theorem budgetFooterLead_length (origin : Nat) : (budgetFooterLead origin).length = 15 := rfl
theorem budgetFooter_length (origin : Nat) : (budgetFooter origin).length = 16 := rfl

theorem setup_straight : StraightProgram setup := by simp [setup, storeSlot, StraightProgram, StraightOp]
theorem counterLead_straight (slot target : Nat) : StraightProgram (counterLead slot target) := by
  simp [counterLead, loadSlot, StraightProgram, StraightOp]
theorem backLead_straight (target : Nat) : StraightProgram (backLead target) := by
  simp [backLead, StraightProgram, StraightOp]
theorem budgetLead_straight : StraightProgram budgetLead := by
  simp [budgetLead, loadSlot, storeSlot, StraightProgram, StraightOp]
theorem tagTail_straight : StraightProgram tagTail := by
  simp [tagTail, storeSlot, StraightProgram, StraightOp]
theorem nodeLead_straight : StraightProgram nodeLead := by
  simp [nodeLead, loadSlot, storeSlot, StraightProgram, StraightOp]
theorem countsLocator_straight : StraightProgram countsLocator := by
  simp [countsLocator, StraightProgram, StraightOp]
theorem nodeTail_straight : StraightProgram nodeTail := by
  simp [nodeTail, nodeCountRead, nodeReadSuffix, acceptCompare, countsLocator, loadSlot, storeSlot, StraightProgram, StraightOp]
theorem acceptFinish_straight : StraightProgram acceptFinish := by
  simp [acceptFinish, goodStore, ancestorInit, loadSlot, storeSlot, StraightProgram, StraightOp]
theorem ancestorLead_straight : StraightProgram ancestorLead := by
  simp [ancestorLead, loadSlot, storeSlot, StraightProgram, StraightOp]
theorem ancestorTail_straight : StraightProgram ancestorTail := by
  simp [ancestorTail, ancestorCountRead, ancestorReadSuffix, extensionCompare, parentTail, countsLocator, loadSlot, storeSlot, StraightProgram, StraightOp]
theorem budgetFinish_straight : StraightProgram budgetFinish := by
  simp [budgetFinish, loadSlot, StraightProgram, StraightOp]

theorem straight_append (left right : List PackingOp)
    (hl : StraightProgram left) (hr : StraightProgram right) : StraightProgram (left ++ right) := by
  intro op ho
  rcases List.mem_append.mp ho with ho | ho
  · exact hl op ho
  · exact hr op ho

theorem budgetInit_straight : StraightProgram budgetInit :=
  straight_append _ _ (straight_append _ _ budgetLead_straight PA17A19RuntimeRead007.cachedProgram_straight)
    tagTail_straight

theorem nodeBodyLead_straight (origin : Nat) : StraightProgram (nodeBodyLead origin) :=
  straight_append _ _ (straight_append _ _ (straight_append _ _ nodeLead_straight
    PA17A19RuntimeRead007.cachedProgram_straight) nodeTail_straight) (backLead_straight _)

theorem ancestorBodyLead_straight (origin : Nat) : StraightProgram (ancestorBodyLead origin) :=
  straight_append _ _ (straight_append _ _ (straight_append _ _ ancestorLead_straight
    PA17A19RuntimeRead007.cachedProgram_straight) ancestorTail_straight) (backLead_straight _)

theorem budgetFooterLead_straight (origin : Nat) : StraightProgram (budgetFooterLead origin) :=
  straight_append _ _ budgetFinish_straight (backLead_straight _)

theorem steps_bound (q size : Nat) (ht : 0 < size) : steps q size ≤ 728 * ((q + 1) * size) := by
  have hq : q + 2 ≤ 2 * (q + 1) := by omega
  have hs : 143 + 215 * size ≤ 358 * size := by omega
  have hm := Nat.mul_le_mul hq hs
  have hp : 1 ≤ (q + 1) * size := Nat.mul_pos (by omega) ht
  unfold steps
  nlinarith

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
