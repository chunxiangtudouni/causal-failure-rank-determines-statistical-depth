module

public import Paid.PDROC_D27Prepare_Resources_003
public import Paid.PDROC_D27Prepare_Program_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute
open PDCompute.Solver
open PDROC.D27Prepare.Program

namespace PDROC.D27Prepare.Resources

theorem single_prefix_bounds (input : List Cell) (instruction : Instruction)
    (before after : State) (H B : ℕ) (hbefore : StateBounds H B before)
    (hafter : StateBounds H B after) (executed : instruction.execute input before = some after) :
    LinearPrefixBounds input [instruction] before H B :=
  LinearPrefixBounds.cons input instruction [] before after H B hbefore executed
    (LinearPrefixBounds.nil input hafter)

theorem constantSlot_prefix_bounds (input : List Cell) (before : State)
    (target H B : ℕ) (value : Cell) (hbefore : StateBounds H B before)
    (fresh : before.register .fresh = .natural 0) (inside : target < H)
    (addressBits : 1 + natBits H ≤ B) (valueBits : value.bits ≤ B) :
    LinearPrefixBounds input (constantSlot target value) before H B := by
  let middle := ({before with pc := before.pc + 1}).set .total value
  have hm : StateBounds H B middle := (hbefore.with_pc _).set _ _ valueBits
  have first : LinearPrefixBounds input [.constant .total value] before H B :=
    single_prefix_bounds input _ before middle H B hbefore hm (by rfl)
  have execute : linearExecute input [.constant .total value] before = some middle := rfl
  apply LinearPrefixBounds.append input _ _ before middle H B execute first
  exact storeSlot_prefix_bounds input middle target .total H B hm
    (by simpa [middle, State.set] using fresh) inside (by decide)
    (address_cell_bits target H B inside addressBits)

theorem copySlot_prefix_bounds (input : List Cell) (before : State)
    (source target H B : ℕ) (hbefore : StateBounds H B before)
    (fresh : before.register .fresh = .natural 0) (live : source ∈ before.live)
    (sourceInside : source < H) (targetInside : target < H)
    (addressBits : 1 + natBits H ≤ B) :
    LinearPrefixBounds input (copySlot source target) before H B := by
  let middle := loadSlotResult before 0 source .total
  have first := loadSlot_prefix_bounds input before source .total H B hbefore fresh live
    (address_cell_bits source H B sourceInside addressBits)
  have execute : linearExecute input (loadSlot source .total) before = some middle :=
    loadSlot_execute input before 0 source .total fresh (by simpa only [Nat.zero_add] using live)
  have hm := first.final execute
  apply LinearPrefixBounds.append input _ _ before middle H B execute first
  exact storeSlot_prefix_bounds input middle target .total H B hm
    (by simpa [middle, loadSlotResult] using fresh) targetInside (by decide)
    (address_cell_bits target H B targetInside addressBits)

/-- The only arithmetic result of a binary macro is explicitly bounded.
All earlier literal states only contain incoming cells, the two heap reads,
fixed addresses and that result. In particular this lemma does not iterate
a coarse arithmetic-growth factor over the data-dependent outer loops. -/
theorem binary_macro_prefix_bounds (input : List Cell) (before : State)
    (left right target H B : ℕ) (instruction : Instruction) (value : Cell)
    (hbefore : StateBounds H B before) (fresh : before.register .fresh = .natural 0)
    (leftLive : left ∈ before.live) (rightLive : right ∈ before.live)
    (leftInside : left < H) (rightInside : right < H) (targetInside : target < H)
    (addressBits : 1 + natBits H ≤ B) (valueBits : value.bits ≤ B)
    (operation : let loaded := loadSlotResult (loadSlotResult before 0 left .total) 0 right .value
      instruction.execute input loaded = some (({loaded with pc := loaded.pc + 1}).set .total value)) :
    LinearPrefixBounds input
      (loadSlot left .total ++ loadSlot right .value ++ [instruction] ++ storeSlot target .total)
      before H B := by
  let first := loadSlotResult before 0 left .total
  let loaded := loadSlotResult first 0 right .value
  let computed := ({loaded with pc := loaded.pc + 1}).set .total value
  have firstExecute : linearExecute input (loadSlot left .total) before = some first :=
    loadSlot_execute input before 0 left .total fresh (by simpa only [Nat.zero_add] using leftLive)
  have firstBounds := loadSlot_prefix_bounds input before left .total H B hbefore fresh leftLive
    (address_cell_bits left H B leftInside addressBits)
  have hf := firstBounds.final firstExecute
  have firstFresh : first.register .fresh = .natural 0 := by simpa [first, loadSlotResult] using fresh
  have secondExecute : linearExecute input (loadSlot right .value) first = some loaded :=
    loadSlot_execute input first 0 right .value firstFresh (by simpa [first, loadSlotResult] using rightLive)
  have secondBounds := loadSlot_prefix_bounds input first right .value H B hf firstFresh
    (by simpa [first, loadSlotResult] using rightLive) (address_cell_bits right H B rightInside addressBits)
  have hl := secondBounds.final secondExecute
  have computedBounds : StateBounds H B computed := (hl.with_pc _).set _ _ valueBits
  have operationExecute : instruction.execute input loaded = some computed := operation
  have operationBounds := single_prefix_bounds input instruction loaded computed H B hl computedBounds operationExecute
  have storeBounds := storeSlot_prefix_bounds input computed target .total H B computedBounds
    (by simpa [computed, loaded, first, loadSlotResult, State.set] using fresh)
    targetInside (by decide) (address_cell_bits target H B targetInside addressBits)
  have firstTwoExecute : linearExecute input (loadSlot left .total ++ loadSlot right .value) before = some loaded := by
    rw [linearExecute_append, firstExecute, Option.bind_some, secondExecute]
  have firstTwoBounds := LinearPrefixBounds.append input _ _ before first H B firstExecute firstBounds secondBounds
  have firstThreeExecute : linearExecute input
      (loadSlot left .total ++ loadSlot right .value ++ [instruction]) before = some computed := by
    rw [linearExecute_append, firstTwoExecute, Option.bind_some]
    simp only [linearExecute, operationExecute, Option.bind_some]
  have firstThreeBounds := LinearPrefixBounds.append input _ _ before loaded H B firstTwoExecute firstTwoBounds operationBounds
  exact LinearPrefixBounds.append input _ _ before computed H B firstThreeExecute firstThreeBounds storeBounds

theorem ratBinarySlots_prefix_bounds (input : List Cell) (before : State)
    (left right target H B : ℕ) (operation : RatOp) (x y value : ℚ)
    (hbefore : StateBounds H B before) (fresh : before.register .fresh = .natural 0)
    (leftLive : left ∈ before.live) (rightLive : right ∈ before.live)
    (leftValue : before.heap left = .rational x) (rightValue : before.heap right = .rational y)
    (leftInside : left < H) (rightInside : right < H) (targetInside : target < H)
    (addressBits : 1 + natBits H ≤ B) (valueBits : (Cell.rational value).bits ≤ B)
    (evaluated : operation.eval x y = some value) :
    LinearPrefixBounds input (ratBinarySlots operation left right target) before H B := by
  apply binary_macro_prefix_bounds input before left right target H B
    (.ratOp operation .total .total .value) (.rational value) hbefore fresh leftLive rightLive
    leftInside rightInside targetInside addressBits valueBits
  apply PDMenu.ComputeFrame.execute_ratOp operation .total .total .value input _ x y value
  · simp [loadSlotResult, leftValue]
  · simp [loadSlotResult, rightValue]
  · exact evaluated

theorem natBinarySlots_prefix_bounds (input : List Cell) (before : State)
    (left right target H B : ℕ) (operation : NatOp) (x y value : ℕ)
    (hbefore : StateBounds H B before) (fresh : before.register .fresh = .natural 0)
    (leftLive : left ∈ before.live) (rightLive : right ∈ before.live)
    (leftValue : before.heap left = .natural x) (rightValue : before.heap right = .natural y)
    (leftInside : left < H) (rightInside : right < H) (targetInside : target < H)
    (addressBits : 1 + natBits H ≤ B) (valueBits : (Cell.natural value).bits ≤ B)
    (evaluated : operation.eval x y = some value) :
    LinearPrefixBounds input (natBinarySlots operation left right target) before H B := by
  apply binary_macro_prefix_bounds input before left right target H B
    (.natOp operation .total .total .value) (.natural value) hbefore fresh leftLive rightLive
    leftInside rightInside targetInside addressBits valueBits
  apply PDMenu.ComputeFrame.execute_natOp operation .total .total .value input _ x y value
  · simp [loadSlotResult, leftValue]
  · simp [loadSlotResult, rightValue]
  · exact evaluated

theorem natToRatSlot_prefix_bounds (input : List Cell) (before : State)
    (source target H B value : ℕ) (hbefore : StateBounds H B before)
    (fresh : before.register .fresh = .natural 0) (live : source ∈ before.live)
    (hvalue : before.heap source = .natural value) (sourceInside : source < H) (targetInside : target < H)
    (addressBits : 1 + natBits H ≤ B) (valueBits : (Cell.rational value).bits ≤ B) :
    LinearPrefixBounds input (natToRatSlot source target) before H B := by
  let loaded := loadSlotResult before 0 source .total
  let computed := ({loaded with pc := loaded.pc + 1}).set .total (.rational value)
  have loadedExecute : linearExecute input (loadSlot source .total) before = some loaded :=
    loadSlot_execute input before 0 source .total fresh (by simpa only [Nat.zero_add] using live)
  have loadedBounds := loadSlot_prefix_bounds input before source .total H B hbefore fresh live
    (address_cell_bits source H B sourceInside addressBits)
  have hl := loadedBounds.final loadedExecute
  have hc : StateBounds H B computed := (hl.with_pc _).set _ _ valueBits
  have converted : (Instruction.natToRat .total .total).execute input loaded = some computed :=
    PDMenu.ComputeFrame.execute_natToRat .total .total input loaded value (by simp [loaded, loadSlotResult, hvalue])
  have convertedBounds := single_prefix_bounds input (.natToRat .total .total) loaded computed H B hl hc converted
  have storeBounds := storeSlot_prefix_bounds input computed target .total H B hc
    (by simpa [computed, loaded, loadSlotResult, State.set] using fresh)
    targetInside (by decide) (address_cell_bits target H B targetInside addressBits)
  have convertedExecute : linearExecute input (loadSlot source .total ++ [.natToRat .total .total]) before = some computed := by
    rw [linearExecute_append, loadedExecute, Option.bind_some]
    simp only [linearExecute, converted, Option.bind_some]
  have firstBounds := LinearPrefixBounds.append input _ _ before loaded H B loadedExecute loadedBounds convertedBounds
  exact LinearPrefixBounds.append input _ _ before computed H B convertedExecute firstBounds storeBounds

end PDROC.D27Prepare.Resources
