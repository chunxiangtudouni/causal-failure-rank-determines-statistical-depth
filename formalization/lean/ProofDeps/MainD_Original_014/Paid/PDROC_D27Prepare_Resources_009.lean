module

public import Paid.PDROC_D27Prepare_Resources_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute
open PDROC.D27Prepare.Program

namespace PDROC.D27Prepare.Resources

theorem initial_bounds (H B : ℕ) (enough : 2 ≤ B) : StateBounds H B initial := by
  constructor
  · simp only [initial, Finset.empty_subset]
  · intro register
    simpa only [initial, Cell.bits, natBits, Nat.log2_zero, Nat.reduceAdd] using enough
  · intro address live
    exact (Finset.notMem_empty address live).elim
  · intro cell member
    simp only [initial, List.not_mem_nil] at member

theorem jump_prefix_bounds (input : List Cell) (before : State) (target H B : ℕ)
    (hbefore : StateBounds H B before) : LinearPrefixBounds input [.jump target] before H B :=
  single_prefix_bounds input _ before _ H B hbefore (hbefore.with_pc target) rfl

theorem branch_prefix_bounds (input : List Cell) (before : State)
    (condition : Register) (zeroPC nonzeroPC value H B : ℕ)
    (hbefore : StateBounds H B before) (flag : before.register condition = .natural value) :
    LinearPrefixBounds input [.branchZero condition zeroPC nonzeroPC] before H B :=
  single_prefix_bounds input _ before _ H B hbefore (hbefore.with_pc _)
    (PDMenu.ComputeFrame.execute_branchZero condition zeroPC nonzeroPC input before value flag)

theorem inputSlot_prefix_bounds (input : List Cell) (before : State) (offset H B : ℕ)
    (value : Cell) (hbefore : StateBounds H B before) (fresh : before.register .fresh = .natural 0)
    (inside : offset < H) (addressBits : 1 + natBits H ≤ B)
    (fetched : input[offset]? = some value) (valueBits : value.bits ≤ B) :
    LinearPrefixBounds input (inputSlot offset) before H B := by
  let first := ({before with pc := before.pc + 1}).set .address (.natural offset)
  let second := ({first with pc := first.pc + 1}).set .total value
  have hf : StateBounds H B first := (hbefore.with_pc _).set _ _ (address_cell_bits offset H B inside addressBits)
  have hs : StateBounds H B second := (hf.with_pc _).set _ _ valueBits
  have loaded : (Instruction.loadInput .total .address).execute input first = some second :=
    PDMenu.ComputeFrame.execute_loadInput .total .address input first offset value
      (by simp [first, State.set]) fetched
  have firstBounds : LinearPrefixBounds input [.constant .address (.natural offset), .loadInput .total .address] before H B :=
    LinearPrefixBounds.cons input _ _ before first H B hbefore rfl
      (single_prefix_bounds input _ first second H B hf hs loaded)
  have firstExecute : linearExecute input [.constant .address (.natural offset), .loadInput .total .address] before = some second := by
    change ((Instruction.loadInput .total .address).execute input first).bind (linearExecute input []) = some second
    simp only [loaded, Option.bind_some, linearExecute]
  have storeBounds := storeSlot_prefix_bounds input second offset .total H B hs
    (by simpa [second, first, State.set] using fresh) inside (by decide)
    (address_cell_bits offset H B inside addressBits)
  exact LinearPrefixBounds.append input _ _ before second H B firstExecute firstBounds storeBounds

theorem binary_read_prefix_bounds (input : List Cell) (before : State)
    (left right H B : ℕ) (instruction : Instruction) (target : Register) (value : Cell)
    (hbefore : StateBounds H B before) (fresh : before.register .fresh = .natural 0)
    (leftLive : left ∈ before.live) (rightLive : right ∈ before.live)
    (leftInside : left < H) (rightInside : right < H)
    (addressBits : 1 + natBits H ≤ B) (valueBits : value.bits ≤ B)
    (operation : let loaded := loadSlotResult (loadSlotResult before 0 left .total) 0 right .value
      instruction.execute input loaded = some (({loaded with pc := loaded.pc + 1}).set target value)) :
    LinearPrefixBounds input (loadSlot left .total ++ loadSlot right .value ++ [instruction]) before H B := by
  let first := loadSlotResult before 0 left .total
  let loaded := loadSlotResult first 0 right .value
  let computed := ({loaded with pc := loaded.pc + 1}).set target value
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
  have firstTwoExecute : linearExecute input (loadSlot left .total ++ loadSlot right .value) before = some loaded := by
    rw [linearExecute_append, firstExecute, Option.bind_some, secondExecute]
  have firstTwoBounds := LinearPrefixBounds.append input _ _ before first H B firstExecute firstBounds secondBounds
  exact LinearPrefixBounds.append input _ _ before loaded H B firstTwoExecute firstTwoBounds operationBounds

theorem comparison_value_bits (value : Bool) (B : ℕ) (enough : 2 ≤ B) :
    (Cell.natural (if value then 1 else 0)).bits ≤ B := by
  cases value <;> simpa [Cell.bits, natBits] using enough

theorem natCompareSlots_prefix_bounds (input : List Cell) (before : State)
    (left right H B : ℕ) (comparison : Comparison) (x y : ℕ)
    (hbefore : StateBounds H B before) (fresh : before.register .fresh = .natural 0)
    (leftLive : left ∈ before.live) (rightLive : right ∈ before.live)
    (leftValue : before.heap left = .natural x) (rightValue : before.heap right = .natural y)
    (leftInside : left < H) (rightInside : right < H)
    (addressBits : 1 + natBits H ≤ B) (enough : 2 ≤ B) :
    LinearPrefixBounds input (natCompareSlots comparison left right) before H B := by
  apply binary_read_prefix_bounds input before left right H B
    (.natCompare comparison .flag .total .value) .flag (.natural (if comparison.nat x y then 1 else 0))
    hbefore fresh leftLive rightLive leftInside rightInside addressBits
    (comparison_value_bits _ B enough)
  apply PDMenu.ComputeFrame.execute_natCompare comparison .flag .total .value input _ x y
  · simp [loadSlotResult, leftValue]
  · simp [loadSlotResult, rightValue]

theorem ratCompareSlots_prefix_bounds (input : List Cell) (before : State)
    (left right H B : ℕ) (comparison : Comparison) (x y : ℚ)
    (hbefore : StateBounds H B before) (fresh : before.register .fresh = .natural 0)
    (leftLive : left ∈ before.live) (rightLive : right ∈ before.live)
    (leftValue : before.heap left = .rational x) (rightValue : before.heap right = .rational y)
    (leftInside : left < H) (rightInside : right < H)
    (addressBits : 1 + natBits H ≤ B) (enough : 2 ≤ B) :
    LinearPrefixBounds input (ratCompareSlots comparison left right) before H B := by
  apply binary_read_prefix_bounds input before left right H B
    (.ratCompare comparison .flag .total .value) .flag (.natural (if comparison.rat x y then 1 else 0))
    hbefore fresh leftLive rightLive leftInside rightInside addressBits
    (comparison_value_bits _ B enough)
  apply PDMenu.ComputeFrame.execute_ratCompare comparison .flag .total .value input _ x y
  · simp [loadSlotResult, leftValue]
  · simp [loadSlotResult, rightValue]

/-- A real page's final jump changes only pc. The fetch/chain/length
proof remains supplied by the actual page trace theorem. -/
theorem page_trace_bounds (input : List Cell) (body : List Instruction)
    (before terminal after : State) (target H B : ℕ) (trace : List State)
    (bounded : LinearPrefixBounds input body before H B)
    (executed : linearExecute input body before = some terminal)
    (finalState : after = {terminal with pc := target})
    (members : ∀ state ∈ trace, state = after ∨ ∃ count ≤ body.length,
      linearExecute input (body.take count) before = some state) :
    ∀ state ∈ trace, StateBounds H B state := by
  intro state member
  rcases members state member with same | earlier
  · subst state
    rw [finalState]
    exact (bounded.final executed).with_pc target
  · obtain ⟨count, _, actual⟩ := earlier
    exact bounded count state actual

end PDROC.D27Prepare.Resources
