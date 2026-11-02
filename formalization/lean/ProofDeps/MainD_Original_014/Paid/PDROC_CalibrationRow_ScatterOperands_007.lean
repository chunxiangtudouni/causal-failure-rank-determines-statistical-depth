module

public import Paid.PDROC_CalibrationRow_ScatterOperands_002
public import Paid.PDROC_CalibrationRow_ScatterOperands_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CalibrationRow.ScatterOperands

open PaperProofs.Paid.Computation PDLower.CalibrationCompute

theorem boundary_prefix_sources (input : List Cell) (before after : State)
    (base cursor width count : ℕ) (New : Cell → Prop)
    (fresh : before.register .fresh = .natural base)
    (live : base + 8 ∈ before.live) (widthValue : before.heap (base + 8) = .natural width)
    (index : before.register .index = .natural cursor)
    (offsetSource : New (.natural 8)) (addressSource : New (.natural (base + 8)))
    (naturals : ∀ number ≤ max width 2, New (.natural number)) (bound : count ≤ 9)
    (executed : linearExecute input (boundaryCode.take count) before = some after) :
    Sources before after New := by
  let loaded := loadSlotResult before base 8 .total
  let one := ({loaded with pc := loaded.pc + 1}).set .flag (.natural 1)
  let last := ({one with pc := one.pc + 1}).set .total (.natural (width - 1))
  let zero := ({last with pc := last.pc + 1}).set .old (.natural 0)
  let left := ({zero with pc := zero.pc + 1}).set .flag (.natural (if cursor = 0 then 1 else 0))
  let right := ({left with pc := left.pc + 1}).set .old (.natural (if cursor = width - 1 then 1 else 0))
  have small : 2 ≤ max width 2 := Nat.le_max_right _ _
  have loadedSource : Sources before loaded New := loadSlotResult_sources before base 8 .total New
    addressSource (by rw [widthValue]; exact naturals width (Nat.le_max_left _ _))
  have oneSource : Sources before one New := loadedSource.trans
    ((Sources.set loaded New .flag _ (naturals 1 (by omega))).withPC (loaded.pc + 1))
  have lastSource : Sources before last New := oneSource.trans
    ((Sources.set one New .total _ (naturals (width - 1) (by omega))).withPC (one.pc + 1))
  have zeroSource : Sources before zero New := lastSource.trans
    ((Sources.set last New .old _ (naturals 0 (Nat.zero_le _))).withPC (last.pc + 1))
  have leftSource : Sources before left New := zeroSource.trans
    ((Sources.set zero New .flag _ (naturals _ (by split_ifs <;> omega))).withPC (zero.pc + 1))
  have rightSource : Sources before right New := leftSource.trans
    ((Sources.set left New .old _ (naturals _ (by split_ifs <;> omega))).withPC (left.pc + 1))
  have finalSource : Sources before (boundaryResult before base cursor width) New := rightSource.trans
    ((Sources.set right New .flag _ (naturals _ (by unfold boundaryFlag; split_ifs <;> omega))).withPC (right.pc + 1))
  by_cases short : count ≤ 3
  · have shortLength : count ≤ (loadSlot 8 .total).length := short
    rw [boundaryCode, List.take_append_of_le_length shortLength] at executed
    exact loadSlot_prefix_sources input before after base 8 count .total New fresh live
      offsetSource addressSource (by rw [widthValue]; exact naturals width (Nat.le_max_left _ _)) short executed
  · have loadRun : linearExecute input (loadSlot 8 .total) before = some loaded :=
      loadSlot_execute input before base 8 .total fresh live
    have oneRun : (Instruction.constant .flag (.natural 1)).execute input loaded = some one := rfl
    have lastRun : (Instruction.natOp .subtract .total .total .flag).execute input one = some last := by
      simp [Instruction.execute, one, loaded, loadSlotResult, State.set, widthValue, Cell.nat?, NatOp.eval, last]
    have zeroRun : (Instruction.constant .old (.natural 0)).execute input last = some zero := rfl
    have leftRun : (Instruction.natCompare .equal .flag .index .old).execute input zero = some left := by
      simp [Instruction.execute, zero, last, one, loaded, loadSlotResult, State.set, index, Cell.nat?, Comparison.nat, left]
    have rightRun : (Instruction.natCompare .equal .old .index .total).execute input left = some right := by
      simp [Instruction.execute, left, zero, last, one, loaded, loadSlotResult, State.set,
        index, widthValue, Cell.nat?, Comparison.nat, right]
    have lower : 4 ≤ count := by omega
    interval_cases count
    · have run : linearExecute input (boundaryCode.take 4) before = some one := by
        change linearExecute input (loadSlot 8 .total ++ [.constant .flag (.natural 1)]) before = some one
        rw [linearExecute_append, loadRun, Option.bind_some]
        simp only [linearExecute, oneRun, Option.bind_some]
      have same := Option.some.inj (run.symm.trans executed)
      subst after
      exact oneSource
    · have run : linearExecute input (boundaryCode.take 5) before = some last := by
        change linearExecute input (loadSlot 8 .total ++
          [.constant .flag (.natural 1), .natOp .subtract .total .total .flag]) before = some last
        rw [linearExecute_append, loadRun, Option.bind_some]
        simp only [linearExecute, oneRun, lastRun, Option.bind_some]
      have same := Option.some.inj (run.symm.trans executed)
      subst after
      exact lastSource
    · have run : linearExecute input (boundaryCode.take 6) before = some zero := by
        change linearExecute input (loadSlot 8 .total ++
          [.constant .flag (.natural 1), .natOp .subtract .total .total .flag, .constant .old (.natural 0)]) before = some zero
        rw [linearExecute_append, loadRun, Option.bind_some]
        simp only [linearExecute, oneRun, lastRun, zeroRun, Option.bind_some]
      have same := Option.some.inj (run.symm.trans executed)
      subst after
      exact zeroSource
    · have run : linearExecute input (boundaryCode.take 7) before = some left := by
        change linearExecute input (loadSlot 8 .total ++
          [.constant .flag (.natural 1), .natOp .subtract .total .total .flag, .constant .old (.natural 0),
            .natCompare .equal .flag .index .old]) before = some left
        rw [linearExecute_append, loadRun, Option.bind_some]
        simp only [linearExecute, oneRun, lastRun, zeroRun, leftRun, Option.bind_some]
      have same := Option.some.inj (run.symm.trans executed)
      subst after
      exact leftSource
    · have run : linearExecute input (boundaryCode.take 8) before = some right := by
        change linearExecute input (loadSlot 8 .total ++
          [.constant .flag (.natural 1), .natOp .subtract .total .total .flag, .constant .old (.natural 0),
            .natCompare .equal .flag .index .old, .natCompare .equal .old .index .total]) before = some right
        rw [linearExecute_append, loadRun, Option.bind_some]
        simp only [linearExecute, oneRun, lastRun, zeroRun, leftRun, rightRun, Option.bind_some]
      have same := Option.some.inj (run.symm.trans executed)
      subst after
      exact rightSource
    · change linearExecute input boundaryCode before = some after at executed
      rw [boundary_execute input before base cursor width fresh live widthValue index] at executed
      have same := Option.some.inj executed
      subst after
      exact finalSource

end PDROC.CalibrationRow.ScatterOperands
