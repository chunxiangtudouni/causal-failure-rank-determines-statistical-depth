module

public import Paid.PDROC_CalibrationRow_ScatterOperands_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow.ScatterOperands

open PaperProofs.Paid.Computation PDLower.CalibrationCompute

theorem loadSlotResult_sources (before : State) (base slot : ℕ) (target : Register) (New : Cell → Prop)
    (address : New (.natural (base + slot))) (loaded : New (before.heap (base + slot))) :
    Sources before (loadSlotResult before base slot target) New := by
  let addressed := before.set .address (.natural (base + slot))
  have first : Sources before addressed New := Sources.set before New .address _ address
  have last := Sources.set addressed New target (before.heap (base + slot)) loaded
  simpa only [addressed, loadSlotResult, State.set] using (first.trans last).withPC (before.pc + 3)

/-- Exact SSA for the original three opcodes. This supplies provenance
alongside frozen RootD27.Bits.loadSlot_prefix_safe; it does not duplicate
that lemma's complete-state bit calculation. -/
theorem loadSlot_prefix_sources (input : List Cell) (before after : State)
    (base slot count : ℕ) (target : Register) (New : Cell → Prop)
    (fresh : before.register .fresh = .natural base) (live : base + slot ∈ before.live)
    (offsetSource : New (.natural slot)) (addressSource : New (.natural (base + slot)))
    (loadedSource : New (before.heap (base + slot))) (bound : count ≤ 3)
    (executed : linearExecute input ((loadSlot slot target).take count) before = some after) :
    Sources before after New := by
  let first := ({before with pc := before.pc + 1}).set .address (.natural slot)
  let second := ({first with pc := first.pc + 1}).set .address (.natural (base + slot))
  have firstSource : Sources before first New :=
    (Sources.set before New .address _ offsetSource).withPC (before.pc + 1)
  have secondSource : Sources before second New := firstSource.trans
    ((Sources.set first New .address _ addressSource).withPC (first.pc + 1))
  interval_cases count
  · have same : before = after := Option.some.inj executed
    subst after
    exact Sources.refl before New
  · have run : linearExecute input ((loadSlot slot target).take 1) before = some first := rfl
    have same := Option.some.inj (run.symm.trans executed)
    subst after
    exact firstSource
  · have run : linearExecute input ((loadSlot slot target).take 2) before = some second := by
      simp [loadSlot, linearExecute, Instruction.execute, first, second, State.set,
        fresh, Cell.nat?, NatOp.eval, Nat.add_assoc]
    have same := Option.some.inj (run.symm.trans executed)
    subst after
    exact secondSource
  · change linearExecute input (loadSlot slot target) before = some after at executed
    rw [loadSlot_execute input before base slot target fresh live] at executed
    have same := Option.some.inj executed
    subst after
    exact loadSlotResult_sources before base slot target New addressSource loadedSource

end PDROC.CalibrationRow.ScatterOperands
