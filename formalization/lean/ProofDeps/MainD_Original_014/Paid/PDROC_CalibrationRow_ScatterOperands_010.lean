module

public import Paid.PDROC_CalibrationRow_ScatterOperands_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDROC.CalibrationRow.ScatterOperands

open PaperProofs.Paid.Computation PDLower.CalibrationCompute

theorem interior_prefix_sources (input : List Cell) (before after : State)
    (right : Bool) (cursor count : ℕ) (New : Cell → Prop)
    (index : before.register .index = .natural cursor)
    (one : New (.natural 1))
    (target : New (.natural (if right then cursor + 1 else cursor - 1)))
    (bound : count ≤ 2)
    (executed : linearExecute input ((interiorCode right).take count) before = some after) :
    Sources before after New := by
  let first := ({before with pc := before.pc + 1}).set .flag (.natural 1)
  have firstSource : Sources before first New :=
    (Sources.set before New .flag _ one).withPC (before.pc + 1)
  have finalSource : Sources before (interiorResult before right cursor) New :=
    firstSource.trans ((Sources.set first New .index _ target).withPC (first.pc + 1))
  interval_cases count
  · have same : before = after := Option.some.inj executed
    subst after
    exact Sources.refl before New
  · have run : linearExecute input ((interiorCode right).take 1) before = some first := rfl
    have same := Option.some.inj (run.symm.trans executed)
    subst after
    exact firstSource
  · change linearExecute input (interiorCode right) before = some after at executed
    rw [interior_execute input before right cursor index] at executed
    have same := Option.some.inj executed
    subst after
    exact finalSource

end PDROC.CalibrationRow.ScatterOperands
