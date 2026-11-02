module

public import Structure.PA06_A19Prepare_InitializedFront086_Common

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED prefix qualification of this actual patched checker.
Only the boundary's one supplied actual clock is used; an independently
selected old initialization endpoint is never joined to it. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareInitializedFront086

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety RawTreePreprocessingClaims CompactControllerClaims

theorem first_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    PA17UniformGenerator035m.RunSafe (wordLimit q full) (allocation q full)
      (rawIncidenceROM q full) program 17 natInitial := by
  have dimensions := dimensions_fit q full
  have handler := handler_fit q full
  have boundN : full.length ≤ wordLimit q full := by unfold Fits at dimensions; unfold wordLimit; omega
  have boundQ : q ≤ wordLimit q full := by unfold Fits at dimensions; unfold wordLimit; omega
  have boundHandler : 5 * PA06A19PrepareAllQCode082.handlerStart ≤ wordLimit q full := by
    unfold Fits at handler
    unfold wordLimit
    omega
  have actual := PA06A19PreparePositiveFront084.run_safe (rawIncidenceROM q full)
    full.length q (5 * PA06A19PrepareAllQCode082.handlerStart) (wordLimit q full) (allocation q full)
    (PA06A19PrepareAllQCode082.oldP.drop 126) (raw_header_N q full) (raw_header_q q full)
    hq (limit_small q full) boundN boundQ boundHandler
    (by
      change 2 ≤ ((rawIncidenceROM q full).words .input).length
      rw [raw_input_length]
      omega) (by have room := allocation_room q full; omega)
  rw [positive_layout] at actual
  exact actual

private theorem point_of_safe_local (width B H steps count : Nat) (rom : PhysicalROM)
    (code : List PackingOp) (before : NatState)
    (safe : PA17UniformGenerator035m.RunSafe B H rom code steps before)
    (limitFit : Fits width B) (pcFit : Fits width (5 * code.length)) (bound : count < steps) :
    let state := natRun rom code count before
    RegistersFit width state ∧ Fits width state.pc ∧ state.halted = false ∧
      ∃ (index : Nat) (hi : index < code.length), state.pc = 5 * index ∧
        NatAccessFits rom H state code[index] := by
  have state := safe.1 count bound.le
  obtain ⟨index, hi, pc, access⟩ := safe.2 count bound
  refine ⟨PA17UniformGenerator035p.registersFit_of_le _ _ _ limitFit state.1,
    ?_, state.2.1, index, hi, pc, access⟩
  rw [pc]
  exact (Nat.mul_le_mul_left 5 hi.le).trans_lt pcFit

theorem first_point (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (count : Nat) (bound : count < 17) :
    Point q full (natRun (rawIncidenceROM q full) program count natInitial) := by
  simpa only [Point] using
    (point_of_safe_local (bits q full) (wordLimit q full) (allocation q full) 17 count
      (rawIncidenceROM q full) PA06A19PrepareAllQCode082.program natInitial
      (first_safe q full hq) (limit_fits q full)
      (PA06A19PrepareAllQCode082.selected_pc_room full.length q) bound)

/-- Safety at a GIVEN old checker count strictly before the GIVEN active
boundary. Internal safe-halt facts only qualify that count, never select
an execution endpoint to concatenate with the patched run. -/
theorem checker_point (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (last : Nat) (activeLast : (natRun (rawIncidenceROM q full) checker last natInitial).halted = false)
    (count : Nat) (lower : 17 ≤ count) (upper : count < last) :
    Point q full (natRun (rawIncidenceROM q full) checker count natInitial) := by
  let rom := rawIncidenceROM q full
  let state := natRun rom checker count natInitial
  have active : state.halted = false := active_before rom checker natInitial last activeLast count upper.le
  have initial := PA06A19PrepareEarlyGate079.above_head_of_seventeen_pc full.length _
    (PA06A19PrepareEarlyGate079.old_control_seventeen rom full.length q
      (5 * PA06A19PrepareAllQCode082.handlerStart) (raw_header_N q full) (raw_header_q q full) hq).1
  have window := PA06A19PrepareEarlyGate079.above_head_run rom _ initial (count - 17)
  have shifted : natRun rom checker (count - 17) (natRun rom checker 17 natInitial) = state := by
    rw [← natRun_add, Nat.add_sub_of_le lower]
  rw [shifted] at window
  obtain ⟨index, lo, hi, control⟩ := window
  have strict : index < 126 := by
    by_contra notStrict
    have lastIndex : index = 126 := by omega
    have pc : state.pc = 5 * checker.length := by
      simpa only [lastIndex, checker_length] using control.1
    have nextActive := active_before rom checker natInitial last activeLast (count + 1) (by omega)
    have nextStopped : (natRun rom checker (count + 1) natInitial).halted = true := by
      rw [natRun_succ, natStep_halt rom checker state pc active]
    rw [nextStopped] at nextActive
    cases nextActive
  have point := PA06A19PrepareCompactRetention030InitBounds.checker_active_point q full count active
  have registers := PA06A19PrepareCompactRetention030InitBounds.checker_active_registersFit q full count active
  have pcFit := PA06A19PrepareCompactWord008.fits_width32_of_width16 full.length q _
    (safePoint_pcFit q full state point)
  obtain ⟨_oldIndex, _oldBound, _oldPC, guard⟩ := point.2.2
  have access : NatAccessFits rom 8 state (checker[index]'(by rw [checker_length]; exact strict)) := by
    have guarded := guard active
    rw [control.1, natFetch_body checker index (by rw [checker_length]; exact strict), decode_encode] at guarded
    exact guarded
  refine ⟨registers, pcFit, active, index, by have room := program_room; omega, control.1, ?_⟩
  rw [checker_slot index lo strict]
  exact access_mono rom 8 (allocation q full) state _
    (by have room := allocation_room q full; omega) access

end PaperProofs.Structure.LaminarTree.PA06A19PrepareInitializedFront086
