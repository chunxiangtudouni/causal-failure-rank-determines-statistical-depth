module

public import Structure.PA06_A19Prepare_InitializedFront086_Checker
public import Structure.PA06_A19Prepare_InitializedFront086_Segments

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED ONE actual raw front witness: patched checker, its real
two-op dispatcher, then006 initializer16. The resulting Nat heap is the
genuine run from natInitial, not a periodic natView of a Word heap. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareInitializedFront086

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety RawTreePreprocessingClaims CompactControllerClaims

theorem initialized_front_nat (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (laminar : LaminarSchedule full) :
    ∃ clock ≤ checkerSteps full.length q + 17,
      PA06A19PrepareAfterGate081.Initialized q full
        (natRun (rawIncidenceROM q full) program clock natInitial) ∧
      PrefixSafe (Point q full) (rawIncidenceROM q full) program natInitial clock := by
  have actual := PA06A19PrepareEarlyGate079.patched_checker_boundary q full hq
    (5 * PA06A19PrepareAllQCode082.handlerStart) (PA06A19PrepareAllQCode082.oldP.drop 126)
  rw [patched_layout] at actual
  obtain ⟨checked, _lower, checkedBound, post⟩ := actual
  dsimp only at post
  rcases post with ⟨same, active, pc, _flagBound, correct, zero, samePrefix⟩
  let rom := rawIncidenceROM q full
  let boundary := natRun rom program checked natInitial
  have oldActive : (natRun rom checker checked natInitial).halted = false := by
    rw [← same]
    exact active
  have boundaryRegs : RegistersFit (bits q full) boundary := by
    dsimp only [boundary]
    rw [same]
    exact PA06A19PrepareCompactRetention030InitBounds.checker_active_registersFit q full checked oldActive
  have accepted : boundary.register .value = 1 := correct.mpr laminar
  have checkedPoints : PrefixSafe (Point q full) rom program natInitial checked := by
    intro count hc
    by_cases first : count < 17
    · exact first_point q full hq count first
    · rw [samePrefix count (by omega) hc.le]
      exact checker_point q full hq checked oldActive count (by omega) hc
  let entered := natRun rom program (checked + 2) natInitial
  have enterRun : entered = natRun rom program 2 boundary := natRun_add rom program checked 2 natInitial
  have enterEffect : entered =
      { boundary with register := Function.update boundary.register .index (5 * PA06A19PrepareAllQCode082.finalEnd), pc := 640 } := by
    rw [enterRun]
    exact gate_run rom boundary pc active accepted
  have enterPC : entered.pc = 640 := by rw [enterEffect]
  have enterActive : entered.halted = false := by rw [enterEffect]; exact active
  have enterHeap : entered.heap = boundary.heap := by rw [enterEffect]
  have enterRegs : RegistersFit (bits q full) entered := by
    rw [enterRun, gate_prefix_run rom boundary pc active 2 le_rfl]
    exact gate_registers q full boundary boundaryRegs 2 le_rfl
  have gatePoints : PrefixSafe (Point q full) rom program boundary 2 := by
    intro count hc
    exact gate_point q full boundary pc active boundaryRegs count hc
  have beforeInit := PrefixSafe.add (Point q full) rom program natInitial checked 2 checkedPoints gatePoints
  let clock := (checked + 2) + 16
  let prepared := natRun rom program clock natInitial
  have prepareRun : natRun rom program 16 entered = prepared :=
    (natRun_add rom program (checked + 2) 16 natInitial).symm
  have initialized := PA06A19PrepareCompactInit006.initialize_workspace q full program 128
    init_slice.1 init_slice.2 entered enterPC enterActive
  rw [prepareRun] at initialized
  have preparedRegs : RegistersFit (bits q full) prepared := by
    rw [← prepareRun, PA06A19PrepareCompactInit006.natRun_prefix_eq q full program 128
      init_slice.1 init_slice.2 entered enterPC enterActive 16 le_rfl]
    exact PA06A19PrepareCompactRetention030InitBounds.init_prefix_registersFit q full entered enterRegs 16 le_rfl
  have initPoints : PrefixSafe (Point q full) rom program entered 16 := by
    intro count hc
    exact init_point q full entered enterPC enterActive enterRegs count hc
  have wholePoints := PrefixSafe.add (Point q full) rom program natInitial (checked + 2) 16 beforeInit initPoints
  refine ⟨clock, by dsimp only [clock]; omega, ?_, wholePoints⟩
  refine ⟨preparedRegs, initialized.pc, initialized.active, initialized.base_cell, initialized.count_cell, ?_⟩
  intro address above different8 different16
  rw [initialized.heap_frame address different8 different16, enterHeap]
  exact zero address above

end PaperProofs.Structure.LaminarTree.PA06A19PrepareInitializedFront086
