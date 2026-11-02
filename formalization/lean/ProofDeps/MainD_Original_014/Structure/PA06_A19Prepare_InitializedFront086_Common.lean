module

public import Structure.PA06_A19Prepare_AllQCode082
public import Structure.PA06_A19Prepare_PositiveFront084_Word
public import Structure.PA06_A19Prepare_EarlyGate079_CheckerBoundary
public import Structure.PA06_A19Prepare_CompactRetention030InitBounds
public import Structure.PA06_A19Prepare_AfterGate081_Control

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED local vocabulary and actual source slices for the ONE082
checker/dispatcher/initializer front. No state or table answer is input. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareInitializedFront086

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety RawTreePreprocessingClaims CompactControllerClaims

abbrev program := PA06A19PrepareAllQCode082.program
abbrev bits (q : Nat) (full : List (Finset (Fin q))) := indexWidth 32 full.length q
abbrev allocation (q : Nat) (full : List (Finset (Fin q))) := PA06A19PreparePreBuild044.allocation q full
def wordLimit (q : Nat) (full : List (Finset (Fin q))) : Nat := 2 ^ bits q full - 1

def Point (q : Nat) (full : List (Finset (Fin q))) (state : NatState) : Prop :=
  RegistersFit (bits q full) state ∧ Fits (bits q full) state.pc ∧ state.halted = false ∧
    ∃ (index : Nat) (hi : index < program.length), state.pc = 5 * index ∧
      NatAccessFits (rawIncidenceROM q full) (allocation q full) state program[index]

theorem program_room : 144 ≤ program.length := by
  change 144 ≤ PA06A19PrepareAllQCode082.program.length
  rw [← PA06A19PrepareAllQCode082.program_layout]
  simp only [List.length_append, PA06A19PrepareAllQCode082.patchedPrefix_length]
  omega

theorem patched_layout :
    PA06A19PrepareEarlyGate079.program (5 * PA06A19PrepareAllQCode082.handlerStart)
      (checker ++ PA06A19PrepareAllQCode082.oldP.drop 126) = program := by
  rw [← PA06A19PrepareAllQCode082.oldP_checker]
  rfl

theorem positive_layout :
    PA06A19PreparePositiveFront084.code (5 * PA06A19PrepareAllQCode082.handlerStart)
      (PA06A19PrepareAllQCode082.oldP.drop 126) = program := patched_layout

theorem allocation_room (q : Nat) (full : List (Finset (Fin q))) : 17 ≤ allocation q full := by
  change 17 ≤ 4 + packedCapacityWords q
    (capacityWords 8192 full.length q (treeSize q full)) (bits q full) +
      8192 * (full.length + q + treeSize q full + 1)
  omega

theorem limit_fits (q : Nat) (full : List (Finset (Fin q))) : Fits (bits q full) (wordLimit q full) := by
  have positive : 0 < 2 ^ bits q full := pow_pos (by decide) _
  unfold Fits wordLimit
  omega

theorem limit_small (q : Nat) (full : List (Finset (Fin q))) : 640 ≤ wordLimit q full := by
  have powers : 2 ^ 32 ≤ 2 ^ bits q full := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    (PSTRBuildLower.CounterInit.selected_width_room full.length q)
  have literal : 641 ≤ 2 ^ 32 := by decide
  unfold wordLimit
  omega

theorem dimensions_fit (q : Nat) (full : List (Finset (Fin q))) :
    Fits (bits q full) full.length ∧ Fits (bits q full) q := by
  have mass := PA06A19PrepareCompactWord008.fits_width32_of_width16 full.length q _
    (RawCandidateWorkspaceInit.candidateCount_fits full.length q)
  constructor
  · exact (show full.length ≤ RawCandidateWorkspaceInit.candidateCount full.length q by
      unfold RawCandidateWorkspaceInit.candidateCount; omega).trans_lt mass
  · exact (show q ≤ RawCandidateWorkspaceInit.candidateCount full.length q by
      unfold RawCandidateWorkspaceInit.candidateCount; omega).trans_lt mass

theorem handler_fit (q : Nat) (full : List (Finset (Fin q))) :
    Fits (bits q full) (5 * PA06A19PrepareAllQCode082.handlerStart) := by
  have endpoint := PA06A19PrepareAllQCode082.selected_pc_room full.length q
  rw [PA06A19PrepareAllQCode082.program_length] at endpoint
  apply lt_of_le_of_lt _ endpoint
  unfold PA06A19PrepareAllQCode082.finalEnd
  omega

theorem access_mono (rom : PhysicalROM) (small large : Nat) (state : NatState) (op : PackingOp)
    (room : small ≤ large) (access : NatAccessFits rom small state op) : NatAccessFits rom large state op := by
  cases op with
  | base op =>
    cases op with
    | subtract target left right => trivial
    | base instruction =>
      cases instruction <;> simp only [NatAccessFits, AccessFits] at access ⊢
      all_goals first | exact access | exact access.trans_le room
  | arithmetic operation target left right => trivial
  | jumpIfZero condition target => trivial

/-- Active later execution forces the SAME actual earlier run to be active. -/
theorem active_before (rom : PhysicalROM) (code : List PackingOp) (initial : NatState)
    (last : Nat) (active : (natRun rom code last initial).halted = false)
    (count : Nat) (bound : count ≤ last) : (natRun rom code count initial).halted = false := by
  cases stopped : (natRun rom code count initial).halted
  · rfl
  · have same := natRun_after_halt rom code initial count stopped (last - count)
    have clock : count + (last - count) = last := Nat.add_sub_of_le bound
    rw [clock] at same
    have contradiction := congrArg NatState.halted same
    rw [active, stopped] at contradiction
    cases contradiction

theorem checker_slot (index : Nat) (lower : 10 ≤ index) (upper : index < 126) :
    program[index]'(by have room := program_room; omega) = checker[index]'(by rw [checker_length]; exact upper) := by
  have oldRoom : index < PA06A19PrepareAllQCode082.oldP.length := by
    have room := program_room
    rw [PA06A19PrepareAllQCode082.program_length] at room
    rw [PA06A19PrepareAllQCode082.oldP_length]
    omega
  calc
    _ = PA06A19PrepareAllQCode082.oldP[index] :=
      PA06A19PrepareEarlyGate079.slot_after_ten _ _ index lower oldRoom
    _ = checker[index] := by
      rw [List.getElem_of_eq PA06A19PrepareAllQCode082.oldP_checker oldRoom]
      exact List.getElem_append_left (by rw [checker_length]; exact upper)

def gate : List PackingOp :=
  [.base (.base (.constant .index (5 * PA06A19PrepareAllQCode082.finalEnd))), .jumpIfZero .value .index]

private theorem slot_of_slice (code block : List PackingOp) (start size offset : Nat)
    (slice : (code.drop start).take size = block)
    (codeBound : start + offset < code.length) (blockBound : offset < block.length) :
    code[start + offset] = block[offset] := by
  have member : offset < ((code.drop start).take size).length := by
    rw [slice]
    exact blockBound
  have value := List.getElem_of_eq slice member
  simpa only [List.getElem_take, List.getElem_drop] using value

theorem gate_slot (offset : Nat) (bound : offset < 2) :
    program[126 + offset]'(by have room := program_room; omega) =
      gate[offset]'(by change offset < 2; exact bound) := by
  have slice : (program.drop 126).take 2 = gate := PA06A19PrepareAllQCode082.dispatcher_slice
  exact slot_of_slice program gate 126 2 offset slice
    (by have room := program_room; omega) (by change offset < 2; exact bound)

theorem init_slice : 128 + 16 ≤ program.length ∧
    ∀ position < 16, program.getD (128 + position) PA06A19PrepareCompactInit006.paddingOp =
      PA06A19PrepareCompactInit006.initProgram.getD position PA06A19PrepareCompactInit006.paddingOp := by
  refine ⟨program_room, ?_⟩
  intro position bound
  interval_cases position <;> rfl

end PaperProofs.Structure.LaminarTree.PA06A19PrepareInitializedFront086
