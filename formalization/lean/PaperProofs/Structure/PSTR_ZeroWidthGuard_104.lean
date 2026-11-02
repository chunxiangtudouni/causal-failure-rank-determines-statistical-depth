module

public import PaperProofs.Structure.PSTR_BranchAccess_088
public import PaperProofs.Structure.PSTR_OriginalCountRoom_056

/-! Actual two-instruction dispatch after width/mask. The branch tests the
computed width register; target is a static code label. No raw-q answer is
reloaded or supplied. This component alone is not the uniform query. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRZeroWidthGuard

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open RawTreePreprocessingClaims PSTRWordSegments PSTRCountKernel

def lead (zeroTarget : Nat) : List PackingOp :=
  [.base (.base (.constant .address (5 * zeroTarget)))]

def program (zeroTarget : Nat) : List PackingOp := lead zeroTarget ++ [.jumpIfZero .total .address]

theorem lead_length (zeroTarget : Nat) : (lead zeroTarget).length = 1 := rfl
theorem program_length (zeroTarget : Nat) : (program zeroTarget).length = 2 := rfl
theorem program_branch (zeroTarget : Nat) :
    (program zeroTarget)[1]'(by rw [program_length]; decide) = .jumpIfZero .total .address := rfl
theorem lead_straight (zeroTarget : Nat) : StraightProgram (lead zeroTarget) := by
  simp [lead, StraightProgram, StraightOp]

theorem actual_run {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start zeroTarget : Nat)
    (slice : PSTROuterCountCode.BlockAt whole start (program zeroTarget))
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom whole 2 state = executeOps rom (program zeroTarget) state := by
  have bound : start + 2 ≤ whole.length := by
    have h := slice.bound
    rw [program_length] at h
    exact h
  rw [show 2 = (lead zeroTarget).length + 1 from rfl,
    segment_last rom whole (lead zeroTarget) (.jumpIfZero .total .address) start
      (by rw [lead_length]; omega) ?_ ?_ (lead_straight zeroTarget) hwords hpcfit state hp ha]
  · rw [program, executeOps_append]
    rfl
  · intro i hi
    exact (slice.code i (by rw [program_length]; rw [lead_length] at hi; omega)).trans (List.getElem_append_left hi)
  · simpa only [lead_length] using (slice.code 1 (by rw [program_length]; decide)).trans (program_branch zeroTarget)

theorem width_zero_iff {q : Nat} (full : List (Finset (Fin q)))
    (state : WordState (indexWidth 32 full.length q))
    (hw : state.register .total = BitVec.ofNat (indexWidth 32 full.length q) (CapacityBits.width q)) :
    (state.register .total).toNat = 0 ↔ q = 0 := by
  have hfit : Fits (indexWidth 32 full.length q) (CapacityBits.width q) :=
    (PA17PackingBounds043.width_le_bits full.length q).trans_lt
      (show indexWidth 32 full.length q < 2 ^ indexWidth 32 full.length q from Nat.lt_two_pow_self)
  rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit, CapacityBits.width_eq_zero_iff]

theorem actual_result {q : Nat} (full : List (Finset (Fin q))) (rom : PhysicalROM)
    (whole : List PackingOp) (start zeroTarget : Nat)
    (slice : PSTROuterCountCode.BlockAt whole start (program zeroTarget))
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (state : WordState (indexWidth 32 full.length q))
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length q) (5 * start)) (ha : state.halted = false)
    (hw : state.register .total = BitVec.ofNat (indexWidth 32 full.length q) (CapacityBits.width q)) :
    let after := packingRun rom whole 2 state
    after.halted = false ∧
      after.pc = (if q = 0 then BitVec.ofNat (indexWidth 32 full.length q) (5 * zeroTarget)
        else BitVec.ofNat (indexWidth 32 full.length q) (5 * (start + 2))) ∧
      after.heap = state.heap ∧
      (∀ register, register ≠ .address → after.register register = state.register register) := by
  have hz := width_zero_iff full state hw
  dsimp only
  rw [actual_run rom whole start zeroTarget slice hwords hpcfit state hp ha]
  have pc : 5 * start + 5 + 5 = 5 * (start + 2) := by omega
  refine ⟨ha, ?_, rfl, ?_⟩
  · simp +decide only [program, lead, List.cons_append, List.nil_append, executeOps, packingExecuteOp,
      wordOp, wordInstruction, Function.update_apply, ↓reduceIte, hp, BitVec.ofNat_add_ofNat, pc, hz]
  · intro register hr
    simp +decide only [program, lead, List.cons_append, List.nil_append, executeOps, packingExecuteOp,
      wordOp, wordInstruction, Function.update_apply, ite_eq_right hr]

theorem actual_safe {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (start zeroTarget heapWords : Nat)
    (slice : PSTROuterCountCode.BlockAt whole start (program zeroTarget))
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (clock : Nat) (hclock : clock < 2) :
    PSTRCountKernel.AtSafe rom whole heapWords (packingRun rom whole clock state) := by
  have safe : PrefixOK rom heapWords (fun _ => True) (lead zeroTarget) state := by
    apply readOnly_prefixOK
    · simp [lead, ReadOnly]
    · intro count hc
      have he : count = 0 := by rw [lead_length] at hc; omega
      subst count
      trivial
  apply (PSTRBranchAccess.branch_safe rom whole (lead zeroTarget) .total .address heapWords start (fun _ => True)
    (by have hh := slice.bound; rw [program_length] at hh; rw [lead_length]; omega)
    ?_ ?_ (lead_straight zeroTarget) hwords hpcfit state hp ha safe clock (by rw [lead_length]; omega)).1
  · intro i hi
    exact (slice.code i (by rw [program_length]; rw [lead_length] at hi; omega)).trans (List.getElem_append_left hi)
  · simpa only [lead_length] using (slice.code 1 (by rw [program_length]; decide)).trans (program_branch zeroTarget)

theorem prefix_heap {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start zeroTarget : Nat)
    (slice : PSTROuterCountCode.BlockAt whole start (program zeroTarget))
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (clock : Nat) (hclock : clock ≤ 2) : (packingRun rom whole clock state).heap = state.heap := by
  have cases : clock = 0 ∨ clock = 1 ∨ clock = 2 := by omega
  rcases cases with rfl | rfl | rfl
  · rfl
  · have run : packingRun rom whole 1 state = executeOps rom (lead zeroTarget) state := by
      apply straight_segment rom whole (lead zeroTarget) start
        (by have hh := slice.bound; rw [program_length] at hh; rw [lead_length]; omega)
        ?_ (lead_straight zeroTarget) hwords hpcfit state hp ha
      intro i hi
      exact (slice.code i (by rw [program_length]; rw [lead_length] at hi; omega)).trans (List.getElem_append_left hi)
    rw [run]
    rfl
  · rw [actual_run rom whole start zeroTarget slice hwords hpcfit state hp ha]
    rfl

end PaperProofs.Structure.LaminarTree.PSTRZeroWidthGuard
