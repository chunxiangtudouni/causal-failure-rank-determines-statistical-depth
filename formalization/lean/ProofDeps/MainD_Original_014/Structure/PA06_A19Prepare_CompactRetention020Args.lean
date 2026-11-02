module

public import Structure.PA06_A19Prepare_CompactRetention020PairCore
public import PaperProofs.Structure.RawCandidateRetentionWordSafety
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Compact retention ARGUMENT pieces, retaining their original source
counter qualifications. The real cardArguments and pairArguments blocks
write scratch1/2 and preserve the actual B16 cache/header cells. Only
short prefix bounds are generalized; no Nat scan or retention kernel is
rebuilt. afterCard/innerTail/finish pieces remain outside this partial
module until their ordinary source-cell interfaces are discharged. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactRetention020Args

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateRetentionRAM
open RawIncidenceScanSafety (NatAccessFits)
open RawCandidateRetentionWordChunks (Chunk chunkCode chunkLength chunkOffset)

abbrev linearLimit := PA06A19PrepareCompactWord008.linearLimit

private theorem fits_update {bits : Nat} {registers : Register → Nat}
    (hr : ∀ reg, Fits bits (registers reg)) (target : Register) (value : Nat) (hv : Fits bits value) :
    ∀ reg, Fits bits (Function.update registers target value reg) := by
  intro reg
  by_cases heq : reg = target
  · simpa only [heq, Function.update_self] using hv
  · simpa only [Function.update_of_ne heq] using hr reg

theorem cardArgs_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hr : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hi : state.heap (16 + 1) ≤ (full.length + q + 1))
    (count : Nat) (hc : count ≤ 10) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) (cardArguments.take count) state) := by
  have hlimit : Fits (indexWidth 32 full.length q) (linearLimit full.length q) :=
    PA06A19PrepareCompactArrays018.linearLimit_fits full.length q
  induction count with
  | zero => exact hr
  | succ count ih =>
    have hlt : count < 10 := by omega
    have hp := ih hlt.le
    rw [List.take_succ_eq_append_getElem (by change count < 10; exact hlt), runOps_append]
    change RegistersFit _ (natExecuteOp _ (cardArguments[count]'(by change count < 10; exact hlt)) _)
    interval_cases count <;>
      simp only [cardArguments, loadWorkspace, loadCell, storeCell, setCell, List.getElem_append,
        List.getElem_cons_zero, List.getElem_cons_succ, List.length_append, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
    all_goals first | exact hp | apply fits_update hp
    all_goals first
      | (apply lt_of_le_of_lt _ hlimit; unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega)
      | (simp_all [runOps, natExecuteOp, Op.execute, Instruction.execute];
          (apply lt_of_le_of_lt _ hlimit; unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega))

theorem pairArgs_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hr : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hi : state.heap (16 + 1) ≤ (full.length + q + 1))
    (hj : state.heap (16 + 2) ≤ (full.length + q + 1))
    (count : Nat) (hc : count ≤ 14) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) (pairArguments.take count) state) := by
  have hlimit : Fits (indexWidth 32 full.length q) (linearLimit full.length q) :=
    PA06A19PrepareCompactArrays018.linearLimit_fits full.length q
  have hnB2 : 16 + 2 ≠ 1 := by omega
  induction count with
  | zero => exact hr
  | succ count ih =>
    have hlt : count < 14 := by omega
    have hp := ih hlt.le
    rw [List.take_succ_eq_append_getElem (by change count < 14; exact hlt), runOps_append]
    change RegistersFit _ (natExecuteOp _ (pairArguments[count]'(by change count < 14; exact hlt)) _)
    interval_cases count <;>
      simp only [pairArguments, loadWorkspace, loadCell, storeCell, List.getElem_append,
        List.getElem_cons_zero, List.getElem_cons_succ, List.length_append, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
    all_goals first | exact hp | apply fits_update hp
    all_goals first
      | (apply lt_of_le_of_lt _ hlimit; unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega)
      | (simp_all [runOps, natExecuteOp, Op.execute, Instruction.execute];
          (apply lt_of_le_of_lt _ hlimit; unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega))

theorem cardArgs_prefix_access (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hptr : state.heap 8 = 16) (count : Nat) (hc : count < 10) :
    NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q)
      (runOps (rawIncidenceROM q full) (cardArguments.take count) state)
      (cardArguments.getD count RawCandidateRetentionRAM.paddingOp) := by
  have hlim : 8 < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  have haddr : 16 + 1 < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  interval_cases count <;>
    simp [cardArguments, loadWorkspace, loadCell, storeCell, setCell, runOps,
      natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits, hptr, hlim, haddr]
  all_goals omega

theorem pairArgs_prefix_access (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hptr : state.heap 8 = 16) (count : Nat) (hc : count < 14) :
    NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q)
      (runOps (rawIncidenceROM q full) (pairArguments.take count) state)
      (pairArguments.getD count RawCandidateRetentionRAM.paddingOp) := by
  have hlim : 8 < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  have haddr1 : 16 + 1 < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  have haddr2 : 16 + 2 < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  interval_cases count <;>
    simp [pairArguments, loadWorkspace, loadCell, storeCell, runOps,
      natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits, hptr, hlim, haddr1, haddr2]
  all_goals omega

inductive Piece where
  | initialize | outerTest | cardArgs | innerTest | pairArgs

def Piece.original : Piece → Chunk
  | .initialize => .initialize
  | .outerTest => .outerTest
  | .cardArgs => .cardArgs
  | .innerTest => .innerTest
  | .pairArgs => .pairArgs

def Needs (q : Nat) (full : List (Finset (Fin q))) (piece : Piece) (state : NatState) : Prop :=
  state.heap 8 = 16 ∧ match piece with
    | .initialize => True
    | .outerTest => state.heap 16 = full.length + q + 1 ∧ state.heap 17 ≤ full.length + q + 1
    | .cardArgs => state.heap 17 ≤ full.length + q + 1
    | .innerTest => state.heap 16 = full.length + q + 1 ∧ state.heap 18 ≤ full.length + q + 1
    | .pairArgs => state.heap 17 ≤ full.length + q + 1 ∧ state.heap 18 ≤ full.length + q + 1

theorem piece_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (start : Nat)
    (piece : Piece) (state : NatState) (hr : RegistersFit (indexWidth 32 full.length q) state)
    (needs : Needs q full piece state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 398)))
    (count : Nat) (hc : count ≤ chunkLength piece.original) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((chunkCode start piece.original).take count) state) := by
  cases piece with
  | «initialize» =>
    exact PA06A19PrepareCompactMacros014.set_prefix_fit q full 1 0 (by decide) state hr needs.1
      (PA06A19PrepareCompactMacros014.small_constant_fits _ _ 0 (by decide)) count hc
  | outerTest =>
    exact PA06A19PrepareCompactArrays018.counter_test_prefix_fit q full 1 (start + 398) (by decide)
      state hr needs.1 needs.2.1 needs.2.2 hend count hc
  | cardArgs => exact cardArgs_prefix_fit q full state hr needs.1 needs.2 count hc
  | innerTest =>
    exact PA06A19PrepareCompactArrays018.counter_test_prefix_fit q full 2 (start + 364) (by decide)
      state hr needs.1 needs.2.1 needs.2.2 (lt_of_le_of_lt (by omega) hend) count hc
  | pairArgs => exact pairArgs_prefix_fit q full state hr needs.1 needs.2.1 needs.2.2 count hc

theorem piece_prefix_access (q : Nat) (full : List (Finset (Fin q))) (start : Nat)
    (piece : Piece) (state : NatState) (needs : Needs q full piece state)
    (count : Nat) (hc : count < chunkLength piece.original) :
    NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q)
      (runOps (rawIncidenceROM q full) ((chunkCode start piece.original).take count) state)
      ((chunkCode start piece.original).getD count RawCandidateRetentionRAM.paddingOp) := by
  cases piece with
  | «initialize» => exact PA06A19PrepareCompactMacros014.set_prefix_access q full 1 0 (by decide) state needs.1 count hc
  | outerTest => exact PA06A19PrepareCompactMacros014.test_prefix_access q full 1 (start + 398) (by decide) state needs.1 count hc
  | cardArgs => exact cardArgs_prefix_access q full state needs.1 count hc
  | innerTest => exact PA06A19PrepareCompactMacros014.test_prefix_access q full 2 (start + 364) (by decide) state needs.1 count hc
  | pairArgs => exact pairArgs_prefix_access q full state needs.1 count hc

def SafePoint (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp)
    (start : Nat) (state : NatState) : Prop :=
  RegistersFit (indexWidth 32 full.length q) state ∧
    ∃ offset < 398, state.pc = 5 * (start + offset) ∧ state.halted = false ∧
      ∃ op, PackingOp.decode (natFetch containing state.pc) = some op ∧
        NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q) state op

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 398 ≤ containing.length)
  (hcode : ∀ position < 398, containing.getD (start + position) RawCandidateRetentionRAM.paddingOp =
    (programAt start).getD position RawCandidateRetentionRAM.paddingOp)

include hbound hcode

/-- Genuine retention code prefixes for the five currently covered pieces,
including the real test jump. The three data-update pieces remain separate. -/
theorem piece_safe (piece : Piece) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset piece.original)) (ha : state.halted = false)
    (hr : RegistersFit (indexWidth 32 full.length q) state) (needs : Needs q full piece state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 398))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (chunkLength piece.original) ∧
      RegistersFit (indexWidth 32 full.length q)
        (natRun (rawIncidenceROM q full) containing (chunkLength piece.original) state) := by
  constructor
  · intro count hc
    have run := RawCandidateRetentionWordChunks.chunk_run_prefix (rawIncidenceROM q full) containing start hbound hcode
      piece.original state hpc ha count hc.le
    have pc := RawCandidateRetentionWordSafety.chunk_run_pc q full containing start hbound hcode
      piece.original state hpc ha count hc
    have span := RawCandidateRetentionWordChunks.chunk_span piece.original
    refine ⟨?_, chunkOffset piece.original + count, by omega, ?_, ?_,
      (chunkCode start piece.original).getD count RawCandidateRetentionRAM.paddingOp, ?_, ?_⟩
    · rw [run]
      exact piece_prefix_fit q full start piece state hr needs hend count hc.le
    · rw [pc]
      omega
    · rw [run, runOps_halted, ha]
    · rw [pc, natFetch_body containing (start + chunkOffset piece.original + count) (by omega), decode_encode]
      have hh := (hcode (chunkOffset piece.original + count) (by omega)).trans
        (RawCandidateRetentionWordChunks.chunk_slice start piece.original count hc)
      rw [List.getD_eq_getElem _ RawCandidateRetentionRAM.paddingOp (by omega)] at hh
      simpa only [Nat.add_assoc] using congrArg some hh
    · rw [run]
      exact piece_prefix_access q full start piece state needs count hc
  · rw [RawCandidateRetentionWordChunks.chunk_run_prefix (rawIncidenceROM q full) containing start hbound hcode
      piece.original state hpc ha (chunkLength piece.original) le_rfl]
    exact piece_prefix_fit q full start piece state hr needs hend _ le_rfl

end Linked

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactRetention020Args


