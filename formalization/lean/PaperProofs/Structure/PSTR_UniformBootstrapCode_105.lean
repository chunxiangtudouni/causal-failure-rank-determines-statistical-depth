module

public import PaperProofs.Structure.PSTR_ZeroWidthGuard_104

/-! NEW63-op bootstrap with a real zero-width guard at21. Park23,
locator26 and initialization45 are new literal slices. Old61/539 code and
theorems are unchanged. zeroTarget is an assembler label, not runtime data. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRUniformBootstrapCode

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims

def program (zeroTarget : Nat) : List PackingOp :=
  PSTRWidthPrologue.program ++ PSTRZeroWidthGuard.program zeroTarget ++
    PSTRCountInit.park ++ PSTRCountWorkspace.program ++ PSTRCountInit.program

theorem program_length (zeroTarget : Nat) : (program zeroTarget).length = 63 := rfl

structure Contains (whole : List PackingOp) (zeroTarget : Nat) : Prop where
  bound : (program zeroTarget).length ≤ whole.length
  code : ∀ i (hi : i < (program zeroTarget).length), whole[i]'(by omega) = (program zeroTarget)[i]

theorem transfer_block (whole : List PackingOp) (zeroTarget start : Nat)
    (cb : Contains whole zeroTarget) (block : List PackingOp)
    (hb : start + block.length ≤ (program zeroTarget).length)
    (hc : ∀ i (hi : i < block.length), (program zeroTarget)[start + i]'(by omega) = block[i]) :
    PSTROuterCountCode.BlockAt whole start block := by
  refine ⟨hb.trans cb.bound, ?_⟩
  intro i hi
  exact (cb.code (start + i) (by omega)).trans (hc i hi)

theorem header_contains (whole : List PackingOp) (zeroTarget : Nat) (cb : Contains whole zeroTarget) :
    PSTROuterCountCode.BlockAt whole 0 PSTRLiveHeader.program := by
  apply transfer_block whole zeroTarget 0 cb PSTRLiveHeader.program (by rw [program_length]; decide)
  intro i hi
  change i < 8 at hi
  interval_cases i <;> rfl

theorem width_contains (whole : List PackingOp) (zeroTarget : Nat) (cb : Contains whole zeroTarget) :
    PSTRWidthKernel.Contains whole 8 := by
  refine ⟨by rw [PSTRWidthKernel.kernel_length]; have h := cb.bound; rw [program_length] at h; omega, ?_⟩
  intro i hi
  exact (cb.code (8 + i) (by rw [program_length]; change i < 12 at hi; omega)).trans (by
    change i < 12 at hi
    interval_cases i <;> rfl)

theorem mask_code (whole : List PackingOp) (zeroTarget : Nat) (cb : Contains whole zeroTarget) :
    whole[20]'(by have h := cb.bound; rw [program_length] at h; omega) = PSTRWidthEmbedded.maskOp :=
  (cb.code 20 (by rw [program_length]; decide)).trans (by rfl)

theorem guard_contains (whole : List PackingOp) (zeroTarget : Nat) (cb : Contains whole zeroTarget) :
    PSTROuterCountCode.BlockAt whole 21 (PSTRZeroWidthGuard.program zeroTarget) := by
  apply transfer_block whole zeroTarget 21 cb _ (by rw [program_length, PSTRZeroWidthGuard.program_length]; decide)
  intro i hi
  change i < 2 at hi
  interval_cases i <;> rfl

theorem park_contains (whole : List PackingOp) (zeroTarget : Nat) (cb : Contains whole zeroTarget) :
    PSTROuterCountCode.BlockAt whole 23 PSTRCountInit.park := by
  apply transfer_block whole zeroTarget 23 cb _ (by rw [program_length, PSTRCountInit.park_length]; decide)
  intro i hi
  change i < 3 at hi
  interval_cases i <;> rfl

theorem workspace_contains (whole : List PackingOp) (zeroTarget : Nat) (cb : Contains whole zeroTarget) :
    PSTROuterCountCode.BlockAt whole 26 PSTRCountWorkspace.program := by
  apply transfer_block whole zeroTarget 26 cb _ (by rw [program_length, PSTRCountWorkspace.program_length]; decide)
  intro i hi
  change i < 19 at hi
  interval_cases i <;> rfl

theorem init_contains (whole : List PackingOp) (zeroTarget : Nat) (cb : Contains whole zeroTarget) :
    PSTROuterCountCode.BlockAt whole 45 PSTRCountInit.program := by
  apply transfer_block whole zeroTarget 45 cb _ (by rw [program_length, PSTRCountInit.program_length])
  intro i hi
  change i < 18 at hi
  interval_cases i <;> rfl

theorem header_run {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (zeroTarget : Nat)
    (cb : Contains whole zeroTarget) (hwords : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    packingRun rom whole 8 state = executeOps rom PSTRLiveHeader.program state := by
  have hh := header_contains whole zeroTarget cb
  exact PSTRWordSegments.straight_segment rom whole PSTRLiveHeader.program 0 hh.bound hh.code
    PSTRLiveHeader.program_straight hwords hpcfit state hp ha

end PaperProofs.Structure.LaminarTree.PSTRUniformBootstrapCode
