module

public import Structure.PSTR_RuntimeWidthRun_007
public import PaperProofs.Structure.PackingWordBounds

/-! Discharge the width-loop's numeric room from the original logarithmic
word width. No precomputed width or performance certificate is assumed. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRRuntimeWidthBounds

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

theorem word_bits (N q : Nat) : 8 ≤ indexWidth 16 N q := by
  have hp : 0 < Nat.clog 2 (N + q + 2) := Nat.clog_pos (by decide) (by omega)
  unfold indexWidth
  omega

theorem scalar_room (N q : Nat) : Fits (indexWidth 16 N q) (2 * (q + 1)) := by
  apply fits_indexWidth_of_lt_power
  have hsmall0 : 2 * (q + 1) ≤ (N + q + 2) * (N + q + 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hsmall : 2 * (q + 1) ≤ (N + q + 2) ^ 2 + 1024 := by
    rw [pow_two]
    omega
  exact hsmall.trans_lt (quadratic_add_lt_power16 (N + q + 2) (by omega))

theorem scalar_width (N q : Nat) : CapacityBits.width q ≤ indexWidth 16 N q := by
  apply (CapacityBits.width_spec q _).mpr
  have hs : 2 * (q + 1) < 2 ^ indexWidth 16 N q := scalar_room N q
  omega

theorem actual_word_width (rom : PhysicalROM) (N q : Nat)
    (state : WordState (indexWidth 16 N q))
    (hf : (state.register .fresh).toNat = q)
    (hp : state.pc = BitVec.ofNat (indexWidth 16 N q) 0) (ha : state.halted = false) :
    let after := packingRun rom PSTRRuntimeWidth.program (8 * CapacityBits.width q + 8) state
    after.halted = true ∧
      after.register .total = BitVec.ofNat (indexWidth 16 N q) (CapacityBits.width q) ∧
      after.register .value = BitVec.ofNat (indexWidth 16 N q) (2 ^ CapacityBits.width q) ∧
      after.register .fresh = state.register .fresh ∧ after.heap = state.heap :=
  PSTRRuntimeWidthRun.actual_word_width rom q state (word_bits N q) hf hp ha (scalar_room N q)

theorem trace_linear_dimension {bits : Nat} (rom : PhysicalROM) (q : Nat) (state : WordState bits) :
    (packingDynamicTrace rom PSTRRuntimeWidth.program (8 * CapacityBits.width q + 8) state).length ≤
      96 * q + 192 := by
  have ht := PSTRRuntimeWidthRun.actual_trace_bound rom q state
  have hw := PSTRRuntimeWidthWord.width_le q
  omega

end PaperProofs.Structure.LaminarTree.PSTRRuntimeWidthBounds
