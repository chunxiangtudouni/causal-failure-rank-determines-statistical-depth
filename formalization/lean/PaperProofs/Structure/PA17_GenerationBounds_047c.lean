module

public import PaperProofs.Structure.PA17_GenerationBounds_047b

/-! Actual generator resource arithmetic for its proved dynamic-trace
envelope. L/F are fixed syntax constants, never input or output oracles. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

namespace PaperProofs.Structure.LaminarTree.PA17GenerationBounds047

open IndexedRAM IndexedClosureRAM AlgorithmClaims

def generationConstant : Nat := 288230376151711744

theorem generationConstant_eq : generationConstant = 2 ^ 58 := rfl

theorem generationConstant_pos : 0 < generationConstant := by decide

theorem generator_trace_envelope_le (N q size F : Nat) (ht : 0 < size) (hF : F ≤ 2 ^ 32) :
    12 * (6 * N + 12 * q + 55 + (F + 9) * (targetLength N q size + 1)) ≤
      216172834106377176 * work N q size := by
  have hd := PA17BuildResources006.dimension_le_work N q size ht
  have htarget : targetLength N q size ≤ 4194304 * work N q size :=
    generatedCode_length_le N q size ht
  have hnext : targetLength N q size + 1 ≤ 4194305 * work N q size := by omega
  have hf : F + 9 ≤ 4294967305 := by have hh : F ≤ 4294967296 := hF; omega
  have hp := Nat.mul_le_mul hf hnext
  have hfront : 6 * N + 12 * q + 55 ≤ 73 * work N q size := by omega
  omega

theorem generator_total_envelope_le (N q size L F : Nat) (ht : 0 < size)
    (hL : L ≤ 2 ^ 32) (hF : F ≤ 2 ^ 32) :
    3 + (5 * (L + 63) + 5) + generatorHeapWords N q size + 8 +
      12 * (6 * N + 12 * q + 55 + (F + 9) * (targetLength N q size + 1)) ≤
        generationConstant * work N q size := by
  have hw := (PA17BuildResources006.dimension_le_work N q size ht).2.2
  have htarget : targetLength N q size ≤ 4194304 * work N q size :=
    generatedCode_length_le N q size ht
  have hl : L ≤ 4294967296 := hL
  have htrace := generator_trace_envelope_le N q size F ht hF
  unfold generatorHeapWords generationConstant
  omega

end PaperProofs.Structure.LaminarTree.PA17GenerationBounds047
