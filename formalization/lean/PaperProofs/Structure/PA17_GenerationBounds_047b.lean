module

public import PaperProofs.Structure.PA17_GenerationBounds_047a

/-! Exact generator allocation/word bounds. L is the dimension-independent
streamLength64 of the fixed six templates; its static bound is discharged
by the fixed-template assembly. T is always the actual generatedCode length. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

namespace PaperProofs.Structure.LaminarTree.PA17GenerationBounds047

open IndexedRAM IndexedClosureRAM AlgorithmClaims

def targetLength (N q size : Nat) : Nat :=
  (generatedCode PA17WrappedNatRAM038a.implementation PA17PackedPhase045.programs N q size).length

def generatorHeapWords (N q size : Nat) : Nat := 1024 + targetLength N q size + 2

theorem large_cubic_fits (N q value : Nat) (hq : 0 < q)
    (hvalue : value ≤ 1099511627776 * (N + q + 2) ^ 3) :
    Fits (indexWidth 32 N q) value := by
  apply fits_indexWidth_of_lt_power
  let base := N + q + 2
  have hb : 3 ≤ base := by dsimp only [base]; omega
  have hp : 1099511627776 < base ^ 29 :=
    lt_of_lt_of_le (by decide : 1099511627776 < 3 ^ 29) (Nat.pow_le_pow_left hb 29)
  have hpos : 0 < base ^ 3 := pow_pos (by omega) _
  calc
    value ≤ 1099511627776 * base ^ 3 := hvalue
    _ < base ^ 29 * base ^ 3 := Nat.mul_lt_mul_of_pos_right hp hpos
    _ = base ^ 32 := by rw [← pow_add]

theorem generator_footprint_fits (N q size L : Nat) (hq : 0 < q) (ht : 0 < size)
    (hu : size ≤ N + q + 1) (hL : L ≤ 2 ^ 32) :
    Fits (indexWidth 32 N q) (3 + generatorHeapWords N q size + (5 * (L + 63) + 5)) := by
  apply large_cubic_fits N q _ hq
  have htarget : targetLength N q size ≤ 4194304 * (N + q + 2) ^ 3 :=
    generatedCode_length_le_cube N q size ht hu
  have hbase := (PA17QueryFootprint025.powers_dominate N q).1
  have hl : L ≤ 4294967296 := hL
  unfold generatorHeapWords
  omega

theorem dimension_words_fit (N q size : Nat) (hu : size ≤ N + q + 1) :
    WordsFit (indexWidth 32 N q) [N, q, size] := by
  intro value hv
  apply PA17WordBounds023.cubic_fits N q value
  have hp := PA17QueryFootprint025.powers_dominate N q
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with hv | hv | hv <;> omega

structure GeneratorBounds (N q size L : Nat) : Prop where
  footprint : Fits (indexWidth 32 N q) (3 + generatorHeapWords N q size + (5 * (L + 63) + 5))
  pc : 5 * (L + 63) ≤ 2 ^ indexWidth 32 N q - 1
  pc_last : 5 * (L + 63) + 4 ≤ 2 ^ indexWidth 32 N q - 1
  heap : generatorHeapWords N q size ≤ 2 ^ indexWidth 32 N q - 1
  output_end : 1024 + targetLength N q size + 1 ≤ 2 ^ indexWidth 32 N q - 1
  input : WordsFit (indexWidth 32 N q) [N, q, size]
  reserve : 64 ≤ generatorHeapWords N q size
  target : targetLength N q size ≤ generatorHeapWords N q size

theorem generator_bounds (N q size L : Nat) (hq : 0 < q) (ht : 0 < size)
    (hu : size ≤ N + q + 1) (hL : L ≤ 2 ^ 32) : GeneratorBounds N q size L := by
  have hf := generator_footprint_fits N q size L hq ht hu hL
  have hm : 3 + generatorHeapWords N q size + (5 * (L + 63) + 5) ≤ 2 ^ indexWidth 32 N q - 1 := by
    unfold Fits at hf
    omega
  refine ⟨hf, ?_, ?_, ?_, ?_, dimension_words_fit N q size hu, ?_, ?_⟩
  all_goals dsimp only [generatorHeapWords] at *
  all_goals omega

end PaperProofs.Structure.LaminarTree.PA17GenerationBounds047
