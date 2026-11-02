module

public import PaperProofs.Structure.PA17_A19QueryBridge_Numeric_006b
public import PaperProofs.Structure.RawIncidenceLaminarRAM

/-! The original raw call ROM and shared F8192 allocation fit the original
wordFactor32 together with the fixed1340-op query's6705 physical code words.
Commands have only three finite tags,so no Allowed input is strengthened. -/

@[expose] public section
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeFootprint028

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open RawTreePreprocessingClaims

theorem command_word_le (command : Command) : command.word ≤ 2 := by
  cases command <;> decide

theorem callInput_word_le {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (region : Region) (value : Nat) (hv : value ∈ (callInput q full command).words region) :
    value ≤ full.length + q + 2 := by
  cases region with
  | internal | children => cases hv
  | input =>
    change value ∈ ([full.length, q] ++ incidence full) ++ [command.word] at hv
    rcases List.mem_append.mp hv with hraw | hcommand
    · rcases List.mem_append.mp hraw with hheader | hbit
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hheader
        rcases hheader with hN | hq
        · omega
        · omega
      · have hh := RawTreeOutputWords.incidence_word_le_one q full value hbit
        omega
    · simp only [List.mem_singleton] at hcommand
      have hh := command_word_le command
      omega

theorem callInput_words_fit {q : Nat} (full : List (Finset (Fin q))) (command : Command) :
    ∀ region, WordsFit (indexWidth 32 full.length q) ((callInput q full command).words region) := by
  intro region value hv
  apply PA17PackingBounds043.polynomial_fits
  have hh := callInput_word_le full command region value hv
  have hc := PA17A19QueryBridgeNumeric006b.base_le_cube full.length q
  have hp := PA17PackingBounds043.powers_le_six full.length q
  omega

theorem callInput_size {q : Nat} (full : List (Finset (Fin q))) (command : Command) :
    (callInput q full command).size = full.length * q + 3 := by
  simp only [callInput, rawIncidenceROM, PhysicalROM.size, List.length_append,
    List.length_cons, List.length_nil, RawIncidenceLaminarRAM.incidence_length]
  omega

theorem callInput_size_le_cube {q : Nat} (full : List (Finset (Fin q))) (command : Command) :
    (callInput q full command).size ≤ 4 * (full.length + q + 2) ^ 3 := by
  have hN : full.length ≤ full.length + q + 2 := by omega
  have hq : q ≤ full.length + q + 2 := by omega
  have hm : full.length * q ≤ (full.length + q + 2) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hN hq
  have hp := PA17QueryFootprint025.powers_dominate full.length q
  rw [callInput_size]
  omega

theorem call_footprint_8192 {q : Nat} (full : List (Finset (Fin q))) (command : Command) :
    let bits := indexWidth 32 full.length q
    let C := capacityWords 8192 full.length q (treeSize q full)
    let allocatedWords := physicalHeaderWords + packedCapacityWords q C bits +
      8192 * (full.length + q + treeSize q full + 1)
    Fits bits ((callInput q full command).size + allocatedWords + 6705) := by
  dsimp only
  have hc := PA17A19QueryBridgeNumeric006b.capacity_bound full 8192 (by decide)
  have hw := PA17PackingBounds043.width_le_base full.length q
  have hproduct : capacityWords 8192 full.length q (treeSize q full) * CapacityBits.width q ≤
      65538 * (full.length + q + 2) ^ 4 := by
    convert Nat.mul_le_mul hc hw using 1
    ring
  have hp := PA17PackingBounds043.packedCapacityWords_le_product q
    (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)
    (PA17PackingBounds043.bits_pos full.length q)
  have hi := PA17A19QueryBridgeNumeric006b.index_bound full 8192 (by decide)
  have hr := callInput_size_le_cube full command
  have hpowers := PA17PackingBounds043.powers_le_six full.length q
  apply PA17PackingBounds043.polynomial_fits
  unfold physicalHeaderWords
  omega

theorem original_allowed_footprint {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (_hq : 0 < q) (_hl : LaminarSchedule full)
    (_allowed : Allowed full configuration command) :
    let bits := indexWidth 32 full.length q
    let C := capacityWords 8192 full.length q (treeSize q full)
    let allocatedWords := physicalHeaderWords + packedCapacityWords q C bits +
      8192 * (full.length + q + treeSize q full + 1)
    (∀ region, WordsFit bits ((callInput q full command).words region)) ∧
      Fits bits ((callInput q full command).size + allocatedWords + 6705) := by
  exact ⟨callInput_words_fit full command, call_footprint_8192 full command⟩

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeFootprint028
