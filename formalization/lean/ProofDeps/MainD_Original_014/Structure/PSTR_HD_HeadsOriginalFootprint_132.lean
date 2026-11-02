module

public import Structure.PSTR_HD_HeadsBodyCode_131
public import PaperProofs.Structure.RawIncidenceLaminarRAM

/-! ORIGINAL all-q w32/F8192 numeric closure for the real heads array.
The complete raw ROM, packed heap, index allocation and actual code loading
are charged together. Only the compile-time body length is bounded. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine
open RawTreePreprocessingClaims

theorem heads_command_word_le (command : Command) : command.word ≤ 2 := by
  cases command <;> decide

theorem original_heads_rom_word_le {q : Nat} (full : List (Finset (Fin q))) (command : Command)
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
      · have hbit := RawTreeOutputWords.incidence_word_le_one q full value hbit
        omega
    · simp only [List.mem_singleton] at hcommand
      have htag := heads_command_word_le command
      omega

theorem original_heads_rom_fit {q : Nat} (full : List (Finset (Fin q))) (command : Command) :
    ∀ region, WordsFit (indexWidth 32 full.length q) ((callInput q full command).words region) := by
  intro region value hv
  apply PA17PackingBounds043.polynomial_fits
  have hvalue := original_heads_rom_word_le full command region value hv
  have hbase := PA17A19QueryBridgeNumeric006b.base_le_cube full.length q
  have hpowers := PA17PackingBounds043.powers_le_six full.length q
  omega

theorem heads_complete_footprint_bound (raw packed product index base code : Nat)
    (hraw : raw ≤ base ^ 2) (hpacked : packed ≤ product + 1)
    (hproduct : product ≤ 65538 * base ^ 4) (hindex : index ≤ 131072 * base ^ 3)
    (h2 : base ^ 2 ≤ base ^ 6)
    (hpowers : 1 ≤ base ^ 6 ∧ base ^ 3 ≤ base ^ 6 ∧ base ^ 4 ≤ base ^ 6) (hcode : code ≤ 65536) :
    raw + 3 + (4 + packed + index) + code ≤ 16777216 * base ^ 6 := by
  omega

theorem original_heads_total_footprint {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (queryBody : List PackingOp) (hlen : queryBody.length ≤ 8192) :
    Fits (indexWidth 32 full.length q) ((callInput q full command).size + PSTRCountAllocation.allocation full +
      (packingCode (uniformHeadsProgram queryBody)).length) := by
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
  have hraw : full.length * q ≤ (full.length + q + 2) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul
      (show full.length ≤ full.length + q + 2 by omega) (show q ≤ full.length + q + 2 by omega)
  have h2 : (full.length + q + 2) ^ 2 ≤ (full.length + q + 2) ^ 6 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hpowers := PA17PackingBounds043.powers_le_six full.length q
  rw [PSTRCountAllocation.input_size, uniform_heads_code_length]
  apply PA17PackingBounds043.polynomial_fits
  unfold PSTRCountAllocation.allocation physicalHeaderWords
  exact heads_complete_footprint_bound _ _ _ _ _ _ hraw hp hproduct hi h2 hpowers (by omega)

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
