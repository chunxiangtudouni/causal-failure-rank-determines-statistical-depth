module

public import PaperProofs.Structure.PA17_PackedPhase_045c
public import PaperProofs.Structure.PA17_WrappedNatRAM_038c

/-! Literal physical layout and footprint bounds for the original three
wrapped programs. No physical index-word value bound is introduced. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17PackedPhase045

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM PA17PackedTranslator034

theorem bits_min (N q : Nat) : 8 ≤ indexWidth 32 N q := by
  have hp := PA17PackingBounds043.bits_pos N q
  unfold indexWidth at *
  omega

theorem prepared_layout (N q capWords indexWords : Nat) (hpos : 0 < capWords)
    (hc : capWords ≤ 36 * (N + q + 2) ^ 3) (hi : indexWords ≤ 36 * (N + q + 2) ^ 3) :
    PA17PackedStore042b.Layout q capWords indexWords
      (physicalSpillBase q (indexWidth 32 N q) capWords indexWords)
      (packedCapacityWords q capWords (indexWidth 32 N q) + newIndexWords indexWords)
      (indexWidth 32 N q) := by
  exact ⟨hpos, bits_min N q, PA17PackingBounds043.width_le_bits N q,
    PA17PackingBounds043.capacity_fits N q capWords hc,
    PA17PackingBounds043.capacityProduct_fits N q capWords hc, rfl,
    by simp only [physicalSpillBase, newIndexWords, Nat.add_assoc]; exact le_rfl,
    PA17PackingBounds043.physicalHeap_fits N q capWords indexWords hc hi⟩

theorem packedFootprint_fit (N q capWords indexWords : Nat) (body : List Op) (rom : PhysicalROM)
    (hc : capWords ≤ 36 * (N + q + 2) ^ 3) (hi : indexWords ≤ 36 * (N + q + 2) ^ 3)
    (hlogical : rom.size + (haltingWords (logicalProgram (capWords + indexWords) body)).length ≤
      65536 * (N + q + 2) ^ 3) :
    Fits (indexWidth 32 N q)
      (rom.size + (packedCapacityWords q capWords (indexWidth 32 N q) + newIndexWords indexWords) +
        (packingCode (packedProgram q (indexWidth 32 N q) capWords indexWords body)).length) := by
  apply PA17PackingBounds043.polynomial_fits N q
  have hlen := packedProgram_length_le q (indexWidth 32 N q) capWords indexWords body
  have hp := PA17PackingBounds043.packedCapacityWords_le_product q capWords (indexWidth 32 N q)
    (PA17PackingBounds043.bits_pos N q)
  have hprod := PA17PackingBounds043.capacityProduct_le N q capWords hc
  have hpowers := PA17PackingBounds043.powers_le_six N q
  rw [packingCode_length]
  rw [haltingWords_length, logicalProgram_length] at hlogical
  unfold newIndexWords spillWords
  omega

end PaperProofs.Structure.LaminarTree.PA17PackedPhase045
