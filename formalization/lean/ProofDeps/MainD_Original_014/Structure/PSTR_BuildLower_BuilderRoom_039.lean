module

public import Structure.PSTR_BuildLower_CounterInit_036
public import PaperProofs.Structure.PA17_WordBounds_023

set_option maxHeartbeats 1000000
set_option maxRecDepth 30000

/-! Static encoded-code room for the ONE actual counter-prelude/start64 program. Dimensions and
runtime allocations do not occur in these code/PC bounds. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.CounterInit
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

theorem encoded_words_fit32 : WordsFit 32 (packingCode program) := by
  have checked : program.all (fun op => op.encode.toArray.toList.all (fun value => decide (value < 2 ^ 32))) = true := by decide
  have haltChecked : haltWords.toArray.toList.all (fun value => decide (value < 2 ^ 32)) = true := by decide
  intro value hv
  change value < 2 ^ 32
  change value ∈ program.flatMap (fun op => op.encode.toArray.toList) ++ haltWords.toArray.toList at hv
  rcases List.mem_append.mp hv with hv | hv
  · obtain ⟨op, hop, hword⟩ := List.mem_flatMap.mp hv
    exact of_decide_eq_true ((List.all_eq_true.mp ((List.all_eq_true.mp checked) op hop)) value hword)
  · exact of_decide_eq_true ((List.all_eq_true.mp haltChecked) value hv)

theorem pc_room32 : Fits 32 (5 * program.length) := by
  change 5 * program.length < 2 ^ 32
  decide

theorem encoded_words_fit (bits : Nat) (hb : 32 ≤ bits) : WordsFit bits (packingCode program) := by
  intro value hv
  exact PA17WordBounds023.fits_mono_bits hb (encoded_words_fit32 value hv)

theorem pc_room (bits : Nat) (hb : 32 ≤ bits) : Fits bits (5 * program.length) :=
  PA17WordBounds023.fits_mono_bits hb pc_room32

theorem selected_width_room (N q : Nat) : 32 ≤ indexWidth 32 N q := by
  have hc : 0 < Nat.clog 2 (N + q + 2) := Nat.clog_pos (by decide) (by omega)
  unfold indexWidth
  omega

theorem selected_encoded_words_fit (N q : Nat) : WordsFit (indexWidth 32 N q) (packingCode program) :=
  encoded_words_fit _ (selected_width_room N q)

theorem selected_pc_room (N q : Nat) : Fits (indexWidth 32 N q) (5 * program.length) :=
  pc_room _ (selected_width_room N q)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.CounterInit
