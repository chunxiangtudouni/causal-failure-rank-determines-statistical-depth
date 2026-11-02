module
public import PaperProofs.Structure.PA17_PackedTemplates_046l

/-! Original runtime dimension hypotheses discharge all prelude input and
bit-width bounds at the same factor32; the minimum word width is64. -/
@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA17GeneratorStatic048

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17PackedTemplates046

theorem numericScale_le_maxWord (N q t : Nat) (hq : 0 < q) (ht : t ≤ N + q + 1) :
    numericScale N q t ≤ 2 ^ indexWidth 32 N q - 1 := by
  have hu : 1 ≤ numericScale N q t := by dsimp [numericScale]; omega
  have hp : numericScale N q t ≤ numericScale N q t ^ 4 := by
    simpa using (pow_le_pow_right' hu (show 1 ≤ 4 by decide))
  have hf := numericBound_fits N q t hq ht
  change numericBound N q t < 2 ^ indexWidth 32 N q at hf
  dsimp [numericBound] at hf
  omega

theorem input_le_maxWord (N q t : Nat) (hq : 0 < q) (ht : t ≤ N + q + 1) :
    N + q + 1 ≤ 2 ^ indexWidth 32 N q - 1 := by
  have hh := numericScale_le_maxWord N q t hq ht
  dsimp [numericScale] at hh
  omega

theorem bits_le_maxWord (N q t : Nat) (hq : 0 < q) (ht : t ≤ N + q + 1) :
    indexWidth 32 N q ≤ 2 ^ indexWidth 32 N q - 1 :=
  (bits_le_numericScale N q t).trans (numericScale_le_maxWord N q t hq ht)

theorem dimensionWordsFit (N q t : Nat) (hq : 0 < q) (ht : t ≤ N + q + 1) :
    WordsFit (indexWidth 32 N q) [N, q, t] := by
  have hh := numericScale_le_maxWord N q t hq ht
  have hp : 0 < 2 ^ indexWidth 32 N q := pow_pos (by decide) _
  have hfit (value : Nat) (hv : value ≤ numericScale N q t) : Fits (indexWidth 32 N q) value := by
    change value < 2 ^ indexWidth 32 N q
    omega
  intro word hword
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hword
  rcases hword with hw | hw | hw
  · rw [hw]
    exact hfit N (by dsimp [numericScale]; omega)
  · rw [hw]
    exact hfit q (by dsimp [numericScale]; omega)
  · rw [hw]
    exact hfit t (by dsimp [numericScale]; omega)

theorem bits_ge_64 (N q : Nat) (hq : 0 < q) : 64 ≤ indexWidth 32 N q := by
  have hc := Nat.clog_mono_right 2 (show 3 ≤ N + q + 2 by omega)
  have hthree : Nat.clog 2 3 = 2 := by decide
  rw [hthree] at hc
  unfold indexWidth
  omega

theorem maxWord_fits (bits : Nat) : Fits bits (2 ^ bits - 1) :=
  Nat.sub_lt (pow_pos (by decide) _) (by decide)

theorem wordsFit_mono64 (code : List Nat) (N q : Nat) (hq : 0 < q)
    (hc : WordsFit 64 code) : WordsFit (indexWidth 32 N q) code := by
  intro word hw
  exact (hc word hw).trans_le (Nat.pow_le_pow_right (by decide) (bits_ge_64 N q hq))

end PaperProofs.Structure.LaminarTree.PA17GeneratorStatic048
