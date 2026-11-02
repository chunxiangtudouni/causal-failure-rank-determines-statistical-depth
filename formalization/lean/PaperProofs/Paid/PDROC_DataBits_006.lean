module

public import PaperProofs.Paid.PDROC_DataBits_004
public import PaperProofs.Paid.PDROC_DataBits_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.DataBits

theorem ratEncodingBits_le_of_range (q R : ℚ) (D : ℕ) (h0 : 0 ≤ q) (hq : q ≤ R)
    (hd : ratDenBits q ≤ D) : ratEncodingBits q ≤ 2*D + ratEncodingBits R + 2 := by
  have hceil : ⌈|q|⌉₊ ≤ ⌈R⌉₊ := Nat.ceil_mono (by simpa only [abs_of_nonneg h0] using hq)
  have hb := natBits_mono (Nat.add_le_add_right hceil 1)
  have hR := rat_ceil_bits_le_numBits R
  have hn := ratNumBits_le_denBits_ceil_abs q
  unfold ratEncodingBits
  omega

def entryMagnitude (P : Parameters) (n : ℕ) : ℚ := (n:ℚ)*(menuChargeBound P+1)+1

theorem entryMagnitude_encodingBits_le (P : Parameters) (n : ℕ) :
    ratEncodingBits (entryMagnitude P n) ≤ 64 * (ratEncodingBits P.reviewFee +
      ratEncodingBits P.certificate.gamma + natBits P.certificate.M + natBits n + 1) := by
  have htwo : ratEncodingBits (2:ℚ) = 4 := by norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  have hone : ratEncodingBits (1:ℚ) = 3 := by norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  have hg := ratEncodingBits_mul_le (2:ℚ) P.certificate.gamma
  have hm := ratEncodingBits_mul_le P.reviewFee (P.certificate.M:ℚ)
  have hc := ratEncodingBits_div_le (P.reviewFee*(P.certificate.M:ℚ)) (2*P.certificate.gamma)
  have hplus := ratEncodingBits_add_le (menuChargeBound P) 1
  have hprod := ratEncodingBits_mul_le (n:ℚ) (menuChargeBound P+1)
  have hend := ratEncodingBits_add_le ((n:ℚ)*(menuChargeBound P+1)) 1
  rw [htwo] at hg
  rw [ratEncodingBits_natCast_menu] at hm hprod
  rw [hone] at hplus hend
  change ratEncodingBits (menuChargeBound P) ≤ _ at hc
  change ratEncodingBits (entryMagnitude P n) ≤ _ at hend
  omega

theorem entryRange_le_magnitude (P : Parameters) (n : ℕ) (entry : MenuEntry)
    (h : EntryRange P.certificate.M ((n:ℚ)*menuChargeBound P) n entry) :
    entry.observation ≤ entryMagnitude P n ∧ entry.repairs ≤ entryMagnitude P n ∧
      entry.failure ≤ entryMagnitude P n := by
  have hc := menuChargeBound_nonneg P
  have hn : (0:ℚ) ≤ n := Nat.cast_nonneg _
  dsimp [entryMagnitude]
  constructor
  · nlinarith [h.observation_le]
  constructor
  · nlinarith [h.repairs_le, mul_nonneg hn hc]
  · nlinarith [h.failure_le, mul_nonneg hn hc]

def menuEntrySizeBound (P : Parameters) (L : ℕ) : ℕ :=
  3 + natBits P.certificate.M + 3 * (2 * ((P.certificate.stages+1) *
    (2*(P.certificate.M+1)+2)*L) + 64 * (ratEncodingBits P.reviewFee +
    ratEncodingBits P.certificate.gamma + natBits P.certificate.M + natBits P.certificate.stages + 1) + 2)

theorem cachedMenuEntry_bits_le (P : Parameters) (fee penalty : ℚ) (L : ℕ)
    (hL : P.MenuEncodingBound fee L) (n k : ℕ) (hn : n ≤ P.certificate.stages) :
    menuEntryBits (menuEntryAt
      (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages) n k) ≤
      menuEntrySizeBound P L := by
  let entry := menuEntryAt
    (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages) n k
  let D := P.menuCommonDenominator fee
  let B := (P.certificate.stages+1)*(2*(P.certificate.M+1)+2)*L
  have hden := cachedSolveMenuTable_entryDen P fee penalty P.tools P.certificate.stages n k hn
  have hD := menuCommonDenominator_bits P fee L hL
  have hDpos := menuCommonDenominator_pos P fee
  have hpower : natBits (D^(n+1)) ≤ B := by
    have hp := natBits_pow_le_of_pos D (n+1) (by omega)
    have hmul := Nat.mul_le_mul (Nat.add_le_add_right hn 1) hD
    exact hp.trans (by simpa only [D, B, Nat.mul_assoc] using hmul)
  have hdiv : D^n ∣ D^(n+1) := pow_dvd_pow D (by omega)
  have ho := (ratDenBits_le_of_dvd (pow_pos hDpos _) (hden.1.trans hdiv)).trans hpower
  have hr := (ratDenBits_le_of_dvd (pow_pos hDpos _) (hden.2.1.trans hdiv)).trans hpower
  have hf := (ratDenBits_le_of_dvd (pow_pos hDpos _) (hden.2.2.trans hdiv)).trans hpower
  have hrange : EntryRange P.certificate.M ((n:ℚ)*menuChargeBound P) n entry :=
    cachedSolveMenuTable_entryRange P fee penalty P.tools P.certificate.stages n k hn
  have hmag := entryRange_le_magnitude P n entry hrange
  have he := entryMagnitude_encodingBits_le P n
  have he' : ratEncodingBits (entryMagnitude P n) ≤ 64 * (ratEncodingBits P.reviewFee +
      ratEncodingBits P.certificate.gamma + natBits P.certificate.M + natBits P.certificate.stages + 1) := by
    exact he.trans (by have := natBits_mono hn; omega)
  have hob := ratEncodingBits_le_of_range entry.observation (entryMagnitude P n) B
    hrange.observation_nonneg hmag.1 ho
  have hrb := ratEncodingBits_le_of_range entry.repairs (entryMagnitude P n) B
    hrange.repairs_nonneg hmag.2.1 hr
  have hfb := ratEncodingBits_le_of_range entry.failure (entryMagnitude P n) B
    hrange.failure_nonneg hmag.2.2 hf
  change menuActionBits entry.action + ratEncodingBits entry.observation +
    ratEncodingBits entry.repairs + ratEncodingBits entry.failure ≤ _
  have hact := hrange.action_bits_le
  dsimp [menuEntrySizeBound]
  omega

theorem list_map_sum_bound {A : Type*} (values : List A) (f : A → ℕ) (B : ℕ)
    (h : ∀ a ∈ values, f a ≤ B) : (values.map f).sum ≤ values.length*B := by
  have hb := List.sum_le_length_nsmul (values.map f) B (by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact h a ha)
  simpa only [List.length_map, smul_eq_mul] using hb

theorem cachedMenuTable_bits_le (P : Parameters) (fee penalty : ℚ) (L : ℕ)
    (hL : P.MenuEncodingBound fee L) :
    menuTableBits (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages) ≤
      (P.certificate.stages+1)*(P.tools+1)*menuEntrySizeBound P L := by
  let table := P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages
  have hsize : table.size = P.certificate.stages+1 := cachedSolveMenuTable_size P fee penalty _ _
  have hrow : ∀ row ∈ table, row.size = P.tools+1 := by
    simpa only [table, cachedSolveMenuTable_eq] using P.solveMenuTable_row_size fee penalty P.tools P.certificate.stages
  have hentry : ∀ row ∈ table.toList, ∀ entry ∈ row.toList, menuEntryBits entry ≤ menuEntrySizeBound P L := by
    intro row hr entry he
    have hr' : row ∈ table := by simpa using hr
    have he' : entry ∈ row := by simpa using he
    obtain ⟨n, hn, hnr⟩ := Array.getElem_of_mem hr'
    obtain ⟨k, hk, hke⟩ := Array.getElem_of_mem he'
    have hgate : menuEntryAt table n k = entry := by
      simp only [menuEntryAt, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hn,
        Option.getD_some, hnr, Array.getElem?_eq_getElem hk, hke]
    rw [← hgate]
    exact cachedMenuEntry_bits_le P fee penalty L hL n k (by omega)
  have hout := list_map_sum_bound table.toList
    (fun row => (row.toList.map menuEntryBits).sum) ((P.tools+1)*menuEntrySizeBound P L) (by
      intro row hr
      have hb := list_map_sum_bound row.toList menuEntryBits (menuEntrySizeBound P L) (hentry row hr)
      have hr' : row ∈ table := by simpa using hr
      simpa only [Array.length_toList, hrow row hr'] using hb)
  simpa only [menuTableBits, Array.length_toList, hsize, Nat.mul_assoc] using hout

end PDROC.DataBits
