module

public import PaperProofs.Paid.PDROC_MenuExpected_003
public import PaperProofs.Paid.PDMenu_MenuTableLocality_080

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.MenuExpected

def RecordMeans (P : Parameters) (n : ℕ) (records : Tail P n → PDMenu.MenuPathRecord) (entry : MenuEntry) : Prop :=
  (∫⁻ sample, (records sample).observation ∂PDMenu.menuAnalysisLaw P n) = ENNReal.ofReal (entry.observation:ℝ) ∧
  (∫⁻ sample, ((records sample).physicalRepairs:ℝ≥0∞) ∂PDMenu.menuAnalysisLaw P n) = ENNReal.ofReal (entry.repairs:ℝ) ∧
  (∫⁻ sample, failureValue (records sample) ∂PDMenu.menuAnalysisLaw P n) = ENNReal.ofReal (entry.failure:ℝ)

theorem recordMeans_summary_iff (P : Parameters) (table : MenuTable) (n k : ℕ) :
    RecordMeans P n (fun sample => PDMenu.menuPathSummary P table n k sample.1 sample.2) (menuEntryAt table n k) ↔
      PDMenu.MenuPathMeans P table n k := by
  constructor
  · intro h
    exact ⟨h.1,h.2.1,(failure_measure_eq_integral P table n k).trans h.2.2⟩
  · intro h
    exact ⟨h.1,h.2.1,(failure_measure_eq_integral P table n k).symm.trans h.2.2⟩

theorem recordMeans_finish (P : Parameters) (n : ℕ) :
    RecordMeans P n (fun _ => PDMenu.menuPathFinish) finishEntry := by
  simp [RecordMeans, PDMenu.menuPathFinish, finishEntry, failureValue]

theorem recordMeans_abandon (P : Parameters) (n : ℕ) :
    RecordMeans P n (fun _ => PDMenu.menuPathAbandon) abandonEntry := by
  simp [RecordMeans, PDMenu.menuPathAbandon, abandonEntry, failureValue]

theorem recordMeans_increment (P : Parameters) (n : ℕ) (records : Tail P n → PDMenu.MenuPathRecord)
    (entry : MenuEntry) (hmeas : PDMenu.MeasurableMenuRecord records) (h : RecordMeans P n records entry)
    (hr : 0 ≤ entry.repairs) :
    RecordMeans P n (fun sample => {records sample with physicalRepairs := (records sample).physicalRepairs+1})
      (repairEntry entry) := by
  refine ⟨h.1,?_,h.2.2⟩
  have hm : Measurable (fun sample : Tail P n => ((records sample).physicalRepairs:ℝ≥0∞)) :=
    (measurable_of_countable (fun count : ℕ => (count:ℝ≥0∞))).comp hmeas.2.1
  change (∫⁻ sample, (((records sample).physicalRepairs+1:ℕ):ℝ≥0∞) ∂PDMenu.menuAnalysisLaw P n) =
    ENNReal.ofReal ((1+entry.repairs:ℚ):ℝ)
  simp_rw [Nat.cast_add, Nat.cast_one]
  rw [lintegral_add_left hm, h.2.1]
  have hr' : (0:ℝ) ≤ entry.repairs := by exact_mod_cast hr
  simp only [lintegral_const, measure_univ, mul_one, Rat.cast_add, Rat.cast_one,
    ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 1) hr', ENNReal.ofReal_one]
  exact add_comm _ _

theorem ofReal_rat_add (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal ((a+b:ℚ):ℝ) = ENNReal.ofReal (a:ℝ)+ENNReal.ofReal (b:ℝ) := by
  rw [Rat.cast_add]
  exact ENNReal.ofReal_add (by exact_mod_cast ha) (by exact_mod_cast hb)

theorem ofReal_rat_mul (a b : ℚ) (ha : 0 ≤ a) :
    ENNReal.ofReal ((a*b:ℚ):ℝ) = ENNReal.ofReal (a:ℝ)*ENNReal.ofReal (b:ℝ) := by
  rw [Rat.cast_mul]
  exact ENNReal.ofReal_mul (by exact_mod_cast ha)

theorem ofReal_weighted_sum (p x y : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ENNReal.ofReal (((1-p)*x+p*y:ℚ):ℝ) =
      ENNReal.ofReal (1-(p:ℝ))*ENNReal.ofReal (x:ℝ)+
      ENNReal.ofReal (p:ℝ)*ENNReal.ofReal (y:ℝ) := by
  rw [ofReal_rat_add _ _ (mul_nonneg (sub_nonneg.mpr hp1) hx) (mul_nonneg hp hy),
    ofReal_rat_mul _ _ (sub_nonneg.mpr hp1), ofReal_rat_mul _ _ hp]
  norm_cast

theorem ofReal_charge_weighted_sum (c p x y : ℚ) (hc : 0 ≤ c) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ENNReal.ofReal ((c+(1-p)*x+p*y:ℚ):ℝ) =
      ENNReal.ofReal (c:ℝ)+ENNReal.ofReal (1-(p:ℝ))*ENNReal.ofReal (x:ℝ)+
        ENNReal.ofReal (p:ℝ)*ENNReal.ofReal (y:ℝ) := by
  rw [ofReal_rat_add _ _ (add_nonneg hc (mul_nonneg (sub_nonneg.mpr hp1) hx)) (mul_nonneg hp hy),
    ofReal_rat_add _ _ hc (mul_nonneg (sub_nonneg.mpr hp1) hx),
    ofReal_rat_mul _ _ (sub_nonneg.mpr hp1), ofReal_rat_mul _ _ hp]
  norm_cast

/-- The original stored current cell reads exactly the preceding row of
the same full computed table. No summary or policy performance is used. -/
theorem computed_cell_succ (P : Parameters) (fee penalty : ℚ) (N K n k : ℕ)
    (hn : n+1 ≤ N) (hk : k ≤ K) :
    menuEntryAt (P.solveMenuTable fee penalty K N) (n+1) k =
      P.nextMenuEntry fee penalty ((P.solveMenuTable fee penalty K N).getD n #[]) k := by
  calc
    _ = menuEntryAt (P.solveMenuTable fee penalty K (n+1)) (n+1) k :=
      PDMenu.solveMenuTable_cell_prefix P fee penalty K N (n+1) hn k
    _ = P.nextMenuEntry fee penalty ((P.solveMenuTable fee penalty K n).getD n #[]) k :=
      PDMenu.solveMenuTable_last_entry_succ P fee penalty K n k hk
    _ = _ := by
      apply PDMenu.nextMenuEntry_congr_previous
      intro j _hj
      exact (PDMenu.solveMenuTable_cell_prefix P fee penalty K N n (by omega) j).symm

theorem computed_cell_zero (P : Parameters) (fee penalty : ℚ) (N K k : ℕ) (hk : k ≤ K) :
    menuEntryAt (P.solveMenuTable fee penalty K N) 0 k = finishEntry := by
  rw [PDMenu.solveMenuTable_cell_prefix P fee penalty K N 0 (by omega) k]
  exact PDMenu.baseMenuRow_getD K k hk

end PDROC.MenuExpected
