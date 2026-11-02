module

public import PaperProofs.Statistics.RationalRisk
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-! Factor-two rationalization preserves every fixed positive log depth. -/

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace PaperProofs.Statistics

theorem iteratedLog_tendsto_atTop (depth : ℕ) :
    Tendsto (iteratedLog depth) atTop atTop := by
  induction depth with
  | zero => exact tendsto_id
  | succ depth ih => exact Real.tendsto_log_atTop.comp ih

theorem log_inverse_factorTwo (risk target : ℝ) (hrisk : 0 < risk)
    (hlower : risk / 2 ≤ target) (hupper : target ≤ risk) :
    Real.log (1 / risk) ≤ Real.log (1 / target) ∧
      Real.log (1 / target) ≤ Real.log (1 / risk) + Real.log 2 := by
  have ht : 0 < target := lt_of_lt_of_le (half_pos hrisk) hlower
  constructor
  · exact Real.log_le_log (one_div_pos.mpr hrisk)
      (one_div_le_one_div_of_le ht hupper)
  · have hi : 1 / target ≤ 2 * (1 / risk) := by
      calc
        _ ≤ 1 / (risk / 2) := one_div_le_one_div_of_le (half_pos hrisk) hlower
        _ = _ := by field_simp
    have h := Real.log_le_log (one_div_pos.mpr ht) hi
    rwa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (ne_of_gt (one_div_pos.mpr hrisk)), add_comm] at h

theorem factorTwo_log_isEquivalent (choose : ℝ → ℚ)
    (hchoose : ∀ risk : ℝ, 0 < risk →
      risk / 2 ≤ (choose risk : ℝ) ∧ (choose risk : ℝ) ≤ risk) :
    (fun risk : ℝ => Real.log (1 / (choose risk : ℝ))) ~[nhdsWithin 0 (Set.Ioi 0)]
      (fun risk => Real.log (1 / risk)) := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have hinv : Tendsto (fun risk : ℝ => 1 / risk) l atTop := by
    simpa only [one_div] using (tendsto_inv_nhdsGT_zero :
      Tendsto (fun risk : ℝ => risk⁻¹) l atTop)
  have hlog := Real.tendsto_log_atTop.comp hinv
  have hden : ∀ᶠ risk in l, 0 < Real.log (1 / risk) :=
    hlog.eventually_gt_atTop 0
  have hrisk : ∀ᶠ risk in l, 0 < risk := self_mem_nhdsWithin
  have hratio : Tendsto
      (fun risk : ℝ => Real.log (1 / (choose risk : ℝ)) / Real.log (1 / risk)) l (𝓝 1) := by
    have hupper : Tendsto (fun risk : ℝ => 1 + Real.log 2 / Real.log (1 / risk)) l (𝓝 1) := by
      have hz : Tendsto (fun risk : ℝ => Real.log 2 / Real.log (1 / risk)) l (𝓝 0) :=
        tendsto_const_nhds.div_atTop hlog
      simpa only [add_zero] using tendsto_const_nhds.add hz
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ => (1 : ℝ)) (h := fun risk =>
      1 + Real.log 2 / Real.log (1 / risk))
      tendsto_const_nhds hupper
    · filter_upwards [hrisk, hden] with risk hr hd
      have hb := (log_inverse_factorTwo risk (choose risk) hr
        (hchoose risk hr).1 (hchoose risk hr).2).1
      exact (le_div_iff₀ hd).mpr (by simpa only [one_mul] using hb)
    · filter_upwards [hrisk, hden] with risk hr hd
      have hb := (log_inverse_factorTwo risk (choose risk) hr
        (hchoose risk hr).1 (hchoose risk hr).2).2
      calc
        _ ≤ (Real.log (1 / risk) + Real.log 2) / Real.log (1 / risk) :=
          (div_le_div_iff_of_pos_right hd).mpr hb
        _ = _ := by rw [add_div, div_self (ne_of_gt hd)]
  exact (isEquivalent_iff_tendsto_one (hden.mono fun _ h => ne_of_gt h)).mpr hratio

theorem factorTwo_iteratedLog_isEquivalent (depth : ℕ) (choose : ℝ → ℚ)
    (hchoose : ∀ risk : ℝ, 0 < risk →
      risk / 2 ≤ (choose risk : ℝ) ∧ (choose risk : ℝ) ≤ risk) :
    (fun risk : ℝ => iteratedLog (depth + 1) (1 / (choose risk : ℝ)))
      ~[nhdsWithin 0 (Set.Ioi 0)]
        (fun risk => iteratedLog (depth + 1) (1 / risk)) := by
  induction depth with
  | zero => exact factorTwo_log_isEquivalent choose hchoose
  | succ depth ih =>
    apply ih.log
    have hinv : Tendsto (fun risk : ℝ => 1 / risk) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
      simpa only [one_div] using (tendsto_inv_nhdsGT_zero :
        Tendsto (fun risk : ℝ => risk⁻¹) (nhdsWithin 0 (Set.Ioi 0)) atTop)
    exact (iteratedLog_tendsto_atTop (depth + 1)).comp hinv

theorem factorTwoRiskIteratedLogStability : FactorTwoRiskIteratedLogStability := by
  intro depth hdepth choose hchoose
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hdepth)
  have hinv : Tendsto (fun risk : ℝ => 1 / risk) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    simpa only [one_div] using (tendsto_inv_nhdsGT_zero :
      Tendsto (fun risk : ℝ => risk⁻¹) (nhdsWithin 0 (Set.Ioi 0)) atTop)
  exact (isEquivalent_iff_tendsto_one
    (((iteratedLog_tendsto_atTop (n + 1)).comp hinv).eventually_ne_atTop 0)).mp
      (factorTwo_iteratedLog_isEquivalent n choose hchoose)

end PaperProofs.Statistics
