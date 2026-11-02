module

public import PaperProofs.Paid.PDROC_SimulatorLaw_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance} {Seed : Type*}

/-- Expose the genuine FIRST postwrite exit, retaining its minimality and
the original complete history, for finite-stage distribution induction. -/
theorem postwrite_first_exit (input : StatisticalInput I) (C : Contract I)
    (hpay : C.IsCurrentPayment) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hl : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (start : ℕ) (stage : I.Stage)
    (ha : (run input C mode accounting source sample start).halted = false)
    (hc : (run input C mode accounting source sample start).cursor = stage.val)
    (hw : (run input C mode accounting source sample start).ledger.written stage ≠ none) :
    ∃ exit : ℕ, exit ≤ 3 ∧
      ((run input C mode accounting source sample (start + exit)).halted = true ∨
        (run input C mode accounting source sample (start + exit)).cursor = stage.val + 1) ∧
      (∀ k < exit, (run input C mode accounting source sample (start + k)).halted = false ∧
        (run input C mode accounting source sample (start + k)).cursor = stage.val) ∧
      postwriteStageTrace source sample.1 stage (run input C mode accounting source sample start).history 3 =
        (run input C mode accounting source sample (start + exit)).history := by
  classical
  let E := fun k : ℕ => (run input C mode accounting source sample (start + k)).halted = true ∨
    stage.val < (run input C mode accounting source sample (start + k)).cursor
  have he : ∃ k, E k := ⟨3,
    run_written_stage_exit_within_three input C hpay mode accounting source hl sample start stage hc hw⟩
  let exit := Nat.find he
  have hexit : E exit := Nat.find_spec he
  have hbound : exit ≤ 3 := Nat.find_min' he
    (run_written_stage_exit_within_three input C hpay mode accounting source hl sample start stage hc hw)
  have hbefore (k : ℕ) (hk : k < exit) :
      (run input C mode accounting source sample (start + k)).halted = false ∧
        (run input C mode accounting source sample (start + k)).cursor = stage.val := by
    have hn : ¬ E k := Nat.find_min he hk
    refine ⟨Bool.eq_false_iff.mpr (fun hh => hn (Or.inl hh)), ?_⟩
    have hlo := run_cursor_monotone input C mode accounting source hl sample (Nat.le_add_right start k)
    change (run input C mode accounting source sample start).cursor ≤
      (run input C mode accounting source sample (start + k)).cursor at hlo
    rw [hc] at hlo
    have hhi : ¬ stage.val < (run input C mode accounting source sample (start + k)).cursor :=
      fun h => hn (Or.inr h)
    omega
  have hpositive : 0 < exit := by
    have hnzero : ¬ E 0 := by
      simp only [E, Nat.add_zero, ha, hc, Bool.false_eq_true, Nat.lt_irrefl, or_self, not_false_eq_true]
    by_contra hn
    have hz : exit = 0 := by omega
    exact hnzero (hz ▸ hexit)
  have hone : (run input C mode accounting source sample (start + exit)).halted = true ∨
      (run input C mode accounting source sample (start + exit)).cursor = stage.val + 1 := by
    rcases hexit with hh | hgt
    · exact Or.inl hh
    · have hprevious := (hbefore (exit - 1) (by omega)).2
      have hstep := (run_cursor_step_bounds input C mode accounting source hl sample (start + (exit - 1))).2
      rw [hprevious, show start + (exit - 1) + 1 = start + exit by omega] at hstep
      exact Or.inr (by omega)
  obtain ⟨bit, hb⟩ : ∃ bit, (run input C mode accounting source sample start).ledger.written stage = some bit :=
    Option.ne_none_iff_exists'.mp hw
  have hwritten (k : ℕ) : (run input C mode accounting source sample (start + k)).ledger.written stage ≠ none := by
    rw [run_written_some_after input C mode accounting source hl sample start k stage bit hb]
    simp
  have htrace (k : ℕ) :
      postwriteStageTrace source sample.1 stage (run input C mode accounting source sample start).history k =
        (run input C mode accounting source sample (start + min k exit)).history := by
    induction k with
    | zero => simp only [postwriteStageTrace, Nat.zero_min, Nat.add_zero]
    | succ k ih =>
      rw [postwriteStageTrace, ih]
      by_cases hk : k < exit
      · rw [Nat.min_eq_left hk.le]
        obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting source hl sample (start + k)
        have hstep := run_actualStep_of_active input C mode accounting source hl sample (start + k) (hbefore k hk).1
        have hnext := postwriteStageStep_eq_nextHistory input C mode accounting source sample.1
          (input.truthAt sample.2) (worldTapes input sample.2) stage hp (hbefore k hk).1 (hbefore k hk).2 (hwritten k) hstep
        simpa only [Nat.min_eq_left (by omega : k + 1 ≤ exit), Nat.add_assoc] using hnext
      · have hke : exit ≤ k := by omega
        rw [Nat.min_eq_right hke, Nat.min_eq_right (by omega : exit ≤ k + 1)]
        obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting source hl sample (start + exit)
        exact postwriteStageStep_freeze_at_exit input C mode accounting source sample.1
          (input.truthAt sample.2) (worldTapes input sample.2) stage hp hexit
  refine ⟨exit, hbound, hone, hbefore, ?_⟩
  simpa only [Nat.min_eq_right hbound] using htrace 3

end PDROC
