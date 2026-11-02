module

public import PaperProofs.Paid.PDROC_Simulator_039

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

theorem postwriteStageStep_freeze_of_history_exit {Seed : Type*}
    (source : PolicyRule I Seed) (seed : Seed) (stage : I.Stage)
    (history : List (VisibleEvent I))
    (hexit : historyHalted history = true ∨ stage.val < historyCursor history) :
    postwriteStageStep source seed stage history = history := by
  rcases hexit with hh | hc
  · simp only [postwriteStageStep, hh, ↓reduceIte]
  · have hne : historyCursor history ≠ stage.val := by omega
    simp only [postwriteStageStep, hne, ↓reduceIte, ite_self]

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Three public source guards suffice for the concrete full postwrite
exit. There is no source Prefix, existential world, or source legality
premise. The actual run freezes at its first exit and never enters a later
fresh stage during this finite transducer. -/
theorem simulator_postwrite_exit_of_guardGood
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed)
    (seed : SimulatorSeed P Seed) (world : (P.input fee hfee).World)
    (start : ℕ) (stage : P.sharedInstance.Stage) (bit : Bool)
    (hc : (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
      (seed, world) start).cursor = stage.val)
    (hw : (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
      (seed, world) start).ledger.written stage = some bit)
    (hgood : ∀ k : ℕ, k < 3 →
      historyHalted (postwriteStageTrace source seed.1 stage
        (simulatorShadow P fee hfee source seed
          (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
            (seed, world) start).history) k) = false →
      historyCursor (postwriteStageTrace source seed.1 stage
        (simulatorShadow P fee hfee source seed
          (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
            (seed, world) start).history) k) = stage.val →
      historyAllowsAction (postwriteStageTrace source seed.1 stage
        (simulatorShadow P fee hfee source seed
          (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
            (seed, world) start).history) k)
        (source seed.1 (postwriteStageTrace source seed.1 stage
          (simulatorShadow P fee hfee source seed
            (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
              (seed, world) start).history) k))) :
    ∃ exit : ℕ, exit ≤ 3 ∧
      (∀ k < exit,
        (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
          (seed, world) (start + k)).halted = false ∧
        (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
          (seed, world) (start + k)).cursor = stage.val) ∧
      ((run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
        (seed, world) (start + exit)).halted = true ∨
        stage.val < (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
          (seed, world) (start + exit)).cursor) ∧
      simulatorShadow P fee hfee source seed
        (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
          (seed, world) (start + exit)).history =
        postwriteStageTrace source seed.1 stage
          (simulatorShadow P fee hfee source seed
            (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
              (seed, world) start).history) 3 := by
  classical
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  let initialShadow := simulatorShadow P fee hfee source seed
    (run input C.val .uncapped accounting actual (seed, world) start).history
  have hl := simulatorRule_legal P fee hfee C accounting source
  let E := fun k : ℕ => (run input C.val .uncapped accounting actual (seed, world) (start + k)).halted = true ∨
    stage.val < (run input C.val .uncapped accounting actual (seed, world) (start + k)).cursor
  have hthree := run_written_stage_exit_within_three input C.val C.property .uncapped accounting actual hl
    (seed, world) start stage hc (by rw [hw]; exact Option.some_ne_none bit)
  have he : ∃ k : ℕ, E k := ⟨3, hthree⟩
  let exit := Nat.find he
  have hExit : E exit := Nat.find_spec he
  have hBound : exit ≤ 3 := Nat.find_min' he hthree
  have hbefore (k : ℕ) (hk : k < exit) :
      (run input C.val .uncapped accounting actual (seed, world) (start + k)).halted = false ∧
      (run input C.val .uncapped accounting actual (seed, world) (start + k)).cursor = stage.val := by
    have hnot : ¬ E k := Nat.find_min he hk
    refine ⟨Bool.eq_false_iff.mpr (fun hh => hnot (Or.inl hh)), ?_⟩
    have hlo := run_cursor_monotone input C.val .uncapped accounting actual hl (seed, world) (Nat.le_add_right start k)
    change (run input C.val .uncapped accounting actual (seed, world) start).cursor ≤
      (run input C.val .uncapped accounting actual (seed, world) (start + k)).cursor at hlo
    rw [hc] at hlo
    have hhi : ¬ stage.val < (run input C.val .uncapped accounting actual (seed, world) (start + k)).cursor :=
      fun h => hnot (Or.inr h)
    omega
  have hshadowFields (k : ℕ) :
      historyHalted (simulatorShadow P fee hfee source seed
        (run input C.val .uncapped accounting actual (seed, world) (start + k)).history) =
          (run input C.val .uncapped accounting actual (seed, world) (start + k)).halted ∧
      historyCursor (simulatorShadow P fee hfee source seed
        (run input C.val .uncapped accounting actual (seed, world) (start + k)).history) =
          (run input C.val .uncapped accounting actual (seed, world) (start + k)).cursor := by
    obtain ⟨an, _, ap⟩ := run_has_prefix input C.val .uncapped accounting actual hl (seed, world) (start + k)
    have hp := simulatorReplay_sameProjection (simulatorSeedDraw P fee hfee source) seed
      (run input C.val .uncapped accounting actual (seed, world) (start + k)).history
    exact ⟨hp.2.2.2.2.symm.trans (prefix_historyHalted input C.val .uncapped accounting actual seed _ _ ap),
      hp.1.symm.trans (prefix_historyCursor input C.val .uncapped accounting actual seed _ _ ap)⟩
  have hTrace (k : ℕ) (hk : k ≤ 3) :
      postwriteStageTrace source seed.1 stage initialShadow k =
        simulatorShadow P fee hfee source seed
          (run input C.val .uncapped accounting actual (seed, world) (start + min k exit)).history := by
    induction k with
    | zero => simp only [postwriteStageTrace, Nat.zero_min, Nat.add_zero]; rfl
    | succ k ih =>
      have hi := ih (by omega : k ≤ 3)
      rw [postwriteStageTrace, hi]
      by_cases hke : k < exit
      · rw [Nat.min_eq_left hke.le]
        have hb := hbefore k hke
        have hf := hshadowFields k
        have hallow : historyAllowsAction
            (simulatorShadow P fee hfee source seed
              (run input C.val .uncapped accounting actual (seed, world) (start + k)).history)
            (source seed.1 (simulatorShadow P fee hfee source seed
              (run input C.val .uncapped accounting actual (seed, world) (start + k)).history)) := by
          have hi' : postwriteStageTrace source seed.1 stage initialShadow k =
              simulatorShadow P fee hfee source seed
                (run input C.val .uncapped accounting actual (seed, world) (start + k)).history := by
            simpa only [Nat.min_eq_left hke.le] using hi
          rw [← hi']
          exact hgood k (by omega) ((congrArg historyHalted hi').trans (hf.1.trans hb.1))
            ((congrArg historyCursor hi').trans (hf.2.trans hb.2))
        obtain ⟨an, _, ap⟩ := run_has_prefix input C.val .uncapped accounting actual hl (seed, world) (start + k)
        have astep := run_actualStep_of_active input C.val .uncapped accounting actual hl (seed, world) (start + k) hb.1
        have hwritten := run_written_some_after input C.val .uncapped accounting actual hl (seed, world) start k stage bit hw
        have hn := simulator_postwrite_step_shadow_of_historyAllowsAction P fee hfee C accounting source seed
          (input.truthAt world) (worldTapes input world) ap hb.1 stage hb.2
          (by rw [hwritten]; exact Option.some_ne_none bit) hallow astep
        simpa only [Nat.min_eq_left (by omega : k + 1 ≤ exit), Nat.add_assoc] using hn.symm
      · have hle : exit ≤ k := by omega
        rw [Nat.min_eq_right hle, Nat.min_eq_right (by omega : exit ≤ k + 1)]
        apply postwriteStageStep_freeze_of_history_exit
        rcases hExit with hh | hc
        · exact Or.inl ((hshadowFields exit).1.trans hh)
        · exact Or.inr (by rw [(hshadowFields exit).2]; exact hc)
  refine ⟨exit, hBound, hbefore, hExit, ?_⟩
  simpa only [Nat.min_eq_right hBound] using (hTrace 3 le_rfl).symm

end PDROC
