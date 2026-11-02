module

public import PaperProofs.Paid.PDROC_OverlaySimulator_038
public import PaperProofs.Paid.PDROC_StageExit_001
public import PaperProofs.Paid.PDROC_SimulatorLaw_009

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

/-- The first real postwrite exit on an actually wrong stage has the full
source three-step shadow history. Only the visible finite Good predicate is
used, and the genuine physical first-exit clock is retained. -/
theorem overlay_wrong_postwrite_first_exit (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (start : ℕ) (stage : P.sharedInstance.Stage)
    (ha : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).halted = false)
    (hc : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).cursor = stage.val)
    (hw : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).ledger.written stage =
      some (!(run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).ledger.truth stage))
    (hgood : sourcePostwriteGuardGood source sample.1.1 stage (overlayShadow P source sample.1
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).history)) :
    ∃ exit : ℕ, exit ≤ 3 ∧
      ((run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (start + exit)).halted = true ∨
        (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (start + exit)).cursor = stage.val + 1) ∧
      (∀ k < exit, (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (start + k)).halted = false ∧
        (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (start + k)).cursor = stage.val) ∧
      postwriteStageTrace source sample.1.1 stage (overlayShadow P source sample.1
        (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).history) 3 =
        overlayShadow P source sample.1 (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (start + exit)).history := by
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  let view := overlayShadow P source sample.1
  have hl := overlayRule_legal P fee hfee C accounting source
  have hwn : (run input C.val .uncapped accounting actual sample start).ledger.written stage ≠ none := by rw [hw]; simp
  obtain ⟨exit, hb, hexit, hbefore, _hx⟩ := postwrite_first_exit input C.val C.property .uncapped accounting actual hl sample start stage ha hc hwn
  have hfields (clock : ℕ) :
      historyHalted (view (run input C.val .uncapped accounting actual sample clock).history) =
        (run input C.val .uncapped accounting actual sample clock).halted ∧
      historyCursor (view (run input C.val .uncapped accounting actual sample clock).history) =
        (run input C.val .uncapped accounting actual sample clock).cursor := by
    obtain ⟨m, _, hp⟩ := run_has_prefix input C.val .uncapped accounting actual hl sample clock
    have hpj := overlayReplay_historyProjection (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) sample.1
      (run input C.val .uncapped accounting actual sample clock).history
    exact ⟨hpj.2.2.symm.trans (prefix_historyHalted input C.val .uncapped accounting actual sample.1 _ _ hp),
      hpj.1.symm.trans (prefix_historyCursor input C.val .uncapped accounting actual sample.1 _ _ hp)⟩
  have hwrong (k : ℕ) : (run input C.val .uncapped accounting actual sample (start + k)).ledger.written stage =
      some (!(run input C.val .uncapped accounting actual sample (start + k)).ledger.truth stage) := by
    rw [run_written_some_after input C.val .uncapped accounting actual hl sample start k stage _ hw,
      congrFun (run_truth input C.val .uncapped accounting actual hl sample start) stage,
      congrFun (run_truth input C.val .uncapped accounting actual hl sample (start + k)) stage]
  have htrace (k : ℕ) (hk3 : k ≤ 3) :
      postwriteStageTrace source sample.1.1 stage (view (run input C.val .uncapped accounting actual sample start).history) k =
        view (run input C.val .uncapped accounting actual sample (start + min k exit)).history := by
    induction k with
    | zero => simp only [postwriteStageTrace, Nat.zero_min, Nat.add_zero]
    | succ k ih =>
      rw [postwriteStageTrace, ih (by omega)]
      by_cases hk : k < exit
      · rw [Nat.min_eq_left hk.le]
        have hallow := hgood k (by omega)
        rw [ih (by omega), Nat.min_eq_left hk.le] at hallow
        have hp := hbefore k hk
        have hpermit := hallow ((hfields (start + k)).1.trans hp.1) ((hfields (start + k)).2.trans hp.2)
        have hs := overlay_wrong_postwrite_step_shadow P fee hfee C accounting source sample (start + k) stage hp.1 hp.2 (hwrong k) hpermit
        simpa only [Nat.min_eq_left (by omega : k + 1 ≤ exit), Nat.add_assoc] using hs
      · have hke : exit ≤ k := by omega
        rw [Nat.min_eq_right hke, Nat.min_eq_right (by omega : exit ≤ k + 1)]
        rcases hexit with hh | hcExit
        · simp only [postwriteStageStep, (hfields (start + exit)).1.trans hh, ite_true]
        · have hne : historyCursor (view (run input C.val .uncapped accounting actual sample (start + exit)).history) ≠ stage.val := by
            rw [(hfields (start + exit)).2, hcExit]
            omega
          simp only [postwriteStageStep, hne, ite_false, ite_self]
  exact ⟨exit, hb, hexit, hbefore, by simpa only [Nat.min_eq_right hb] using htrace 3 le_rfl⟩

end PDROC
