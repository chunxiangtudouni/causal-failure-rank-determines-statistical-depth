module

public import PaperProofs.Paid.PDROC_OverlayCorrect_001
public import PaperProofs.Paid.PDROC_OverlayGhostExit_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

/-- On an actually correct written stage, all remaining source repairs
are checked virtual calls; one real exit captures the complete trace. -/
theorem overlay_correct_postwrite_exit (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (start : ℕ) (stage : P.sharedInstance.Stage)
    (ha : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).halted = false)
    (hc : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).cursor = stage.val)
    (hw : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).ledger.written stage =
      some ((run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).ledger.truth stage))
    (hfresh : ∀ pair ∈ historyCommitments (overlayShadow P source sample.1
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).history), pair.1.stage ≠ stage)
    (hgood : sourcePostwriteGuardGood source sample.1.1 stage (overlayShadow P source sample.1
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).history)) :
    postwriteStageTrace source sample.1.1 stage (overlayShadow P source sample.1
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).history) 3 =
      overlayShadow P source sample.1 (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (start + 1)).history ∧
    ((run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (start + 1)).halted = true ∨
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (start + 1)).cursor = stage.val + 1) := by
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  let cur := run input C.val .uncapped accounting actual sample start
  let cache := overlaySeedReplay P source sample.1 cur.history
  let virtual := overlayShadow P source sample.1 cur.history
  change cur.ledger.written stage = some (cur.ledger.truth stage) at hw
  have hl := overlayRule_legal P fee hfee C accounting source
  obtain ⟨k, _, hp⟩ := run_has_prefix input C.val .uncapped accounting actual hl sample start
  have hpj := overlayReplay_historyProjection (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) sample.1 cur.history
  have hrealcur : historyCursor cur.history = stage.val :=
    (prefix_historyCursor input C.val .uncapped accounting actual sample.1 _ _ hp).trans hc
  have hstage := simulatorStageAt_some cur.history stage hrealcur
  have hnot : ¬ historyValidHandle cur.history ⟨stage, historyWriteSerial cur.history stage⟩ := by
    intro hv
    have hv' := historyValidHandle_sound input C.val C.property.1.1 .uncapped accounting actual sample.1 _ _ hp _ hv
    have hwrong : cur.ledger.written stage = some (!cur.ledger.truth stage) := hv'.1
    rw [hw] at hwrong
    cases ht : cur.ledger.truth stage <;> simp [ht] at hwrong
  have hfalse : overlayHasActualMismatch cur.history = false := by
    simpa only [overlayHasActualMismatch, hstage, decide_eq_false_iff_not] using hnot
  have hseen : cache.seen = cur.history :=
    overlayReplay_seen (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) sample.1 cur.history
  have hg0 : overlaySeedGhost P source sample.1 cache = overlayGhostCalls 2 source sample.1.1 cache.shadow := by
    change (if overlayHasActualMismatch cache.seen then [] else overlayGhostCalls 2 source sample.1.1 cache.shadow) = _
    simp only [hseen, hfalse, Bool.false_eq_true, ite_false]
  have hg : overlaySeedGhost P source sample.1 cache = overlayGhostCalls 2 source sample.1.1 virtual := hg0
  have hva : historyHalted virtual = false := hpj.2.2.symm.trans
    ((prefix_historyHalted input C.val .uncapped accounting actual sample.1 _ _ hp).trans ha)
  have hvc : historyCursor virtual = stage.val := hpj.1.symm.trans hrealcur
  have hwn : cur.ledger.written stage ≠ none := by rw [hw]; simp
  have hvw : historyWritten virtual stage ≠ none := by
    intro hn
    have hn' := (hpj.2.1 stage).mpr hn
    rw [prefix_historyWritten input C.val .uncapped accounting actual sample.1 _ _ hp stage] at hn'
    exact hwn hn'
  have hexit := overlayGhostCalls_two_source_exit source sample.1.1 stage virtual hva hvc hvw hfresh hgood
  have htrace := overlayGhostCalls_two_postwriteTrace_three source sample.1.1 stage virtual hva hvc hvw hfresh hgood
  rw [← hg] at hexit htrace
  have hcap := overlay_postwrite_exit_capture P fee hfee C accounting source sample start stage ha hc hwn hexit
  exact ⟨htrace.trans hcap.1.symm, hcap.2⟩

end PDROC
