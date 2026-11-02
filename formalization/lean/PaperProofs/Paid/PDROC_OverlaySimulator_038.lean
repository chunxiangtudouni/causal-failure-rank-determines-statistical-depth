module

public import PaperProofs.Paid.PDROC_OverlaySimulator_036

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

/-- A wrong physical postwrite step realizes one exact full source step. -/
theorem overlay_wrong_postwrite_step_shadow (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (n : ℕ) (stage : P.sharedInstance.Stage)
    (ha : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).halted = false)
    (hc : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).cursor = stage.val)
    (hw : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).ledger.written stage =
      some (!(run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).ledger.truth stage))
    (hallow : historyAllowsAction (overlayShadow P source sample.1
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).history)
      (source sample.1.1 (overlayShadow P source sample.1
        (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).history))) :
    postwriteStageStep source sample.1.1 stage (overlayShadow P source sample.1
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).history) =
      overlayShadow P source sample.1 (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (n + 1)).history := by
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  let cur := run input C.val .uncapped accounting actual sample n
  have hl := overlayRule_legal P fee hfee C accounting source
  obtain ⟨k, _, hp⟩ := run_has_prefix input C.val .uncapped accounting actual hl sample n
  have hproj := overlayReplay_historyProjection (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) sample.1 cur.history
  have hvhalt : historyHalted (overlayShadow P source sample.1 cur.history) = false :=
    hproj.2.2.symm.trans ((prefix_historyHalted input C.val .uncapped accounting actual sample.1 _ _ hp).trans ha)
  have hvcursor : historyCursor (overlayShadow P source sample.1 cur.history) = stage.val :=
    hproj.1.symm.trans ((prefix_historyCursor input C.val .uncapped accounting actual sample.1 _ _ hp).trans hc)
  have hcur : historyCursor cur.history = stage.val :=
    (prefix_historyCursor input C.val .uncapped accounting actual sample.1 _ _ hp).trans hc
  have hwn : cur.ledger.written stage ≠ none := by rw [hw]; simp
  have hhistorywritten : historyWritten cur.history stage ≠ none := by
    rwa [prefix_historyWritten input C.val .uncapped accounting actual sample.1 _ _ hp stage]
  have hs := run_actualStep_of_active input C.val .uncapped accounting actual hl sample n ha
  have hhistory := writtenStage_step_history input C.val .uncapped accounting (worldTapes input sample.2) stage hc hwn hs
  have hrule := overlay_wrong_postwrite_rule_eq P fee hfee C accounting source sample n stage ha hc hw hallow
  change actual sample.1 cur.history = reserialAction cur.history (fun _ bit => bit)
    (source sample.1.1 (overlayShadow P source sample.1 cur.history)) at hrule
  change (run input C.val .uncapped accounting actual sample (n + 1)).history =
    cur.history ++ postwriteResponse (actual sample.1 cur.history) at hhistory
  rw [hrule] at hhistory
  have hg := overlay_wrong_ghost_nil P fee hfee C accounting source sample n stage hc hw
  have hresponse := overlayReplay_postwrite_response (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source)
    sample.1 cur.history stage hcur hhistorywritten hg _ hallow
  change postwriteStageStep source sample.1.1 stage (overlayShadow P source sample.1 cur.history) =
    overlayShadow P source sample.1 (run input C.val .uncapped accounting actual sample (n + 1)).history
  simp only [postwriteStageStep, hvhalt, Bool.false_eq_true, ite_false, hvcursor, ite_true]
  rw [hhistory]
  exact hresponse.symm

end PDROC
