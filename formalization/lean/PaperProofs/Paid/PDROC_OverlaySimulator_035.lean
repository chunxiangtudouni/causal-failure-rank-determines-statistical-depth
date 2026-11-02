module

public import PaperProofs.Paid.PDROC_OverlaySimulator_034

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

/-- Ghost work vanishes at an actually wrong written current stage. -/
theorem overlay_wrong_ghost_nil (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (n : ℕ) (stage : P.sharedInstance.Stage)
    (hc : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).cursor = stage.val)
    (hw : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).ledger.written stage =
      some (!(run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).ledger.truth stage)) :
    overlaySeedGhost P source sample.1 (overlaySeedReplay P source sample.1
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).history) = [] := by
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  obtain ⟨k, _, hp⟩ := run_has_prefix input C.val .uncapped accounting actual
    (overlayRule_legal P fee hfee C accounting source) sample n
  have hcursor := (prefix_historyCursor input C.val .uncapped accounting actual sample.1 _ _ hp).trans hc
  have hs := simulatorStageAt_some (run input C.val .uncapped accounting actual sample n).history stage hcursor
  have hv := overlaySuccess_prefix_validHandle_of_wrong input C.val C.property.1.1 .uncapped accounting actual sample.1 _ _ hp stage hw
  apply overlayGhostAtCache_actualMismatch
  simp only [overlaySeedReplay, overlayReplay_seen]
  change overlayHasActualMismatch (run input C.val .uncapped accounting actual sample n).history = true
  simp only [overlayHasActualMismatch, hs, decide_eq_true_eq]
  exact hv

/-- With the visible source guard Good, the real postwrite guard is
nonbinding on every wrong actual branch, including failed payments. -/
theorem overlay_wrong_postwrite_rule_eq (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
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
    overlayRule P fee hfee source sample.1
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).history =
      reserialAction (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).history
        (fun _ bit => bit) (source sample.1.1 (overlayShadow P source sample.1
          (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).history)) := by
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  let cur := run input C.val .uncapped accounting actual sample n
  obtain ⟨k, _, hp⟩ := run_has_prefix input C.val .uncapped accounting actual
    (overlayRule_legal P fee hfee C accounting source) sample n
  have hhalt := (prefix_historyHalted input C.val .uncapped accounting actual sample.1 _ _ hp).trans ha
  have hcursor := (prefix_historyCursor input C.val .uncapped accounting actual sample.1 _ _ hp).trans hc
  have hs := simulatorStageAt_some cur.history stage hcursor
  have hwn : historyWritten cur.history stage ≠ none := by
    rw [prefix_historyWritten input C.val .uncapped accounting actual sample.1 _ _ hp stage, hw]
    simp
  change historyHalted cur.history = false at hhalt
  have hg := overlay_wrong_ghost_nil P fee hfee C accounting source sample n stage hc hw
  change overlaySeedGhost P source sample.1 (overlaySeedReplay P source sample.1 cur.history) = [] at hg
  have hcand : overlayCandidate P fee hfee source sample.1 cur.history =
      reserialAction cur.history (fun _ bit => bit) (source sample.1.1 (overlayShadow P source sample.1 cur.history)) := by
    simp only [overlayCandidate, overlayCandidateAtCache, hhalt, Bool.false_eq_true, ite_false,
      hs, hwn, overlayPostwriteAction, hg, overlayGhostEvents, List.map_nil, List.append_nil, overlayShadow]
  have hactual : historyAllowsAction cur.history
      (reserialAction cur.history (fun _ bit => bit) (source sample.1.1 (overlayShadow P source sample.1 cur.history))) := by
    exact overlay_wrong_guard_transport input C.val C.property.1.1 .uncapped accounting actual sample.1 _ _
      source sample.1.1 (overlaySeedDraw P source) (overlaySeedMark P) sample.1 hp stage hc hw _ hallow
  change (if historyAllowsAction cur.history (overlayCandidate P fee hfee source sample.1 cur.history) then
    overlayCandidate P fee hfee source sample.1 cur.history else .abandon) = _
  rw [hcand, ite_eq_left hactual]

end PDROC
