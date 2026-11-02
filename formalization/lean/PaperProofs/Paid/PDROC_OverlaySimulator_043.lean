module

public import PaperProofs.Paid.PDROC_OverlaySimulator_042

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

theorem overlay_terminal_step_history (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I} (hs : Step input C mode accounting tapes s action next)
    (ht : action = .stop ∨ action = .abandon) :
    next.history = s.history ++ postwriteResponse action ∧ next.halted = true := by
  rcases ht with rfl | rfl <;> cases hs <;> exact ⟨rfl, rfl⟩

universe u
variable {Seed : Type u}

/-- Stop and abandonment of a sampled nonwriting record are distinct real
terminal steps carrying the full source review packet. -/
theorem overlay_entered_terminal_packet_clock (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (stage : P.sharedInstance.Stage) (entry : List (VisibleEvent P.sharedInstance))
    (he : entryHistory (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) stage sample = some entry)
    (draw : SimulatorDraw P.sharedInstance)
    (hdraw : overlaySeedDraw P source sample.1 stage (overlayShadow P source sample.1 entry) = some draw)
    (hterminal : draw.action = .stop ∨ draw.action = .abandon) (virtualTruth : Bool) :
    ∃ start : ℕ,
      FirstEntryAt (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) stage.val start sample ∧
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).history = entry ∧
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).halted = false ∧
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).cursor = stage.val ∧
      overlayShadow P source sample.1 (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source)
        sample (start + 1)).history = sourceDrawTerminalHistory stage (overlayShadow P source sample.1 entry) draw virtualTruth ∧
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (start + 1)).halted = true := by
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  have hl := overlayRule_legal P fee hfee C accounting source
  obtain ⟨start, hc, hbefore, hh⟩ := (entryHistory_some_iff input C.val .uncapped accounting actual stage sample entry).mp he
  let s := run input C.val .uncapped accounting actual sample start
  have he' : FirstEntryAt input C.val .uncapped accounting actual stage.val start sample := ⟨hc, hbefore⟩
  obtain ⟨ha, hunborn⟩ := firstEntryAt_unborn input C.val .uncapped accounting actual hl sample stage.val start he'
  have hw := (hunborn stage le_rfl).1
  obtain ⟨k, _, hp⟩ := run_has_prefix input C.val .uncapped accounting actual hl sample start
  have hhh := (prefix_historyHalted input C.val .uncapped accounting actual sample.1 _ _ hp).trans ha
  have hhc := (prefix_historyCursor input C.val .uncapped accounting actual sample.1 _ _ hp).trans hc
  have hhw := (prefix_historyWritten input C.val .uncapped accounting actual sample.1 _ _ hp stage).trans hw
  have hdraw0 : overlaySeedDraw P source sample.1 stage (overlayShadow P source sample.1 s.history) = some draw := by
    rw [show s.history = entry from hh]
    exact hdraw
  have hd : draw.record.decision = none := by
    have hd' := (overlaySeedDraw_some_spec P source sample.1 stage _ draw hdraw0).1
    rcases hterminal with ht | ht <;> rw [hd', ht] <;> rfl
  have hreserial : reserialAction s.history (fun _ bit => bit) draw.action = draw.action := by
    rcases hterminal with ht | ht <;> rw [ht] <;> rfl
  have hcand : overlayCandidate P fee hfee source sample.1 s.history = draw.action := by
    have hcand' := overlayCandidate_prewrite P fee hfee source sample.1 s.history stage hhh hhc hhw
    simpa only [hdraw0, overlayDrawAction, hd, hreserial] using hcand'
  have hallow : historyAllowsAction s.history draw.action := by
    rcases hterminal with ht | ht <;> rw [ht] <;> trivial
  have hrule : actual sample.1 s.history = draw.action := by
    change (if historyAllowsAction s.history (overlayCandidate P fee hfee source sample.1 s.history) then
      overlayCandidate P fee hfee source sample.1 s.history else .abandon) = _
    rw [hcand, ite_eq_left hallow]
  have hs := run_actualStep_of_active input C.val .uncapped accounting actual hl sample start ha
  rw [hrule] at hs
  have hnext := overlay_terminal_step_history input C.val .uncapped accounting (worldTapes input sample.2) hs hterminal
  have hpj := overlayReplay_historyProjection (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) sample.1 s.history
  have hg : overlaySeedGhost P source sample.1 (overlaySeedReplay P source sample.1 s.history) = [] :=
    overlayGhostAtCache_unwritten_nil input C.val C.property.1.1 .uncapped accounting actual sample.1 _ _ hp stage hc hw
      source sample.1.1 _ (overlayReplay_seen _ _ _ _ _) hpj
  have hpacket := overlayReplay_prewrite_terminal_full (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source)
    sample.1 s.history stage hhc hhw hg draw hdraw0 virtualTruth hterminal
  have hsentry : s.history = entry := hh
  rw [hsentry] at hpacket
  refine ⟨start, he', hh, ha, hc, ?_, hnext.2⟩
  rw [hnext.1]
  simpa only [overlayShadow, overlaySeedReplay, hh] using hpacket

end PDROC
