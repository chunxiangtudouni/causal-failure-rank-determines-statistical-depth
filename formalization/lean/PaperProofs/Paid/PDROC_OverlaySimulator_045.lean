module

public import PaperProofs.Paid.PDROC_OverlaySimulator_037
public import PaperProofs.Paid.PDROC_OverlaySimulator_043
public import PaperProofs.Paid.PDROC_OverlaySimulator_044
public import PaperProofs.Paid.PDROC_OverlayCapture_002
public import PaperProofs.Paid.PDROC_OverlayFreshPorts_001
public import PaperProofs.Paid.PDROC_OverlayLaw_007

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

/-- The concrete Native overlay captures the exact full source stage exit
at a genuine first actual exit. The only pointwise inputs are actual local
MAP termination and the visible finite source guard predicate. -/
theorem overlay_minimal_exit_captured (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (hfinite : ∀ (record : AuxiliaryRecord) (coins : Bool × Bool), ∃ n : ℕ,
      (P.overlayRecordTest fee hfee record).rule.stop coins (worldTapes (P.input fee hfee) sample.2 stage) = (n : ℕ∞))
    (hgood : optionalSourceDrawGuardGood (sourceForOptionalHistory source) stage
      (overlayEventualReportedDraw P fee hfee C accounting source stage sample)) :
    OverlayMinimalExitCaptured P fee hfee C accounting source stage sample := by
  intro entry he
  obtain ⟨draw, hd, hg, hx⟩ := overlay_entry_capture_of_eventualReportedDraw P fee hfee C accounting source stage sample hgood entry he
  rcases hg.1 with ⟨decision, haction⟩ | hterminal
  · have hdecision : draw.record.decision = some decision := by
      rw [(overlaySeedDraw_some_spec P source sample.1 stage _ draw hd).1, haction]
      rfl
    have htruth := overlaySeedRowVirtualTruth_eq_reportTruth P fee hfee sample.1 stage draw.record
      ((P.input fee hfee).truthAt sample.2 stage) (worldTapes (P.input fee hfee) sample.2 stage) decision hdecision
    have hpost := hg.2
    dsimp only at hpost
    rw [htruth] at hpost hx
    obtain ⟨start, n, hfirst, _hentry, _hstop, hpre, ha, hc, hw, hpacket⟩ :=
      overlay_entered_write_packet_clock P fee hfee C accounting source sample stage entry he draw decision hd hdecision haction hfinite
    let base := start + n + 1
    have hwn : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample base).ledger.written stage ≠ none := by
      rw [hw]
      simp
    have hpostActual : sourcePostwriteGuardGood source sample.1.1 stage
        (overlayShadow P source sample.1 (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample base).history) := by
      rw [hpacket]
      exact hpost
    have hfresh : ∀ pair ∈ historyCommitments (overlayShadow P source sample.1
        (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample base).history), pair.1.stage ≠ stage := by
      rw [hpacket]
      exact overlay_entry_sourcePacket_no_current_commitment P fee hfee C accounting source sample stage entry he draw _
    obtain ⟨exit, _hbound, hexit, hbefore, htrace⟩ :=
      overlay_postwrite_first_exit P fee hfee C accounting source sample base stage ha hc hwn hfresh hpostActual
    rw [← hpacket, htrace] at hx
    refine ⟨start, n + 1 + exit, hfirst, ?_, ?_, ?_⟩
    · intro k hk
      by_cases hkpre : k ≤ n
      · exact hpre k hkpre
      · let j := k - (n + 1)
        have hj : j < exit := by dsimp only [j]; omega
        have htime : start + k = base + j := by dsimp only [base, j]; omega
        rw [htime]
        exact hbefore j hj
    · simpa only [base, Nat.add_assoc] using hx
    · simpa only [base, Nat.add_assoc] using hexit
  · let truth := overlayRowVirtualTruth P fee hfee draw.record ((P.input fee hfee).truthAt sample.2 stage)
      (sample.1.2.2 stage, worldTapes (P.input fee hfee) sample.2 stage)
    obtain ⟨start, hfirst, _hentry, ha, hc, hpacket, hh⟩ :=
      overlay_entered_terminal_packet_clock P fee hfee C accounting source sample stage entry he draw hd hterminal truth
    have hhalt := sourceDrawTerminalHistory_halted stage (overlayShadow P source sample.1 entry) draw truth hterminal
    rw [postwriteStageTrace_of_halted sample.1.1 stage _ hhalt 3, ← hpacket] at hx
    refine ⟨start, 1, hfirst, ?_, hx, Or.inl hh⟩
    intro k hk
    have hk0 : k = 0 := by omega
    subst k
    simpa only [Nat.add_zero] using And.intro ha hc

end PDROC
