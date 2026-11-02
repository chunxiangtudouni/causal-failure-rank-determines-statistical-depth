module

public import PaperProofs.Paid.PDROC_OverlaySimulator_034
public import PaperProofs.Paid.PDROC_OverlaySimulator_032

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

/-- An unwritten actual current stage admits no checked ghost call. -/
theorem overlayGhostAtCache_unwritten_nil
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Actual Source : Type*}
    (rule : PolicyRule I Actual) (seed : Actual) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (stage : I.Stage) (hc : s.cursor = stage.val) (hw : s.ledger.written stage = none)
    (source : PolicyRule I Source) (oldSeed : Source) (cache : SimulatorCache I)
    (hseen : cache.seen = s.history) (hproj : OverlayHistoryProjection s.history cache.shadow) :
    overlayGhostAtCache source oldSeed cache = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro call hm
  have hcorrect := overlaySuccess_ghost_member_correct input C hearly mode accounting rule seed truth tapes hp
    source oldSeed cache hseen hproj call hm
  have hcalls : call ∈ overlayGhostCalls 2 source oldSeed cache.shadow := by
    unfold overlayGhostAtCache at hm
    split at hm
    · cases hm
    · exact hm
  have hstage := (overlaySuccess_ghostTrace_member source oldSeed cache.shadow _
    (overlayGhostCalls_trace 2 source oldSeed cache.shadow) call hcalls).1
  have he : call.2.1.stage = stage := Fin.ext (hstage.trans (hproj.1.symm.trans
    ((prefix_historyCursor input C mode accounting rule seed truth tapes hp).trans hc)))
  rw [he, hw] at hcorrect
  cases hcorrect

/-- A nonwriting sampled source terminal action contributes its full old
review packet and the identical stop/abandon event, with no ghosts. -/
theorem overlayReplay_prewrite_terminal_full {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (stage : I.Stage)
    (hc : historyCursor history = stage.val) (hw : historyWritten history stage = none)
    (hg : ghost seed (overlayReplay draw mark ghost seed history) = [])
    (sampled : SimulatorDraw I) (hd : draw seed stage (overlayReplay draw mark ghost seed history).shadow = some sampled)
    (truth : Bool) (hterminal : sampled.action = .stop ∨ sampled.action = .abandon) :
    (overlayReplay draw mark ghost seed (history ++ postwriteResponse sampled.action)).shadow =
      sourceDrawTerminalHistory stage (overlayReplay draw mark ghost seed history).shadow sampled truth := by
  have hlt : historyCursor (overlayReplay draw mark ghost seed history).seen < I.stageCount := by
    rw [overlayReplay_seen, hc]
    exact stage.isLt
  have he : (⟨historyCursor (overlayReplay draw mark ghost seed history).seen, hlt⟩ : I.Stage) = stage :=
    Fin.ext (by simpa only [overlayReplay_seen] using hc)
  have hwn : historyWritten (overlayReplay draw mark ghost seed history).seen stage = none := by
    simpa only [overlayReplay_seen] using hw
  rcases hterminal with hs | hs
  · rw [sourceDrawTerminalHistory_stop stage _ sampled truth hs, hs]
    simp only [postwriteResponse, overlayReplay_append_event, overlayStep, hlt, ↓reduceDIte,
      he, hwn, ite_true, simulatorAppend, hd, simulatorDrawRecord, Option.map_some, Option.getD_some,
      hg, overlayGhostEvents, List.map_nil, List.nil_append, List.append_assoc]
  · rw [sourceDrawTerminalHistory_abandon stage _ sampled truth hs, hs]
    simp only [postwriteResponse, overlayReplay_append_event, overlayStep, hlt, ↓reduceDIte,
      he, hwn, ite_true, simulatorAppend, hd, simulatorDrawRecord, Option.map_some, Option.getD_some,
      hg, overlayGhostEvents, List.map_nil, List.nil_append, List.append_assoc]

end PDROC
