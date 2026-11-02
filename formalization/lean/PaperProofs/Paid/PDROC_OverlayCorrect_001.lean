module

public import PaperProofs.Paid.PDROC_OverlaySimulator_009
public import PaperProofs.Paid.PDROC_OverlaySimulator_005
public import PaperProofs.Paid.PDROC_SimulatorLaw_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

/-- Exit actions insert the entire checked ghost packet exactly once. -/
theorem overlayReplay_exit_response {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (stage : I.Stage)
    (hc : historyCursor history = stage.val) (hw : historyWritten history stage ≠ none)
    (action : Action I) (hexit : action = .advance stage ∨ action = .stop ∨ action = .abandon) :
    (overlayReplay draw mark ghost seed (history ++ postwriteResponse action)).shadow =
      (overlayReplay draw mark ghost seed history).shadow ++
        overlayGhostEvents (ghost seed (overlayReplay draw mark ghost seed history)) ++ postwriteResponse action := by
  have hlt : historyCursor (overlayReplay draw mark ghost seed history).seen < I.stageCount := by
    rw [overlayReplay_seen, hc]
    exact stage.isLt
  have he : (⟨historyCursor (overlayReplay draw mark ghost seed history).seen, hlt⟩ : I.Stage) = stage :=
    Fin.ext (by simpa only [overlayReplay_seen] using hc)
  have hwn : historyWritten (overlayReplay draw mark ghost seed history).seen stage ≠ none := by
    simpa only [overlayReplay_seen] using hw
  rcases hexit with rfl | rfl | rfl
  all_goals simp only [postwriteResponse, overlayReplay_append_event, overlayStep,
    hlt, ↓reduceDIte, he, hwn, ite_false, simulatorAppend, List.append_assoc]

/-- A genuine Native exit response halts or increments exactly one cursor. -/
theorem overlay_exit_step_result (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I} (stage : I.Stage) (hc : s.cursor = stage.val)
    (hs : Step input C mode accounting tapes s action next)
    (hexit : action = .advance stage ∨ action = .stop ∨ action = .abandon) :
    next.halted = true ∨ next.cursor = stage.val + 1 := by
  rcases hexit with rfl | rfl | rfl
  · cases hs
    exact Or.inr (congrArg (fun x => x + 1) hc)
  · cases hs
    exact Or.inl rfl
  · cases hs
    exact Or.inl rfl

universe u
variable {Seed : Type u}

/-- Any source exit after the checked ghost packet is one genuine physical
exit with the exact full source-visible response. -/
theorem overlay_postwrite_exit_capture (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (n : ℕ) (stage : P.sharedInstance.Stage)
    (ha : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).halted = false)
    (hc : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).cursor = stage.val)
    (hw : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).ledger.written stage ≠ none)
    (hexit :
      let cache := overlaySeedReplay P source sample.1
        (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).history
      let final := cache.shadow ++ overlayGhostEvents (overlaySeedGhost P source sample.1 cache)
      source sample.1.1 final = .advance stage ∨ source sample.1.1 final = .stop ∨ source sample.1.1 final = .abandon) :
    let cache := overlaySeedReplay P source sample.1
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).history
    let final := cache.shadow ++ overlayGhostEvents (overlaySeedGhost P source sample.1 cache)
    overlayShadow P source sample.1 (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (n + 1)).history =
      final ++ postwriteResponse (source sample.1.1 final) ∧
    ((run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (n + 1)).halted = true ∨
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (n + 1)).cursor = stage.val + 1) := by
  dsimp only at hexit ⊢
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  let cur := run input C.val .uncapped accounting actual sample n
  let cache := overlaySeedReplay P source sample.1 cur.history
  let final := cache.shadow ++ overlayGhostEvents (overlaySeedGhost P source sample.1 cache)
  let action := source sample.1.1 final
  have hl := overlayRule_legal P fee hfee C accounting source
  obtain ⟨k, _, hp⟩ := run_has_prefix input C.val .uncapped accounting actual hl sample n
  have hhalt : historyHalted cur.history = false :=
    (prefix_historyHalted input C.val .uncapped accounting actual sample.1 _ _ hp).trans ha
  have hcursor : historyCursor cur.history = stage.val :=
    (prefix_historyCursor input C.val .uncapped accounting actual sample.1 _ _ hp).trans hc
  have hstage := simulatorStageAt_some cur.history stage hcursor
  have hwn : historyWritten cur.history stage ≠ none := by
    rwa [prefix_historyWritten input C.val .uncapped accounting actual sample.1 _ _ hp stage]
  have he : action = .advance stage ∨ action = .stop ∨ action = .abandon := hexit
  have hreserial : reserialAction cur.history (fun _ bit => bit) action = action := by
    rcases he with hh | hh | hh <;> rw [hh] <;> rfl
  have hcandidate : overlayCandidate P fee hfee source sample.1 cur.history = action := by
    simp only [overlayCandidate, overlayCandidateAtCache, hhalt, Bool.false_eq_true, ite_false,
      hstage, hwn, overlayPostwriteAction]
    exact hreserial
  have hallow : historyAllowsAction cur.history action := by
    rcases he with hh | hh | hh
    · rw [hh]; exact ⟨hcursor, hwn⟩
    · rw [hh]; trivial
    · rw [hh]; trivial
  have hrule : actual sample.1 cur.history = action := by
    change (if historyAllowsAction cur.history (overlayCandidate P fee hfee source sample.1 cur.history) then
      overlayCandidate P fee hfee source sample.1 cur.history else .abandon) = _
    rw [hcandidate, ite_eq_left hallow]
  have hs := run_actualStep_of_active input C.val .uncapped accounting actual hl sample n ha
  rw [hrule] at hs
  have hh := writtenStage_step_history input C.val .uncapped accounting (worldTapes input sample.2) stage hc hw hs
  have hresponse := overlayReplay_exit_response (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source)
    sample.1 cur.history stage hcursor hwn action he
  refine ⟨?_, overlay_exit_step_result input C.val .uncapped accounting (worldTapes input sample.2) stage hc hs he⟩
  rw [hh]
  exact hresponse

end PDROC
