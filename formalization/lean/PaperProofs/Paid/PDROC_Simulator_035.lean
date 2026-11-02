module

public import PaperProofs.Paid.PDROC_Simulator_034

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

theorem simulatorReplay_terminal_shadow {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (stage : I.Stage) (abandoned : Bool)
    (hc : historyCursor history = stage.val) (hw : historyWritten history stage = none) :
    (simulatorReplay draw seed (history ++ [if abandoned then .abandoned else .stopped])).shadow =
      ((simulatorReplay draw seed history).shadow ++
        simulatorReviewPacket stage (simulatorDrawRecord (draw seed stage (simulatorReplay draw seed history).shadow))) ++
        [if abandoned then .abandoned else .stopped] := by
  have hc' : historyCursor (simulatorReplay draw seed history).seen < I.stageCount := by
    rw [simulatorReplay_seen, hc]
    exact stage.isLt
  have he : (⟨historyCursor (simulatorReplay draw seed history).seen, hc'⟩ : I.Stage) = stage := by
    apply Fin.ext
    simpa only [simulatorReplay_seen] using hc
  have hw' : historyWritten (simulatorReplay draw seed history).seen stage = none := by
    simpa only [simulatorReplay_seen] using hw
  cases abandoned <;>
    simp only [Bool.false_eq_true, ↓reduceIte, simulatorReplay_append_event, simulatorStep,
      hc', ↓reduceDIte, he, hw', simulatorAppend, List.append_assoc]

universe u
variable {Seed : Type u}

theorem simulatorRule_prewrite_terminal_eq (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (source : PolicyRule P.sharedInstance Seed)
    (seed : SimulatorSeed P Seed) (history : List (VisibleEvent P.sharedInstance))
    (stage : P.sharedInstance.Stage) (draw : SimulatorDraw P.sharedInstance) (abandoned : Bool)
    (hh : historyHalted history = false) (hc : historyCursor history = stage.val)
    (hw : historyWritten history stage = none)
    (hdraw : simulatorSeedDraw P fee hfee source seed stage (simulatorShadow P fee hfee source seed history) = some draw)
    (haction : draw.action = if abandoned then .abandon else .stop) :
    simulatorRule P fee hfee source seed history = if abandoned then .abandon else .stop := by
  have hd : draw.record.decision = none := by
    have hd := (simulatorSeedDraw_some_spec P fee hfee source seed stage _ draw hdraw).1
    cases abandoned <;> simpa only [haction, Bool.false_eq_true, ↓reduceIte, optionWriteBit] using hd
  have hr := simulatorCandidate_prewrite P fee hfee source seed history stage hh hc hw
  rw [hdraw] at hr
  simp only [simulatorDrawAction, hd] at hr
  cases abandoned <;>
    simp only [simulatorRule, hr, haction, Bool.false_eq_true, ↓reduceIte, reserialAction, historyAllowsAction]

theorem simulator_terminal_record_shadow_packet (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed) (world : (P.input fee hfee).World)
    (start : ℕ) (s : State P.sharedInstance) (stage : P.sharedInstance.Stage)
    (draw : SimulatorDraw P.sharedInstance) (abandoned : Bool) (virtualTruth : Bool)
    (hs0 : run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) start = s)
    (ha : s.halted = false) (hc : s.cursor = stage.val) (hw : s.ledger.written stage = none)
    (hdraw : simulatorSeedDraw P fee hfee source seed stage (simulatorShadow P fee hfee source seed s.history) = some draw)
    (haction : draw.action = if abandoned then .abandon else .stop) :
    (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
      (seed, world) (start + 1)).halted = true ∧
    simulatorShadow P fee hfee source seed
      (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
        (seed, world) (start + 1)).history =
      sourceDrawTerminalHistory stage (simulatorShadow P fee hfee source seed s.history) draw virtualTruth := by
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  obtain ⟨k, _, hp⟩ := run_has_prefix input C.val .uncapped accounting actual
    (simulatorRule_legal P fee hfee C accounting source) (seed, world) start
  have hp' : Prefix input C.val .uncapped accounting actual seed _ _ k s := hs0 ▸ hp
  have hh := (prefix_historyHalted input C.val .uncapped accounting actual seed _ _ hp').trans ha
  have hhc := (prefix_historyCursor input C.val .uncapped accounting actual seed _ _ hp').trans hc
  have hhw := (prefix_historyWritten input C.val .uncapped accounting actual seed _ _ hp' stage).trans hw
  have hrule := simulatorRule_prewrite_terminal_eq P fee hfee source seed s.history stage draw abandoned hh hhc hhw hdraw haction
  have hrun : run input C.val .uncapped accounting actual (seed, world) (start + 1) = stopState s abandoned := by
    apply run_succ_of_step input C.val .uncapped accounting actual (seed, world) start _
    · exact (congrArg State.halted hs0).trans ha
    · rw [hs0]
      change Step input C.val .uncapped accounting (worldTapes input world) s
        (simulatorRule P fee hfee source seed s.history) (stopState s abandoned)
      rw [hrule]
      cases abandoned
      · exact .stop s ha
      · exact .abandon s ha
  rw [hrun]
  refine ⟨rfl, ?_⟩
  have hf := simulatorReplay_terminal_shadow (simulatorSeedDraw P fee hfee source) seed s.history stage abandoned hhc hhw
  have hrec : simulatorDrawRecord (simulatorSeedDraw P fee hfee source seed stage
      (simulatorShadow P fee hfee source seed s.history)) = draw.record := by rw [hdraw]; rfl
  change simulatorShadow P fee hfee source seed
    (s.history ++ [if abandoned then .abandoned else .stopped]) = _ at hf
  simp only [simulatorShadow] at hrec hf
  rw [hrec] at hf
  cases abandoned <;> simpa only [stopState, Bool.false_eq_true, ↓reduceIte,
    sourceDrawTerminalHistory, haction, simulatorShadow] using hf

end PDROC
