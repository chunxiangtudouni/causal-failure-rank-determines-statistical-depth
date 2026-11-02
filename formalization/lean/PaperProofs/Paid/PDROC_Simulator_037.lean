module

public import PaperProofs.Paid.PDROC_Simulator_035
public import PaperProofs.Paid.PDROC_Simulator_036

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

theorem postwriteStageTrace_of_historyHalted {Seed : Type*}
    (source : PolicyRule I Seed) (seed : Seed) (stage : I.Stage)
    (history : List (VisibleEvent I)) (hh : historyHalted history = true) (n : ℕ) :
    postwriteStageTrace source seed stage history n = history := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [postwriteStageTrace, ih, postwriteStageStep, hh, ↓reduceIte]

theorem sourceDrawStageExit_terminal {Seed : Type*}
    (source : PolicyRule I Seed) (seed : Seed) (stage : I.Stage)
    (entry : List (VisibleEvent I)) (draw : SimulatorDraw I) (abandoned truth : Bool)
    (haction : draw.action = if abandoned then .abandon else .stop) :
    sourceDrawStageExit source stage (((seed, entry), draw), truth) =
      (seed, sourceDrawTerminalHistory stage entry draw truth) := by
  have hh : historyHalted (sourceDrawTerminalHistory stage entry draw truth) = true := by
    cases abandoned <;>
      simp [sourceDrawTerminalHistory, haction, historyHalted, historyActions, eventAction]
  exact congrArg (Prod.mk seed) (postwriteStageTrace_of_historyHalted source seed stage _ hh 3)

universe u
variable {Seed : Type u}

/-- A nonwriting source draw produces the same full stage exit immediately,
with stop and abandonment kept distinct. -/
theorem simulator_terminal_stageExit (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed) (world : (P.input fee hfee).World)
    (start : ℕ) (s : State P.sharedInstance) (stage : P.sharedInstance.Stage)
    (draw : SimulatorDraw P.sharedInstance) (abandoned virtualTruth : Bool)
    (hs0 : run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) start = s)
    (ha : s.halted = false) (hc : s.cursor = stage.val) (hw : s.ledger.written stage = none)
    (hdraw : simulatorSeedDraw P fee hfee source seed stage (simulatorShadow P fee hfee source seed s.history) = some draw)
    (haction : draw.action = if abandoned then .abandon else .stop) :
    ∃ finish : ℕ, start ≤ finish ∧
      (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
        (seed, world) finish).halted = true ∧
      (seed.1, simulatorShadow P fee hfee source seed
        (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
          (seed, world) finish).history) =
        sourceDrawStageExit source stage
          (((seed.1, simulatorShadow P fee hfee source seed s.history), draw), virtualTruth) := by
  have hs := simulator_terminal_record_shadow_packet P fee hfee C accounting source seed world start s stage draw
    abandoned virtualTruth hs0 ha hc hw hdraw haction
  refine ⟨start + 1, by omega, hs.1, ?_⟩
  rw [sourceDrawStageExit_terminal source seed.1 stage _ draw abandoned virtualTruth haction]
  exact congrArg (Prod.mk seed.1) hs.2

end PDROC
