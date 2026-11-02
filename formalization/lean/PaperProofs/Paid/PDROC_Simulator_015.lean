module

public import PaperProofs.Paid.PDROC_Simulator_014

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

theorem simulatorCandidate_prewrite (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage)
    (hh : historyHalted history = false) (hc : historyCursor history = stage.val)
    (hw : historyWritten history stage = none) :
    simulatorCandidate P fee hfee source seed history = simulatorDrawAction history stage (seed.2.2 stage)
      (simulatorSeedDraw P fee hfee source seed stage (simulatorShadow P fee hfee source seed history)) := by
  unfold simulatorCandidate simulatorCandidateAtCache
  exact simulatorCandidateFromData_prewrite history stage _ _ _ hh hc hw

/-- Every concrete unwritten record with no decision terminates immediately
on the actual protocol. Even a malformed source exit cannot generate an
extra physical review: the existing visible guard proves this pathwise. -/
theorem simulatorRule_prewrite_none_terminal (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage)
    (hh : historyHalted history = false) (hc : historyCursor history = stage.val)
    (hw : historyWritten history stage = none)
    (hnone : (simulatorDrawRecord (simulatorSeedDraw P fee hfee source seed stage
      (simulatorShadow P fee hfee source seed history))).decision = none) :
    simulatorRule P fee hfee source seed history = .stop ∨
      simulatorRule P fee hfee source seed history = .abandon := by
  have hraw := simulatorCandidate_prewrite P fee hfee source seed history stage hh hc hw
  cases hdraw : simulatorSeedDraw P fee hfee source seed stage (simulatorShadow P fee hfee source seed history) with
  | none =>
    have hab : simulatorCandidate P fee hfee source seed history = .abandon := by
      simpa only [hdraw, simulatorDrawAction] using hraw
    exact Or.inr (by simp only [simulatorRule, hab, historyAllowsAction, ↓reduceIte])
  | some draw =>
    have hd : draw.record.decision = none := by
      simpa only [hdraw, simulatorDrawRecord, Option.map_some, Option.getD_some] using hnone
    have hraw' : simulatorCandidate P fee hfee source seed history =
        reserialAction history (fun _ bit => bit) draw.action := by
      simpa only [hdraw, simulatorDrawAction, hd] using hraw
    by_cases hallow : historyAllowsAction history (reserialAction history (fun _ bit => bit) draw.action)
    · have hspec := simulatorSeedDraw_some_spec P fee hfee source seed stage _ draw hdraw
      have hwrite : optionWriteBit draw.action = none := hspec.1.symm.trans hd
      have hterminal := historyAllowsAction_unwritten_terminal history stage draw.action hc hw hspec.2 hwrite hallow
      rcases hterminal with hs | ha
      · exact Or.inl (by simp only [simulatorRule, hraw', hs, reserialAction, historyAllowsAction, ↓reduceIte])
      · exact Or.inr (by simp only [simulatorRule, hraw', ha, reserialAction, historyAllowsAction, ↓reduceIte])
    · exact Or.inr (by simp only [simulatorRule, hraw', hallow, ↓reduceIte])

end PDROC
