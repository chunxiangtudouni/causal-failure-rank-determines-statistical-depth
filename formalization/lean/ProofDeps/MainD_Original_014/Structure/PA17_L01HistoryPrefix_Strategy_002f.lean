module
public import Structure.PA17_L01HistoryPrefix_Strategy_002e
public import Structure.PA17_L01HistoryPrefix_Commands_001b

/-! Actual TABLE histories satisfy the original compact-command qualifications.
The only history argument is a native uncapped TABLE Prefix. -/
@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2400000
namespace PaperProofs.Common.Native.PA17L01HistoryPrefixStrategy002
open PaperProofs.Statistics PaperProofs.Structure
open PaperProofs.Structure.LaminarTree CompactPrice CompactControllerClaims
open PaperProofs.Structure.LaminarTree.PA17L01HistoryPrefixCommands001
variable {I : Instance}

theorem prefix_stageTransitions (input : StatisticalInput I) (C : Contract I)
    (hl : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hb : 0 < budget) (hsmall : budget ≤ 1 / 2) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes n s) :
    StageTransitions I.compatibility (declarationAt s.history) (stageUsed available s.history)
      (min (historyCursor s.history) I.stageCount) := by
  intro stage hs
  have hc := prefix_historyCursor input C .uncapped accounting
    (tableRule input available budget limit) seed truth tapes hp
  have hpast : stage.val < s.cursor := by
    rw [← hc]
    exact hs.trans_le (Nat.min_le_left _ _)
  have outcome := prefix_stage_outcomes input C hl current accounting available budget hb hsmall limit seed truth tapes hp stage hpast
  unfold StageTransition
  rw [declarationAt_lt s.history stage.val stage.isLt]
  exact outcome

theorem prefix_commandsAt_data (input : StatisticalInput I) (C : Contract I)
    (hl : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hb : 0 < budget) (hsmall : budget ≤ 1 / 2) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes n s) :
    PSTRCommandPrefixes.AllowedSequence I.compatibility ⟨0, Finset.univ \ available, false⟩
        (CompactPrice.commandsAt I s.history) ∧
      (CompactPrice.commandsAt I s.history).foldl (nextConfiguration I.toolCount I.compatibility)
        ⟨0, Finset.univ \ available, false⟩ = ⟨s.cursor, stageUsed available s.history s.cursor, false⟩ := by
  have transitions := prefix_stageTransitions input C hl current accounting available budget hb hsmall limit seed truth tapes hp
  have data := commandsAt_stage_data s.history (stageUsed available s.history) transitions
  have hc := prefix_historyCursor input C .uncapped accounting
    (tableRule input available budget limit) seed truth tapes hp
  have hbound := (prefix_cursorInvariant input C .uncapped accounting
    (tableRule input available budget limit) seed truth tapes hp).bound
  have hcount : min (historyCursor s.history) I.stageCount = s.cursor := by rw [hc]; exact Nat.min_eq_left hbound
  have hzero : stageConfiguration (stageUsed available s.history) 0 =
      (⟨0, Finset.univ \ available, false⟩ : Configuration I.toolCount) := by
    unfold stageConfiguration
    rw [stageUsed_zero]
  refine ⟨?_, ?_⟩
  · exact hzero ▸ data.2.1
  · have folded := data.2.2
    rw [hzero, hcount] at folded
    exact folded

theorem prefix_commandsAt_allowed (input : StatisticalInput I) (C : Contract I)
    (hl : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hb : 0 < budget) (hsmall : budget ≤ 1 / 2) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes n s) :
    PSTRCommandPrefixes.AllowedSequence I.compatibility ⟨0, Finset.univ \ available, false⟩
      (CompactPrice.commandsAt I s.history) :=
  (prefix_commandsAt_data input C hl current accounting available budget hb hsmall limit seed truth tapes hp).1

end PaperProofs.Common.Native.PA17L01HistoryPrefixStrategy002
