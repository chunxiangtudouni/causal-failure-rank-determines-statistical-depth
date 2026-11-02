module
public import Structure.PA17_L01HistoryPrefix_Strategy_002d
public import Structure.PA17_L01HistoryPrefix_History_003a

/-! The actual TABLE prefix supplies every completed-stage transition.
The current stage is excluded from stageUsed even after its commitment. -/
@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2400000
namespace PaperProofs.Common.Native.PA17L01HistoryPrefixStrategy002
open PaperProofs.Statistics PaperProofs.Structure
open PaperProofs.Structure.LaminarTree CompactPrice PSTRStatistics.TableAlignment
variable {I : Instance}

def StageOutcome (available : Finset I.Tool) (history : List (VisibleEvent I)) (stage : I.Stage) : Prop :=
  (CompactPrice.declaration history stage = .correct ∧
    stageUsed available history (stage.val + 1) = stageUsed available history stage.val) ∨
  ∃ tool, CompactPrice.declaration history stage = .error ∧
    (tableReply I available stage (toolsBefore history stage.val)).tool = some tool ∧
    stageUsed available history (stage.val + 1) = insert tool (stageUsed available history stage.val)

theorem stageOutcome_transport (available : Finset I.Tool)
    (before after : List (VisibleEvent I)) (stage : I.Stage)
    (hd : CompactPrice.declaration after stage = CompactPrice.declaration before stage)
    (hlo : toolsBefore after stage.val = toolsBefore before stage.val)
    (hhi : toolsBefore after (stage.val + 1) = toolsBefore before (stage.val + 1))
    (old : StageOutcome available before stage) : StageOutcome available after stage := by
  have ulo := congrArg (fun tools => (Finset.univ \ available) ∪ tools) hlo
  have uhi := congrArg (fun tools => (Finset.univ \ available) ∪ tools) hhi
  change stageUsed available after stage.val = stageUsed available before stage.val at ulo
  change stageUsed available after (stage.val + 1) = stageUsed available before (stage.val + 1) at uhi
  rcases old with ⟨decl, used⟩ | ⟨tool, decl, pick, used⟩
  · exact Or.inl ⟨hd.trans decl, uhi.trans (used.trans ulo.symm)⟩
  · exact Or.inr ⟨tool, hd.trans decl,
      (congrArg (fun tools => (tableReply I available stage tools).tool) hlo).trans pick,
      uhi.trans (used.trans (congrArg (insert tool) ulo.symm))⟩

theorem step_completed_outcome (input : StatisticalInput I) (C : Contract I)
    (current : C.IsCurrentAllocation) (mode : ResourceMode) (accounting : NormalAccounting I)
    (tapes : ReviewTapes input) {before after : State I} {action : Action I}
    (step : Step input C mode accounting tapes before action after)
    (available : Finset I.Tool) (stage : I.Stage) (hpast : stage.val < before.cursor)
    (old : StageOutcome available before.history stage) : StageOutcome available after.history stage := by
  apply stageOutcome_transport available before.history after.history stage
    (PA17L01HistoryPrefixHistory003.step_completed_declaration input C current.1 mode accounting tapes step stage hpast)
    (step_toolsBefore input C current.1 current.2 mode accounting tapes step stage.val (Nat.le_of_lt hpast))
    (step_toolsBefore input C current.1 current.2 mode accounting tapes step (stage.val + 1) (by omega)) old

theorem declaration_append_advance (history : List (VisibleEvent I)) (advanced stage : I.Stage) :
    CompactPrice.declaration (history ++ [.advanced advanced]) stage = CompactPrice.declaration history stage := by
  simp only [CompactPrice.declaration, historyWrite, historyReport, List.filterMap_append,
    List.filterMap_cons, List.filterMap_nil, eventWrite, eventReport, List.append_nil]

theorem outcome_append_advance (available : Finset I.Tool) (history : List (VisibleEvent I))
    (advanced stage : I.Stage) (old : StageOutcome available history stage) :
    StageOutcome available (history ++ [.advanced advanced]) stage := by
  have hc : historyCommitments (history ++ [.advanced advanced]) = historyCommitments history := by
    simp only [historyCommitments, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
      eventCommitment, List.append_nil]
  exact stageOutcome_transport available history _ stage (declaration_append_advance history advanced stage)
    (toolsBefore_congr hc _) (toolsBefore_congr hc _) old

theorem prefix_stage_outcomes (input : StatisticalInput I) (C : Contract I)
    (hl : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hb : 0 < budget) (hsmall : budget ≤ 1 / 2) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes n s) :
    ∀ stage : I.Stage, stage.val < s.cursor → StageOutcome available s.history stage := by
  induction hp with
  | initial => intro stage hs; change stage.val < 0 at hs; omega
  | @next n s next earlier step ih =>
    generalize haction : tableRule input available budget limit seed s.history = action at step
    intro stage hs
    by_cases hpast : stage.val < s.cursor
    · exact step_completed_outcome input C current .uncapped accounting tapes step available stage hpast (ih stage hpast)
    · cases step with
      | advance advanced live written resources =>
        change stage.val < s.cursor + 1 at hs
        have heq : stage = advanced := Fin.ext (by have hc := live.2; omega)
        subst stage
        change StageOutcome available (s.history ++ [.advanced advanced]) advanced
        apply outcome_append_advance
        exact advance_stage_transition input C hl current accounting available budget hb hsmall limit seed truth tapes
          earlier advanced live.1 live.2 haction
      | review | write | allocate | execute | stop | abandon =>
        change stage.val < s.cursor at hs
        exact (hpast hs).elim

end PaperProofs.Common.Native.PA17L01HistoryPrefixStrategy002
