module
public import Common.PSTR_ST_TableAlignment_003

/-! Tools consumed by completed stages of the actual visible history.
Current-stage commitments are deliberately excluded until the true advance.
No machine answer, successful-run or AllowedSequence premise is introduced. -/
@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PA17L01HistoryPrefixStrategy002
open PaperProofs.Statistics PaperProofs.Structure
open PaperProofs.Structure.LaminarTree CompactPrice

variable {I : Instance}

def toolsBefore (history : List (VisibleEvent I)) (stage : Nat) : Finset I.Tool :=
  (((historyCommitments history).filter (fun pair => decide (pair.1.stage.val < stage))).map Prod.snd).toFinset

def stageUsed (available : Finset I.Tool) (history : List (VisibleEvent I)) (stage : Nat) : Finset I.Tool :=
  (Finset.univ \ available) ∪ toolsBefore history stage

theorem stageUsed_zero (available : Finset I.Tool) (history : List (VisibleEvent I)) :
    stageUsed available history 0 = Finset.univ \ available := by
  simp [stageUsed, toolsBefore]

theorem mem_toolsBefore (history : List (VisibleEvent I)) (stage : Nat) (tool : I.Tool) :
    tool ∈ toolsBefore history stage ↔
      ∃ handle, (handle, tool) ∈ historyCommitments history ∧ handle.stage.val < stage := by
  simp only [toolsBefore, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨handle, value⟩, ⟨hm, hs⟩, he⟩
    cases he
    exact ⟨handle, hm, hs⟩
  · rintro ⟨handle, hm, hs⟩
    exact ⟨(handle, tool), ⟨hm, hs⟩, rfl⟩

theorem toolsBefore_eq_used (history : List (VisibleEvent I)) (stage : Nat)
    (hall : ∀ pair ∈ historyCommitments history, pair.1.stage.val < stage) :
    toolsBefore history stage = historyUsed history := by
  unfold toolsBefore historyUsed
  rw [List.filter_eq_self.mpr (by intro pair hp; exact decide_eq_true (hall pair hp))]

theorem toolsBefore_commit (history : List (VisibleEvent I)) (handle : MismatchHandle I)
    (tool : I.Tool) (stage : Nat) :
    toolsBefore (history ++ [.committed handle tool]) stage =
      if handle.stage.val < stage then insert tool (toolsBefore history stage) else toolsBefore history stage := by
  by_cases hs : handle.stage.val < stage <;>
    simp [toolsBefore, historyCommitments, List.filterMap_append, eventCommitment, hs]

theorem stageUsed_commit (available : Finset I.Tool) (history : List (VisibleEvent I))
    (handle : MismatchHandle I) (tool : I.Tool) (stage : Nat) :
    stageUsed available (history ++ [.committed handle tool]) stage =
      if handle.stage.val < stage then insert tool (stageUsed available history stage)
      else stageUsed available history stage := by
  rw [stageUsed, toolsBefore_commit]
  by_cases hs : handle.stage.val < stage <;> simp [hs, stageUsed]

theorem toolsBefore_congr {old fresh : List (VisibleEvent I)}
    (hc : historyCommitments fresh = historyCommitments old) (stage : Nat) :
    toolsBefore fresh stage = toolsBefore old stage := by
  unfold toolsBefore
  rw [hc]

theorem stageUsed_congr (available : Finset I.Tool) {old fresh : List (VisibleEvent I)}
    (hc : historyCommitments fresh = historyCommitments old) (stage : Nat) :
    stageUsed available fresh stage = stageUsed available old stage := by
  unfold stageUsed
  rw [toolsBefore_congr hc]

theorem prefix_commitment_stage_le {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hwindow : C.allocation = .currentWindow)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s) :
    ∀ a ∈ s.ledger.commitments, a.handle.stage.val ≤ s.cursor := by
  induction hp with
  | initial => simp [initial]
  | @next n s next earlier step ih =>
    generalize haction : rule seed s.history = action at step
    cases step with
    | review i live port resources => simpa only [record, reviewLedger] using ih
    | write i bit live port resources =>
      simpa only [record, reportedWriteLedger, hearly, ite_true, writeLedger] using ih
    | allocate handle tool active valid compatible unused unallocated window resources =>
      have hc := window hwindow
      intro a ha
      change a ∈ s.ledger.commitments ++ [⟨handle, tool, s.clock⟩] at ha
      rcases List.mem_append.mp ha with hold | hnew
      · exact ih a hold
      · have heq := List.mem_singleton.mp hnew
        subst a
        change handle.stage.val ≤ s.cursor
        omega
    | execute handle tool active valid compatible committed unused uncorrected window resources =>
      simpa only [record, executeLedger] using ih
    | advance i live written resources =>
      intro a ha
      exact (ih a ha).trans (by change s.cursor ≤ s.cursor + 1; omega)
    | stop active => simpa only [stopState] using ih
    | abandon active => simpa only [stopState] using ih

end PaperProofs.Common.Native.PA17L01HistoryPrefixStrategy002
