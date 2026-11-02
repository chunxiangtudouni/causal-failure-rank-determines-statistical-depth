module

public import PaperProofs.Paid.PDROC_CoordinateCoupling_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

/-- The simulator's action transport changes only the ordinary decision and
real handle serial. It neither grants tools nor changes any stage/tool. -/
def reserialAction (actual : List (VisibleEvent I)) (writeBit : I.Stage → Bool → Bool) : Action I → Action I
  | .write stage bit => .write stage (writeBit stage bit)
  | .allocate handle tool => .allocate (reserialHandle actual handle) tool
  | .execute handle tool => .execute (reserialHandle actual handle) tool
  | action => action

theorem historyUsed_eq_of_reserialCommitments (actual virtual : List (VisibleEvent I))
    (hcommit : historyCommitments actual = (historyCommitments virtual).map
      (fun pair => (reserialHandle actual pair.1, pair.2))) : historyUsed actual = historyUsed virtual := by
  simp only [historyUsed, hcommit, List.map_map]
  rfl

theorem historyAllowsAction_reserial_transport
    (actual virtual : List (VisibleEvent I)) (writeBit : I.Stage → Bool → Bool) (action : Action I)
    (hcursor : historyCursor actual = historyCursor virtual)
    (hnone : ∀ stage : I.Stage, historyWritten actual stage = none ↔ historyWritten virtual stage = none)
    (hvalid : ∀ handle : MismatchHandle I, historyValidHandle virtual handle →
      historyValidHandle actual (reserialHandle actual handle))
    (hcommit : historyCommitments actual = (historyCommitments virtual).map
      (fun pair => (reserialHandle actual pair.1, pair.2)))
    (hexecution : historyExecutions actual = (historyExecutions virtual).map
      (fun pair => (reserialHandle actual pair.1, pair.2)))
    (hallow : historyAllowsAction virtual action) :
    historyAllowsAction actual (reserialAction actual writeBit action) := by
  have hused := historyUsed_eq_of_reserialCommitments actual virtual hcommit
  cases action with
  | review stage => exact ⟨hcursor.trans hallow.1, (hnone stage).mpr hallow.2⟩
  | write stage bit => exact ⟨hcursor.trans hallow.1, (hnone stage).mpr hallow.2⟩
  | advance stage => exact ⟨hcursor.trans hallow.1, fun hn => hallow.2 ((hnone stage).mp hn)⟩
  | allocate handle tool =>
    rcases hallow with ⟨hc, hv, hcompatible, hfresh, hunallocated⟩
    refine ⟨hcursor.trans hc, hvalid handle hv, hcompatible, ?_, ?_⟩
    · simpa only [hused] using hfresh
    · intro pair hp
      rw [hcommit] at hp
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hp
      exact hunallocated original ho
  | execute handle tool =>
    rcases hallow with ⟨hc, hv, hcompatible, hcommitted, hfresh, huncorrected⟩
    refine ⟨hcursor.trans hc, hvalid handle hv, hcompatible, ?_, ?_, ?_⟩
    · rw [hcommit]
      exact List.mem_map.mpr ⟨(handle, tool), hcommitted, rfl⟩
    · intro pair hp
      rw [hexecution] at hp
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hp
      exact hfresh original ho
    · intro pair hp
      rw [hexecution] at hp
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hp
      exact huncorrected original ho
  | stop => trivial
  | abandon => trivial



/-- The transported visible permission produces an ORIGINAL actual Native
Step at every reachable active early-report prefix, including execution. -/
theorem reserialAction_step_exists (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) {Seed : Type*}
    (source : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C .uncapped accounting source seed truth tapes n s)
    (ha : s.halted = false) (virtual : List (VisibleEvent I))
    (writeBit : I.Stage → Bool → Bool) (action : Action I)
    (hcursor : historyCursor s.history = historyCursor virtual)
    (hnone : ∀ stage : I.Stage, historyWritten s.history stage = none ↔ historyWritten virtual stage = none)
    (hvalid : ∀ handle : MismatchHandle I, historyValidHandle virtual handle →
      historyValidHandle s.history (reserialHandle s.history handle))
    (hcommit : historyCommitments s.history = (historyCommitments virtual).map
      (fun pair => (reserialHandle s.history pair.1, pair.2)))
    (hexecution : historyExecutions s.history = (historyExecutions virtual).map
      (fun pair => (reserialHandle s.history pair.1, pair.2)))
    (hallow : historyAllowsAction virtual action) :
    ∃ next : State I, Step input C .uncapped accounting tapes s
      (reserialAction s.history writeBit action) next :=
  historyAllowsAction_sound input C hearly accounting source seed truth tapes hp ha _
    (historyAllowsAction_reserial_transport s.history virtual writeBit action hcursor hnone hvalid hcommit hexecution hallow)

end PDROC
