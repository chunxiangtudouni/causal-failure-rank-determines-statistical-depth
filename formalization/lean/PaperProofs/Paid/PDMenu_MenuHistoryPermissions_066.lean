module

public import PaperProofs.Paid.MenuCompiler
public import PaperProofs.Common.ReferenceControllerPreservation

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {I : Instance}

/-- A visible commitment on a real prefix has its original genuine handle. -/
theorem menuCommittedHandle_valid (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {clock : ℕ} {state : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes clock state)
    (pair : MismatchHandle I × I.Tool) (hpair : pair ∈ historyCommitments state.history) :
    historyValidHandle state.history pair.1 := by
  rw [prefix_historyCommitments input C mode accounting rule seed truth tapes hp] at hpair
  obtain ⟨a, ha, heq⟩ := List.mem_map.mp hpair
  have hinv := prefix_invariant input C mode accounting rule seed truth tapes hp
  have hg := hinv.commitment_genuine a ha
  obtain ⟨time, ht, _⟩ := hinv.wellFormed.reported a ha
  have hv : validHandle state a.handle := ⟨hg.1, hg.2, time, ht⟩
  have hh : a.handle = pair.1 := congrArg Prod.fst heq
  exact hh ▸ prefix_historyValidHandle_of_valid input C hearly mode accounting rule seed truth tapes hp a.handle hv

/-- An executed tool has the stage of its unique real prior commitment.
This uses both genuine backing and the original no-reuse invariant. -/
theorem menuExecutedTool_stage (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {clock : ℕ} {state : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes clock state)
    (committed executed : MismatchHandle I × I.Tool)
    (hc : committed ∈ historyCommitments state.history)
    (he : executed ∈ historyExecutions state.history) (htool : executed.2 = committed.2) :
    executed.1.stage = committed.1.stage := by
  rw [prefix_historyCommitments input C mode accounting rule seed truth tapes hp] at hc
  rw [prefix_historyExecutions input C mode accounting rule seed truth tapes hp] at he
  obtain ⟨a, ha, hac⟩ := List.mem_map.mp hc
  obtain ⟨e, he, hee⟩ := List.mem_map.mp he
  have hwf := prefix_ledgerWellFormed input C mode accounting rule seed truth tapes hp
  obtain ⟨b, hb, hhandle, hbtool, _⟩ := hwf.backed e he
  have hba : b.tool = a.tool := hbtool.trans ((congrArg Prod.snd hee).trans (htool.trans (congrArg Prod.snd hac).symm))
  have hbeq : b = a := List.inj_on_of_nodup_map hwf.commitment_tools hb ha hba
  subst b
  exact (congrArg (fun pair : MismatchHandle I × I.Tool => pair.1.stage) hee).symm.trans
    ((congrArg MismatchHandle.stage hhandle).symm.trans (congrArg (fun pair : MismatchHandle I × I.Tool => pair.1.stage) hac))

/-- The visible old-serial handle is valid precisely from the actual
write/report mismatch packet checked by the menu script. -/
theorem menuVisibleHandle_valid (history : List (VisibleEvent I)) (stage : I.Stage)
    (bit truth : Bool) (serial reportedSerial : ℕ)
    (hw : historyWrite history stage = some (bit, serial))
    (hr : historyReport history stage = some (truth, reportedSerial))
    (hs : serial = reportedSerial) (hb : bit ≠ truth)
    (handle : MismatchHandle I) (hh : referenceVisibleHandle history stage = some handle) :
    handle.stage = stage ∧ historyValidHandle history handle := by
  have hh' : (⟨stage, serial⟩ : MismatchHandle I) = handle := by
    simpa only [referenceVisibleHandle, hw, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] using hh
  subst handle
  have hb' : bit = !truth := by cases bit <;> cases truth <;> simp_all
  refine ⟨rfl, ?_⟩
  simp only [historyValidHandle, hr, historyWritten, historyWriteSerial, hw,
    Option.map_some, Option.getD_some, hb', hs, and_self]

end PDMenu
