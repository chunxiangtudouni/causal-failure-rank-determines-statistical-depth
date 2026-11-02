module

public import PaperProofs.Paid.RootPaidToolTransport008

@[expose] public section

namespace RootPaidToolRename

open MeasureTheory PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {I : Instance}

def action (e : I.Tool ≃ I.Tool) : Action I → Action I
  | .review stage => .review stage
  | .write stage bit => .write stage bit
  | .allocate handle tool => .allocate handle (e tool)
  | .execute handle tool => .execute handle (e tool)
  | .advance stage => .advance stage
  | .stop => .stop
  | .abandon => .abandon

def event (e : I.Tool ≃ I.Tool) : VisibleEvent I → VisibleEvent I
  | .observation stage symbol => .observation stage symbol
  | .wrote stage bit serial => .wrote stage bit serial
  | .report stage truth serial => .report stage truth serial
  | .committed handle tool => .committed handle (e tool)
  | .executed handle tool => .executed handle (e tool)
  | .advanced stage => .advanced stage
  | .stopped => .stopped
  | .abandoned => .abandoned

theorem symm_event (e : I.Tool ≃ I.Tool) (value : VisibleEvent I) :
    event e.symm (event e value) = value := by
  cases value with
  | observation _ _ => rfl
  | wrote _ _ _ => rfl
  | report _ _ _ => rfl
  | committed handle tool => exact congrArg (VisibleEvent.committed handle) (e.symm_apply_apply tool)
  | executed handle tool => exact congrArg (VisibleEvent.executed handle) (e.symm_apply_apply tool)
  | advanced _ => rfl
  | stopped => rfl
  | abandoned => rfl

theorem symm_history (e : I.Tool ≃ I.Tool) (history : List (VisibleEvent I)) :
    (history.map (event e)).map (event e.symm) = history := by
  induction history with
  | nil => rfl
  | cons head rest ih => simp only [List.map_cons, symm_event, ih]

def commitment (e : I.Tool ≃ I.Tool) (a : Commitment I) : Commitment I := {a with tool := e a.tool}
def execution (e : I.Tool ≃ I.Tool) (a : Execution I) : Execution I := {a with tool := e a.tool}
def ledger (e : I.Tool ≃ I.Tool) (L : Ledger I) : Ledger I :=
  { L with commitments := L.commitments.map (commitment e), executions := L.executions.map (execution e) }
def state (e : I.Tool ≃ I.Tool) (s : State I) : State I :=
  { s with ledger := ledger e s.ledger, history := s.history.map (event e) }

def rawRule {Seed : Type*} (e : I.Tool ≃ I.Tool) (rule : PolicyRule I Seed) : PolicyRule I Seed :=
  fun seed history => action e (rule seed (history.map (event e.symm)))

theorem rawRule_on_history {Seed : Type*} (e : I.Tool ≃ I.Tool) (rule : PolicyRule I Seed)
    (seed : Seed) (history : List (VisibleEvent I)) :
    rawRule e rule seed (history.map (event e)) = action e (rule seed history) := by
  simp only [rawRule, symm_history]

theorem state_initial (e : I.Tool ≃ I.Tool) (truth : I.Stage → Bool) :
    state e (initial truth) = initial truth := rfl

theorem state_cursor (e : I.Tool ≃ I.Tool) (s : State I) : (state e s).cursor = s.cursor := rfl

theorem state_record (e : I.Tool ≃ I.Tool) (s : State I) (a : Action I)
    (responses : List (VisibleEvent I)) (L : Ledger I) (cursor : ℕ) (halted : Bool) :
    state e (record (zeroAccounting I) s a responses L cursor halted) =
      record (zeroAccounting I) (state e s) (action e a) (responses.map (event e)) (ledger e L) cursor halted := by
  simp only [state, ledger, record, zeroAccounting, List.map_append]

theorem ledger_review (e : I.Tool ≃ I.Tool) (s : State I) (stage : I.Stage) :
    ledger e (reviewLedger s stage) = reviewLedger (state e s) stage := rfl

theorem ledger_reportedWrite (e : I.Tool ≃ I.Tool) (s : State I) (stage : I.Stage) (bit : Bool) :
    ledger e (reportedWriteLedger (paidRelaxedContract I) s stage bit) =
      reportedWriteLedger (paidRelaxedContract I) (state e s) stage bit := by
  simp only [reportedWriteLedger, paidRelaxedContract, ite_true]
  rfl

theorem writeResponses_map (e : I.Tool ≃ I.Tool) (s : State I) (stage : I.Stage) (bit : Bool) :
    (writeResponses (paidRelaxedContract I) s stage bit).map (event e) =
      writeResponses (paidRelaxedContract I) (state e s) stage bit := rfl

theorem ledger_allocate (e : I.Tool ≃ I.Tool) (s : State I) (handle : MismatchHandle I) (tool : I.Tool) :
    ledger e (allocateLedger s handle tool) = allocateLedger (state e s) handle (e tool) := by
  simp only [ledger, allocateLedger, state, List.map_append, List.map_cons, List.map_nil, commitment]

theorem ledger_execute (e : I.Tool ≃ I.Tool) (s : State I) (handle : MismatchHandle I) (tool : I.Tool) :
    ledger e (executeLedger s handle tool) = executeLedger (state e s) handle (e tool) := by
  simp only [ledger, executeLedger, state, List.map_append, List.map_cons, List.map_nil, execution]

theorem ledger_advance (e : I.Tool ≃ I.Tool) (s : State I) (stage : I.Stage) :
    ledger e (advanceLedger s stage) = advanceLedger (state e s) stage := rfl

theorem state_stop (e : I.Tool ≃ I.Tool) (s : State I) (abandon : Bool) :
    state e (stopState s abandon) = stopState (state e s) abandon := by
  cases abandon <;> simp [state, ledger, stopState, allWritten, event, List.map_append]
  all_goals exact decide_eq_decide.mpr Iff.rfl

theorem ledger_success (e : I.Tool ≃ I.Tool) (L : Ledger I) (h : L.success (paidRelaxedContract I)) :
    (ledger e L).success (paidRelaxedContract I) := by
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · intro stage time ht hw
    obtain ⟨ha, he⟩ := h.2.2.1 stage time ht hw
    constructor
    · intro hc
      obtain ⟨a, hamem, hastage, hatime⟩ := ha hc
      exact ⟨commitment e a, List.mem_map.mpr ⟨a, hamem, rfl⟩, hastage, hatime⟩
    · intro hc
      obtain ⟨a, hamem, hastage, hatime⟩ := he hc
      exact ⟨execution e a, List.mem_map.mpr ⟨a, hamem, rfl⟩, hastage, hatime⟩
  · intro stage
    rcases h.2.2.2 stage with hw | ⟨a, ha, hstage⟩
    · exact Or.inl hw
    · exact Or.inr ⟨execution e a, List.mem_map.mpr ⟨a, ha, rfl⟩, hstage⟩

end RootPaidToolRename
