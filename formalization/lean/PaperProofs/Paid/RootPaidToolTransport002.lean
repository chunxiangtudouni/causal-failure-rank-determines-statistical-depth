module

public import PaperProofs.Paid.RootPaidToolTransport001
public import PaperProofs.Paid.PDMenu_CurrentHeadKernel_006

@[expose] public section

namespace RootPaidToolTransport

open MeasureTheory PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem upStage_injective (n k : ℕ) : Function.Injective (upStage n k) :=
  (stages n k).injective

theorem downStage_injective (n k : ℕ) : Function.Injective (downStage n k) :=
  (stages n k).symm.injective

theorem upTool_injective (k : ℕ) : Function.Injective (upTool k) := by
  intro a b h
  exact Fin.ext (congrArg (fun tool : Fin (k + 1) => tool.val) h)

theorem update_comp_downStage {α : Type*} (n k : ℕ)
    (f : (freshInstance n k).Stage → α) (stage : (freshInstance n k).Stage) (value : α) :
    Function.update f stage value ∘ downStage n k =
      Function.update (f ∘ downStage n k) (upStage n k stage) value :=
  Function.update_comp_eq_of_injective f (downStage_injective n k) (upStage n k stage) value

theorem upState_initial (n k : ℕ) (truth : (freshInstance n k).Stage → Bool) :
    upState n k (initial truth) = initial (truth ∘ downStage n k) := rfl

theorem upState_cursor (n k : ℕ) (s : State (freshInstance n k)) :
    (upState n k s).cursor = s.cursor := rfl

theorem upState_reviews (n k : ℕ) (s : State (freshInstance n k)) (stage : (freshInstance n k).Stage) :
    (upState n k s).ledger.reviews (upStage n k stage) = s.ledger.reviews stage := rfl

theorem upState_record (n k : ℕ) (s : State (freshInstance n k))
    (action : Action (freshInstance n k)) (responses : List (VisibleEvent (freshInstance n k)))
    (L : Ledger (freshInstance n k)) (cursor : ℕ) (halted : Bool) :
    upState n k (record (zeroAccounting _) s action responses L cursor halted) =
      record (zeroAccounting _) (upState n k s) (upAction n k action)
        (upHistory n k responses) (upLedger n k L) cursor halted := by
  simp only [upState, record, upLedger, upHistory, zeroAccounting, List.map_append]

theorem upLedger_review (n k : ℕ) (s : State (freshInstance n k)) (stage : (freshInstance n k).Stage) :
    upLedger n k (reviewLedger s stage) = reviewLedger (upState n k s) (upStage n k stage) := by
  simp only [upLedger, reviewLedger, upState, update_comp_downStage, Function.comp_apply, down_up_stage]

theorem upLedger_write (n k : ℕ) (s : State (freshInstance n k))
    (stage : (freshInstance n k).Stage) (bit : Bool) :
    upLedger n k (writeLedger s stage bit) = writeLedger (upState n k s) (upStage n k stage) bit := by
  simp only [upLedger, writeLedger, upState, update_comp_downStage]

theorem upLedger_reportedWrite (n k : ℕ) (s : State (freshInstance n k))
    (stage : (freshInstance n k).Stage) (bit : Bool) :
    upLedger n k (reportedWriteLedger (paidRelaxedContract _) s stage bit) =
      reportedWriteLedger (paidRelaxedContract _) (upState n k s) (upStage n k stage) bit := by
  simp only [reportedWriteLedger, paidRelaxedContract, ite_true]
  simp only [upLedger, writeLedger, upState, update_comp_downStage]

theorem upHistory_writeResponses (n k : ℕ) (s : State (freshInstance n k))
    (stage : (freshInstance n k).Stage) (bit : Bool) :
    upHistory n k (writeResponses (paidRelaxedContract _) s stage bit) =
      writeResponses (paidRelaxedContract _) (upState n k s) (upStage n k stage) bit := rfl

theorem upLedger_allocate (n k : ℕ) (s : State (freshInstance n k))
    (handle : MismatchHandle (freshInstance n k)) (tool : (freshInstance n k).Tool) :
    upLedger n k (allocateLedger s handle tool) =
      allocateLedger (upState n k s) (upHandle n k handle) (upTool k tool) := by
  simp only [upLedger, allocateLedger, upState, List.map_append, List.map_cons, List.map_nil, upCommitment]

theorem upLedger_execute (n k : ℕ) (s : State (freshInstance n k))
    (handle : MismatchHandle (freshInstance n k)) (tool : (freshInstance n k).Tool) :
    upLedger n k (executeLedger s handle tool) =
      executeLedger (upState n k s) (upHandle n k handle) (upTool k tool) := by
  simp only [upLedger, executeLedger, upState, List.map_append, List.map_cons, List.map_nil, upExecution]

theorem upLedger_advance (n k : ℕ) (s : State (freshInstance n k)) (stage : (freshInstance n k).Stage) :
    upLedger n k (advanceLedger s stage) = advanceLedger (upState n k s) (upStage n k stage) := by
  simp only [upLedger, advanceLedger, upState, update_comp_downStage]

theorem allWritten_upLedger (n k : ℕ) (L : Ledger (freshInstance n k)) :
    allWritten (upLedger n k L) ↔ allWritten L := by
  constructor
  · intro h stage
    exact h (upStage n k stage)
  · intro h stage
    exact h (downStage n k stage)

theorem upState_stopState (n k : ℕ) (s : State (freshInstance n k)) (abandon : Bool) :
    upState n k (stopState s abandon) = stopState (upState n k s) abandon := by
  classical
  have hd : decide (allWritten (upState n k s).ledger) = decide (allWritten s.ledger) := by
    change decide (allWritten (upLedger n k s.ledger)) = _
    simp only [allWritten_upLedger]
  simp only [stopState]
  rw [hd]
  cases abandon <;> simp [upState, upLedger, upHistory, upEvent, List.map_append]

def upTapes (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    (tapes : ReviewTapes (P.freshInput n k fee hfee)) :
    ReviewTapes (P.freshInput n (k + 1) fee hfee) :=
  fun stage => tapes (downStage n k stage)

theorem upTapes_upStage (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    (tapes : ReviewTapes (P.freshInput n k fee hfee)) (stage : (freshInstance n k).Stage) :
    upTapes P fee hfee n k tapes (upStage n k stage) = tapes stage := rfl

theorem upStep (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    (tapes : ReviewTapes (P.freshInput n k fee hfee))
    {s next : State (freshInstance n k)} {action : Action (freshInstance n k)}
    (hs : Step (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped
      (zeroAccounting _) tapes s action next) :
    Step (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) .uncapped
      (zeroAccounting _) (upTapes P fee hfee n k tapes)
      (upState n k s) (upAction n k action) (upState n k next) := by
  cases hs with
  | review stage live port _ =>
    simpa only [upAction, upState_record, upLedger_review, upHistory, List.map_cons,
      List.map_nil, upEvent, upState_cursor, upState_reviews, upTapes_upStage] using
      (Step.review (input := P.freshInput n (k + 1) fee hfee) (C := paidRelaxedContract _)
        (mode := .uncapped) (accounting := zeroAccounting _) (tapes := upTapes P fee hfee n k tapes)
        (upState n k s) (upStage n k stage) live port (.inl rfl))
  | write stage bit live port _ =>
    simpa only [upAction, upState_record, upLedger_reportedWrite, upHistory_writeResponses, upState_cursor] using
      (Step.write (input := P.freshInput n (k + 1) fee hfee) (C := paidRelaxedContract _)
        (mode := .uncapped) (accounting := zeroAccounting _) (tapes := upTapes P fee hfee n k tapes)
        (upState n k s) (upStage n k stage) bit live port (.inl rfl))
  | allocate handle tool active valid _compatible unused unallocated window _ =>
    have hu : ∀ a ∈ (upState n k s).ledger.commitments, a.tool ≠ upTool k tool := by
      intro a ha heq
      change a ∈ s.ledger.commitments.map (upCommitment n k) at ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact unused b hb (upTool_injective k heq)
    have hh : ∀ a ∈ (upState n k s).ledger.commitments,
        a.handle.stage ≠ (upHandle n k handle).stage := by
      intro a ha heq
      change a ∈ s.ledger.commitments.map (upCommitment n k) at ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact unallocated b hb (upStage_injective n k heq)
    have hc : upTool k tool ∈ (freshInstance n (k + 1)).eligible (upHandle n k handle).stage := by
      simp [freshInstance, Instance.eligible]
      exact Finset.mem_univ _
    simpa only [upAction, upState_record, upLedger_allocate, upHistory, List.map_cons,
      List.map_nil, upEvent, upState_cursor] using
      (Step.allocate (input := P.freshInput n (k + 1) fee hfee) (C := paidRelaxedContract _)
        (mode := .uncapped) (accounting := zeroAccounting _) (tapes := upTapes P fee hfee n k tapes)
        (upState n k s) (upHandle n k handle) (upTool k tool) active valid hc hu hh window (.inl rfl))
  | execute handle tool active valid _compatible committed unused uncorrected window _ =>
    have hc : ∃ a ∈ (upState n k s).ledger.commitments,
        a.handle = upHandle n k handle ∧ a.tool = upTool k tool := by
      obtain ⟨a, ha, hh, ht⟩ := committed
      exact ⟨upCommitment n k a, List.mem_map.mpr ⟨a, ha, rfl⟩,
        congrArg (upHandle n k) hh, congrArg (upTool k) ht⟩
    have hu : ∀ e ∈ (upState n k s).ledger.executions, e.tool ≠ upTool k tool := by
      intro e he heq
      change e ∈ s.ledger.executions.map (upExecution n k) at he
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
      exact unused b hb (upTool_injective k heq)
    have hh : ∀ e ∈ (upState n k s).ledger.executions,
        e.handle.stage ≠ (upHandle n k handle).stage := by
      intro e he heq
      change e ∈ s.ledger.executions.map (upExecution n k) at he
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
      exact uncorrected b hb (upStage_injective n k heq)
    have hm : upTool k tool ∈ (freshInstance n (k + 1)).eligible (upHandle n k handle).stage := by
      simp [freshInstance, Instance.eligible]
      exact Finset.mem_univ _
    simpa only [upAction, upState_record, upLedger_execute, upHistory, List.map_cons,
      List.map_nil, upEvent, upState_cursor] using
      (Step.execute (input := P.freshInput n (k + 1) fee hfee) (C := paidRelaxedContract _)
        (mode := .uncapped) (accounting := zeroAccounting _) (tapes := upTapes P fee hfee n k tapes)
        (upState n k s) (upHandle n k handle) (upTool k tool) active valid hm hc hu hh window (.inl rfl))
  | advance stage live written _ =>
    simpa only [upAction, upState_record, upLedger_advance, upHistory, List.map_cons,
      List.map_nil, upEvent, upState_cursor] using
      (Step.advance (input := P.freshInput n (k + 1) fee hfee) (C := paidRelaxedContract _)
        (mode := .uncapped) (accounting := zeroAccounting _) (tapes := upTapes P fee hfee n k tapes)
        (upState n k s) (upStage n k stage) live written (.inl rfl))
  | stop active =>
    simpa only [upAction, upState_stopState] using
      (Step.stop (input := P.freshInput n (k + 1) fee hfee) (C := paidRelaxedContract _)
        (mode := .uncapped) (accounting := zeroAccounting _) (tapes := upTapes P fee hfee n k tapes)
        (upState n k s) active)
  | abandon active =>
    simpa only [upAction, upState_stopState] using
      (Step.abandon (input := P.freshInput n (k + 1) fee hfee) (C := paidRelaxedContract _)
        (mode := .uncapped) (accounting := zeroAccounting _) (tapes := upTapes P fee hfee n k tapes)
        (upState n k s) active)

end RootPaidToolTransport
