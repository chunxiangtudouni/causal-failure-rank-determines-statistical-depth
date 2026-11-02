module

public import PaperProofs.Paid.RootPaidToolRename009

@[expose] public section

namespace RootPaidToolRename

open MeasureTheory PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open scoped ENNReal

theorem state_reviews {I : Instance} (e : I.Tool ≃ I.Tool) (s : State I) (stage : I.Stage) :
    (state e s).ledger.reviews stage = s.ledger.reviews stage := rfl

theorem step (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    (e : (freshInstance n k).Tool ≃ (freshInstance n k).Tool)
    (tapes : ReviewTapes (P.freshInput n k fee hfee))
    {s next : State (freshInstance n k)} {a : Action (freshInstance n k)}
    (hs : Step (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) tapes s a next) :
    Step (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
      tapes (state e s) (action e a) (state e next) := by
  cases hs with
  | review stage live port _ =>
    simpa only [action, state_record, ledger_review, List.map_cons, List.map_nil, event,
      state_cursor, state_reviews] using
      (Step.review (input := P.freshInput n k fee hfee) (C := paidRelaxedContract _)
        (mode := .uncapped) (accounting := zeroAccounting _) (tapes := tapes)
        (state e s) stage live port (.inl rfl))
  | write stage bit live port _ =>
    simpa only [action, state_record, ledger_reportedWrite, writeResponses_map, state_cursor] using
      (Step.write (input := P.freshInput n k fee hfee) (C := paidRelaxedContract _)
        (mode := .uncapped) (accounting := zeroAccounting _) (tapes := tapes)
        (state e s) stage bit live port (.inl rfl))
  | allocate handle tool active valid _compatible unused unallocated window _ =>
    have hu : ∀ a ∈ (state e s).ledger.commitments, a.tool ≠ e tool := by
      intro a ha heq
      change a ∈ s.ledger.commitments.map (commitment e) at ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact unused b hb (e.injective heq)
    have hh : ∀ a ∈ (state e s).ledger.commitments, a.handle.stage ≠ handle.stage := by
      intro a ha heq
      change a ∈ s.ledger.commitments.map (commitment e) at ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact unallocated b hb heq
    have hm : e tool ∈ (freshInstance n k).eligible handle.stage := by
      simp [freshInstance, Instance.eligible]
      exact Finset.mem_univ _
    simpa only [action, state_record, ledger_allocate, List.map_cons, List.map_nil, event, state_cursor] using
      (Step.allocate (input := P.freshInput n k fee hfee) (C := paidRelaxedContract _)
        (mode := .uncapped) (accounting := zeroAccounting _) (tapes := tapes)
        (state e s) handle (e tool) active valid hm hu hh window (.inl rfl))
  | execute handle tool active valid _compatible committed unused uncorrected window _ =>
    have hc : ∃ a ∈ (state e s).ledger.commitments, a.handle = handle ∧ a.tool = e tool := by
      obtain ⟨a, ha, hh, ht⟩ := committed
      exact ⟨commitment e a, List.mem_map.mpr ⟨a, ha, rfl⟩, hh, congrArg e ht⟩
    have hu : ∀ a ∈ (state e s).ledger.executions, a.tool ≠ e tool := by
      intro a ha heq
      change a ∈ s.ledger.executions.map (execution e) at ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact unused b hb (e.injective heq)
    have hh : ∀ a ∈ (state e s).ledger.executions, a.handle.stage ≠ handle.stage := by
      intro a ha heq
      change a ∈ s.ledger.executions.map (execution e) at ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact uncorrected b hb heq
    have hm : e tool ∈ (freshInstance n k).eligible handle.stage := by
      simp [freshInstance, Instance.eligible]
      exact Finset.mem_univ _
    simpa only [action, state_record, ledger_execute, List.map_cons, List.map_nil, event, state_cursor] using
      (Step.execute (input := P.freshInput n k fee hfee) (C := paidRelaxedContract _)
        (mode := .uncapped) (accounting := zeroAccounting _) (tapes := tapes)
        (state e s) handle (e tool) active valid hm hc hu hh window (.inl rfl))
  | advance stage live written _ =>
    simpa only [action, state_record, ledger_advance, List.map_cons, List.map_nil, event, state_cursor] using
      (Step.advance (input := P.freshInput n k fee hfee) (C := paidRelaxedContract _)
        (mode := .uncapped) (accounting := zeroAccounting _) (tapes := tapes)
        (state e s) stage live written (.inl rfl))
  | stop active =>
    simpa only [action, state_stop] using
      (Step.stop (input := P.freshInput n k fee hfee) (C := paidRelaxedContract _)
        (mode := .uncapped) (accounting := zeroAccounting _) (tapes := tapes) (state e s) active)
  | abandon active =>
    simpa only [action, state_stop] using
      (Step.abandon (input := P.freshInput n k fee hfee) (C := paidRelaxedContract _)
        (mode := .uncapped) (accounting := zeroAccounting _) (tapes := tapes) (state e s) active)

theorem measurable_rawRule {I : Instance} {Seed : Type*} [MeasurableSpace Seed]
    (e : I.Tool ≃ I.Tool) (rule : PolicyRule I Seed) (hm : MeasurableRule rule) :
    MeasurableRule (rawRule e rule) := by
  apply measurable_from_prod_countable_left
  intro history
  have h : Measurable (fun seed : Seed => rule seed (history.map (event e.symm))) :=
    hm.comp (measurable_id.prodMk measurable_const)
  exact (measurable_of_countable (action e)).comp h

def policy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed]
    (e : (freshInstance n k).Tool ≃ (freshInstance n k).Tool) (available : Finset (freshInstance n k).Tool)
    (source : AvailablePolicy (P.freshInput n k fee hfee) (paidRelaxedContract _) (zeroAccounting _) available Seed) :
    AvailablePolicy (P.freshInput n k fee hfee) (paidRelaxedContract _) (zeroAccounting _) (available.image e) Seed :=
  ⟨{rule := PDMenu.paidGuardedRule (available.image e) (rawRule e source.val.rule)
    measurable_rule := PDMenu.measurable_paidGuardedRule _ _ (measurable_rawRule e source.val.rule source.val.measurable_rule)
    legal := PDMenu.paidGuardedRule_legal _ _ rfl _ _ _}, PDMenu.paidGuardedRule_usesOnly _ _ _ _ _⟩

theorem ledger_actualBill (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    (e : (freshInstance n k).Tool ≃ (freshInstance n k).Tool) (L : Ledger (freshInstance n k)) :
    (ledger e L).actualBill (P.freshInput n k fee hfee).fees = L.actualBill (P.freshInput n k fee hfee).fees := by
  unfold Ledger.actualBill Ledger.correctionBill
  simp only [ledger, List.map_map, StatisticalInput.fees, Parameters.freshInput]
  rfl

end RootPaidToolRename
