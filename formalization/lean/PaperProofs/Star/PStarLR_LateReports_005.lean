module

public import PaperProofs.Star.PStarLR_PrefixFrame_003
public import PaperProofs.Retained.NativeMatching
public import PaperProofs.Retained.PRet_EarlyReports_034

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PStarLR

variable {I : Instance}

theorem historyReport_append_reportAll (history : List (VisibleEvent I)) (L : Ledger I) (stage : I.Stage) :
    historyReport (history ++ reportAll L) stage = some (L.truth stage, L.writeSerial stage) := by
  classical
  let reports := (reportAll L).filterMap (eventReport stage)
  have hmem : (L.truth stage, L.writeSerial stage) ∈ reports := by
    apply List.mem_filterMap.mpr
    exact ⟨.report stage (L.truth stage) (L.writeSerial stage),
      List.mem_ofFn.mpr ⟨stage, rfl⟩, by simp [eventReport]⟩
  have hne : reports ≠ [] := by
    intro hempty
    simp only [hempty, List.not_mem_nil] at hmem
  have unique : ∀ pair ∈ reports, pair = (L.truth stage, L.writeSerial stage) := by
    intro pair hpair
    obtain ⟨event, hevent, heq⟩ := List.mem_filterMap.mp hpair
    obtain ⟨other, rfl⟩ := List.mem_ofFn.mp hevent
    simp only [eventReport] at heq
    split_ifs at heq with hstage
    · subst other
      exact Option.some.inj heq.symm
  unfold historyReport
  rw [List.filterMap_append, List.getLast?_append_of_ne_nil _ hne,
    List.getLast?_eq_some_getLast hne, unique _ (List.getLast_mem hne)]

theorem prefix_historyReport_all_contracts (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {state : State I} (path : Prefix input C mode accounting policy seed truth tapes n state) :
    ∀ stage : I.Stage, historyReport state.history stage =
      (state.ledger.reportTime stage).map (fun _ => (state.ledger.truth stage, state.ledger.writeSerial stage)) := by
  classical
  by_cases hearly : C.reporting = .early
  · exact prefix_historyReport_early input C hearly mode accounting policy seed truth tapes path
  have hlate : C.reporting = .late := by cases h : C.reporting <;> simp_all
  induction path with
  | initial => intro stage; rfl
  | @next n state next earlier step ih =>
    generalize haction : policy seed state.history = action at step
    cases step with
    | write current bit live port resources =>
      intro stage
      by_cases hall : allWritten (writeLedger state current bit)
      · change historyReport (state.history ++ writeResponses C state current bit) stage = _
        simp only [writeResponses, hearly, ↓reduceIte, hall]
        rw [← List.append_assoc, historyReport_append_reportAll]
        simp only [record, reportedWriteLedger, hearly, ↓reduceIte, hall, Option.map_some]
      · have hbefore : ¬ allWritten state.ledger := by
          intro complete
          exact complete current port
        have hnone := (prefix_invariant input C mode accounting policy seed truth tapes earlier).late_report_gate
          hlate hbefore
        have hresponses : writeResponses C state current bit = [.wrote current bit state.clock] := by
          simp only [writeResponses, hearly, ↓reduceIte, hall, List.append_nil]
        have hledger : reportedWriteLedger C state current bit = writeLedger state current bit := by
          simp only [reportedWriteLedger, hearly, ↓reduceIte, hall]
        change historyReport (state.history ++ writeResponses C state current bit) stage =
          ((reportedWriteLedger C state current bit).reportTime stage).map
            (fun _ => ((reportedWriteLedger C state current bit).truth stage,
              (reportedWriteLedger C state current bit).writeSerial stage))
        rw [hresponses, hledger]
        have hleft : historyReport (state.history ++ [.wrote current bit state.clock]) stage =
            historyReport state.history stage := by
          simp only [historyReport, List.filterMap_append, List.filterMap_cons,
            List.filterMap_nil, eventReport, List.append_nil]
        rw [hleft, ih stage, hnone stage]
        simp only [Option.map_none, writeLedger, hnone]
    | review | allocate | execute | advance | stop | abandon =>
      intro stage
      simpa [record, stopState, historyReport, List.filterMap_append, List.filterMap_cons,
        eventReport, reviewLedger, allocateLedger, executeLedger, advanceLedger] using ih stage

theorem prefix_late_allWritten_reported (input : StatisticalInput I) (C : Contract I)
    (hlate : C.reporting = .late) (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {state : State I} (path : Prefix input C mode accounting policy seed truth tapes n state) :
    allWritten state.ledger → ∀ stage : I.Stage, state.ledger.reportTime stage ≠ none := by
  classical
  induction path with
  | initial => intro complete stage; exact (complete stage rfl).elim
  | @next n state next earlier step ih =>
    generalize haction : policy seed state.history = action at step
    cases step with
    | write current bit live port resources =>
      intro complete stage
      have hearly : C.reporting ≠ .early := by simp [hlate]
      have hall : allWritten (writeLedger state current bit) := by
        by_cases h : allWritten (writeLedger state current bit)
        · exact h
        · intro other
          simpa only [record, reportedWriteLedger, hearly, ↓reduceIte, h] using complete other
      simp only [record, reportedWriteLedger, hearly, ↓reduceIte, hall]
      exact Option.some_ne_none _
    | review | allocate | execute | advance | stop | abandon => exact ih

theorem prefix_allWritten_reported (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {state : State I} (path : Prefix input C mode accounting policy seed truth tapes n state)
    (complete : allWritten state.ledger) : ∀ stage : I.Stage, state.ledger.reportTime stage ≠ none := by
  cases hr : C.reporting with
  | early =>
    intro stage
    obtain ⟨time, ht⟩ := PaperProofs.Retained.PRetEarlyReports034.prefix_written_reported
      input C hr mode accounting policy seed truth tapes path stage (complete stage)
    rw [ht]
    exact Option.some_ne_none _
  | late => exact prefix_late_allWritten_reported input C hr mode accounting policy seed truth tapes path complete

end PStarLR
