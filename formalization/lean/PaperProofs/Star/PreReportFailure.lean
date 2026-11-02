module

public import PaperProofs.Star.PreReportPosterior
public import PaperProofs.Retained.NativeMatching

/-! The non-Jensen failure bound in frozen star-proofs.tex:58--72.
Actual late-report cuts retain every ordinary write of their run. A
successful star run has a correct ordinary write because q tools cannot
correct q+1 different stages. The analysis-only opposite-write truth
selector therefore forces failure; incomplete histories are covered by
the same implication, without adding writes to the actual record.
C04 is summed over measurable finite truth fibres of arbitrary private
seed x history events. This closes only PreReportFailureLower: the native
observation-information bridge and the Jensen price bound stay separate. -/

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace PaperProofs.Common.Native

variable {I : Instance}

theorem step_written_eq_of_allWritten (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I} (hs : Step input C mode accounting tapes s action next)
    (hw : allWritten s.ledger) : next.ledger.written = s.ledger.written := by
  cases hs with
  | review i _ port => exact False.elim (hw i port)
  | write i bit _ port => exact False.elim (hw i port)
  | allocate | execute | advance | stop | abandon => rfl

theorem prefix_allWritten_of_not_reportFree (input : StatisticalInput I) (C : Contract I)
    (hlate : C.reporting = .late) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (hf : ¬ ReportFree s.history) : allWritten s.ledger := by
  induction hp with
  | initial => exact False.elim (hf (by intro event he; cases he))
  | @next n s next hp hs ih =>
    by_cases hsource : ReportFree s.history
    · obtain hnext | ⟨i, bit, ha⟩ :=
        step_reportFree_or_write input C hlate mode accounting rule seed truth tapes hp hsource hs
      · exact False.elim (hf hnext)
      · generalize haction : rule seed s.history = action at hs ha
        cases hs with
        | write j b =>
          cases ha
          have hw : allWritten (writeLedger s i bit) := by
            by_contra hn
            exact hf ((late_write_reportFree_iff C hlate accounting s i bit hsource).mpr hn)
          change allWritten (reportedWriteLedger C s i bit)
          simp only [reportedWriteLedger, hlate, reduceCtorEq, ↓reduceIte, hw]
          exact hw
        | review | allocate | execute | advance | stop | abandon => cases ha
    · have hw := ih hsource
      unfold allWritten at hw ⊢
      rw [step_written_eq_of_allWritten input C mode accounting tapes hs hw]
      exact hw

theorem prefix_preReport_historyWritten (input : StatisticalInput I) (C : Contract I)
    (hlate : C.reporting = .late) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes n s) (i : I.Stage) :
    historyWritten (s.history.takeWhile beforeTruthReport) i = s.ledger.written i := by
  induction hp with
  | initial => rfl
  | @next n s next hp hs ih =>
    by_cases hnext : ReportFree next.history
    · rw [List.takeWhile_eq_self_iff.mpr hnext]
      exact prefix_historyWritten input C mode accounting rule seed truth tapes (.next hp hs) i
    · by_cases hsource : ReportFree s.history
      · obtain hf | ⟨j, bit, ha⟩ :=
          step_reportFree_or_write input C hlate mode accounting rule seed truth tapes hp hsource hs
        · exact False.elim (hnext hf)
        · have hpnext := Prefix.next hp hs
          generalize haction : rule seed s.history = action at hs ha
          cases hs with
          | write k b =>
            cases ha
            rw [late_write_history_takeWhile C hlate accounting s j bit hsource]
            have hfull := prefix_historyWritten input C mode accounting rule seed truth tapes hpnext i
            change historyWritten (s.history ++ writeResponses C s j bit) i = _ at hfull
            have hparse : historyWritten (s.history ++ [.wrote j bit s.clock]) i =
                historyWritten (s.history ++ writeResponses C s j bit) i := by
              unfold historyWritten
              rw [historyWrite_append_writeResponses]
              simp only [historyWrite, List.filterMap_append, List.filterMap_cons,
                List.filterMap_nil, eventWrite]
              by_cases hji : j = i <;> simp [hji]
            exact hparse.trans hfull
          | review | allocate | execute | advance | stop | abandon => cases ha
      · rw [step_cut_eq_of_not_reportFree input C mode accounting tapes hs hsource, ih,
          step_written_eq_of_allWritten input C mode accounting tapes hs
            (prefix_allWritten_of_not_reportFree input C hlate mode accounting rule seed truth tapes hp hsource)]

end PaperProofs.Common.Native

namespace PaperProofs.Common.Native

variable {I : Instance} {Seed : Type*}

theorem runSuccess_ledger_of_halted (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (sample : Seed × input.World) (N : ℕ)
    (hhalt : (run input C mode accounting rule sample N).halted = true)
    (hsuccess : runSuccess input C mode accounting rule sample) :
    (run input C mode accounting rule sample N).ledger.success C := by
  obtain ⟨n, hn, hs⟩ := hsuccess
  rcases le_total n N with hle | hle
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [run_after_halt input C mode accounting rule sample n hn k]
    exact hs
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [run_after_halt input C mode accounting rule sample N hhalt k] at hs
    exact hs

theorem preReport_historyWritten (input : StatisticalInput I) (C : Contract I)
    (hlate : C.reporting = .late) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .native accounting rule) (sample : Seed × input.World) (i : I.Stage) :
    historyWritten (preReportPublicHistory input C accounting rule sample) i =
      (run input C .native accounting rule sample (nativeActionBound C + 1)).ledger.written i := by
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .native accounting rule hlegal sample (nativeActionBound C + 1)
  exact prefix_preReport_historyWritten input C hlate .native accounting rule sample.1 _ _ hp i

end PaperProofs.Common.Native

namespace PaperProofs.Star.Parameters

open Common Common.Native

universe u

theorem success_has_correct_ordinary_write (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (L : Ledger (starInstance P.tools order))
    (hwf : LedgerWellFormed L) (hs : L.success C) :
    ∃ i, L.written i = some (L.truth i) := by
  classical
  by_contra hnone
  have hall : Retained.executedStages L = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    rcases hs.2.2.2 i with hcorrect | he
    · exact False.elim (hnone ⟨i, hcorrect⟩)
    · exact (Retained.mem_executedStages L i).mpr he
  have hc := (Retained.executedStages_matchable L hwf).card_le_tools
  rw [hall, Finset.card_univ] at hc
  have hcard : Fintype.card (starInstance P.tools order).Stage = P.tools + 1 := by
    simp only [Instance.Stage, Fintype.card_fin]
    exact stageCount_eq P.tools order
  rw [hcard] at hc
  change P.tools + 1 ≤ P.tools at hc
  omega

theorem runSuccess_has_correct_cut_write (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (hlate : C.reporting = .late)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type u}
    (rule : PolicyRule (starInstance P.tools order) Seed)
    (hlegal : LegalRule (P.input order) C .native accounting rule)
    (sample : Seed × (P.input order).World)
    (hs : runSuccess (P.input order) C .native accounting rule sample) :
    ∃ i, historyWritten (preReportPublicHistory (P.input order) C accounting rule sample) i =
      some ((P.input order).truthAt sample.2 i) := by
  have hhalt := run_halted_nativeActionBound_succ (P.input order) C accounting rule hlegal sample
  have hsuccess := runSuccess_ledger_of_halted (P.input order) C .native accounting rule sample _ hhalt hs
  obtain ⟨i, hi⟩ := P.success_has_correct_ordinary_write order C _
    (run_ledgerWellFormed (P.input order) C .native accounting rule hlegal sample _) hsuccess
  refine ⟨i, ?_⟩
  rw [preReport_historyWritten (P.input order) C hlate accounting rule hlegal sample i,
    hi, run_truth (P.input order) C .native accounting rule hlegal]

def cutBadTruth (P : Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order))) : (starInstance P.tools order).Stage → Bool :=
  fun i => !((historyWritten history i).getD false)

theorem cutBadTruth_forces_failure (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (hlate : C.reporting = .late)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type u}
    (rule : PolicyRule (starInstance P.tools order) Seed)
    (hlegal : LegalRule (P.input order) C .native accounting rule)
    (sample : Seed × (P.input order).World)
    (hbad : (P.input order).truthAt sample.2 =
      P.cutBadTruth order (preReportPublicHistory (P.input order) C accounting rule sample)) :
    ¬ runSuccess (P.input order) C .native accounting rule sample := by
  intro hs
  obtain ⟨i, hi⟩ := P.runSuccess_has_correct_cut_write order C hlate accounting rule hlegal sample hs
  have hb := congrFun hbad i
  simp only [cutBadTruth, hi, Option.getD_some] at hb
  cases hx : (P.input order).truthAt sample.2 i <;> simp [hx] at hb

theorem cutPosterior_badTruth_lower (P : Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order))) :
    (∏ i, ENNReal.ofReal (P.preReportMAPError order history i)) ≤
      P.cutPosterior order history (P.cutBadTruth order history) := by
  apply Finset.prod_le_prod
  intro i _
  exact P.preReportMAPError_le_decision order history i ((historyWritten history i).getD false)

section Seed

variable {Seed : Type u} [MeasurableSpace Seed]

theorem preReport_badTruth_event_integral (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (hlate : C.reporting = .late)
    (accounting : NormalAccounting (starInstance P.tools order))
    (rule : PolicyRule (starInstance P.tools order) Seed) (hm : MeasurableRule rule)
    (hlegal : LegalRule (P.input order) C .native accounting rule)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (B : Set (Seed × List (VisibleEvent (starInstance P.tools order)))) (hB : MeasurableSet B) :
    (P.input order).seededWorldLaw ν
      {sample | preReportRecord (P.input order) C accounting rule sample ∈ B ∧
        (P.input order).truthAt sample.2 =
          P.cutBadTruth order (preReportRecord (P.input order) C accounting rule sample).2} =
      ∫⁻ record, B.indicator
        (fun record => P.cutPosterior order record.2 (P.cutBadTruth order record.2)) record
        ∂preReportLaw (P.input order) C accounting rule ν := by
  classical
  let fibres (truth : (starInstance P.tools order).Stage → Bool) :=
    B ∩ {record | P.cutBadTruth order record.2 = truth}
  let events (truth : (starInstance P.tools order).Stage → Bool) :=
    {sample | preReportRecord (P.input order) C accounting rule sample ∈ fibres truth ∧
      (P.input order).truthAt sample.2 = truth}
  have hselect : Measurable (fun record : Seed × List (VisibleEvent (starInstance P.tools order)) =>
      P.cutBadTruth order record.2) := (measurable_of_countable (P.cutBadTruth order)).comp measurable_snd
  have hfibres (truth : (starInstance P.tools order).Stage → Bool) : MeasurableSet (fibres truth) :=
    hB.inter (hselect (measurableSet_singleton truth))
  have hrecord := measurable_preReportRecord (P.input order) C accounting rule hm
  have htruth : Measurable (fun sample : Seed × (P.input order).World => (P.input order).truthAt sample.2) :=
    measurable_pi_iff.mpr fun i => ((P.input order).measurable_truthAt i).comp measurable_snd
  have hevents (truth : (starInstance P.tools order).Stage → Bool) : MeasurableSet (events truth) :=
    ((hfibres truth).preimage hrecord).inter (htruth (measurableSet_singleton truth))
  have hdisjf : Pairwise (fun truth truth' => Disjoint (fibres truth) (fibres truth')) := by
    intro truth truth' hne
    apply Set.disjoint_left.mpr
    intro record hr hr'
    exact hne (hr.2.symm.trans hr'.2)
  have hdisje : Pairwise (fun truth truth' => Disjoint (events truth) (events truth')) := by
    intro truth truth' hne
    apply Set.disjoint_left.mpr
    intro sample hs hs'
    exact hne (hs.2.symm.trans hs'.2)
  have hfibres_union : B = ⋃ truth, fibres truth := by
    ext record
    simp only [Set.mem_iUnion, fibres, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hr
      exact ⟨P.cutBadTruth order record.2, hr, rfl⟩
    · rintro ⟨_, hr, _⟩
      exact hr
  have hevents_union :
      {sample | preReportRecord (P.input order) C accounting rule sample ∈ B ∧
        (P.input order).truthAt sample.2 =
          P.cutBadTruth order (preReportRecord (P.input order) C accounting rule sample).2} =
        ⋃ truth, events truth := by
    ext sample
    simp only [Set.mem_iUnion, events, fibres, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hB, heq⟩
      exact ⟨_, ⟨hB, rfl⟩, heq⟩
    · rintro ⟨truth, ⟨hB, hselector⟩, heq⟩
      exact ⟨hB, heq.trans hselector.symm⟩
  rw [hevents_union, measure_iUnion hdisje hevents, lintegral_indicator hB,
    hfibres_union, lintegral_iUnion hfibres hdisjf]
  apply tsum_congr
  intro truth
  rw [P.preReport_truth_event_integral order C hlate accounting rule hm hlegal ν
    (fibres truth) (hfibres truth) truth, lintegral_indicator (hfibres truth)]
  apply setLIntegral_congr_fun (hfibres truth)
  intro record hr
  change P.cutPosterior order record.2 truth = P.cutPosterior order record.2 (P.cutBadTruth order record.2)
  rw [hr.2]

theorem preReport_failure_lower (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (hlate : C.reporting = .late)
    (accounting : NormalAccounting (starInstance P.tools order))
    (rule : PolicyRule (starInstance P.tools order) Seed) (hm : MeasurableRule rule)
    (hlegal : LegalRule (P.input order) C .native accounting rule)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (B : Set (Seed × List (VisibleEvent (starInstance P.tools order)))) (hB : MeasurableSet B) :
    (∫⁻ record, B.indicator
      (fun record => ∏ i, ENNReal.ofReal (P.preReportMAPError order record.2 i)) record
      ∂preReportLaw (P.input order) C accounting rule ν) ≤
    (P.input order).seededWorldLaw ν
      {sample | preReportRecord (P.input order) C accounting rule sample ∈ B ∧
        ¬ runSuccess (P.input order) C .native accounting rule sample} := by
  calc
    _ ≤ ∫⁻ record, B.indicator
        (fun record => P.cutPosterior order record.2 (P.cutBadTruth order record.2)) record
        ∂preReportLaw (P.input order) C accounting rule ν := by
      apply lintegral_mono
      intro record
      by_cases hr : record ∈ B
      · simpa only [Set.indicator_of_mem hr] using P.cutPosterior_badTruth_lower order record.2
      · simp only [Set.indicator_of_notMem hr, le_refl]
    _ = _ := (P.preReport_badTruth_event_integral order C hlate accounting rule hm hlegal ν B hB).symm
    _ ≤ _ := by
      apply measure_mono
      intro sample hs
      exact ⟨hs.1, P.cutBadTruth_forces_failure order C hlate accounting rule hlegal sample hs.2⟩

end Seed

theorem preReportFailureLower (P : Star.Parameters) : P.PreReportFailureLower.{u} := by
  intro order C hlate accounting Seed m ν hν policy B hB
  exact P.preReport_failure_lower order C hlate.1 accounting policy.rule
    policy.measurable_rule policy.legal ν B hB

end PaperProofs.Star.Parameters
