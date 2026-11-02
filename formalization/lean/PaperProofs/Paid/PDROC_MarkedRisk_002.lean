module

public import PaperProofs.Paid.PDROC_MarkedFees_001
public import PaperProofs.Common.NativeDeadlines
public import PaperProofs.Common.HistorySuffixSuccess
public import PaperProofs.Common.NativeHeadContinuation

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

/-- Every actual early report carries the same immutable written-stage
truth and serial as the current actual ledger. -/
theorem prefix_report_mem_sound (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (source : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting source seed truth tapes n s) :
    ∀ stage bit serial, VisibleEvent.report stage bit serial ∈ s.history →
      s.ledger.written stage ≠ none ∧ s.ledger.truth stage = bit ∧ s.ledger.writeSerial stage = serial := by
  induction hp with
  | initial => simp only [initial, List.not_mem_nil, false_implies, implies_true]
  | @next n before after hp hs ih =>
    generalize haction : source seed before.history = action at hs
    cases hs with
    | write current bit live port resources =>
      intro stage fact serial hm
      simp only [record, writeResponses, hearly, ↓reduceIte, writeLedger,
        List.singleton_append, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false, false_or, VisibleEvent.report.injEq, reduceCtorEq] at hm
      rcases hm with hold | ⟨rfl, rfl, rfl⟩
      · obtain ⟨hw, ht, hserial⟩ := ih stage fact serial hold
        have hne : stage ≠ current := by intro heq; subst current; exact hw port
        simpa only [record, reportedWriteLedger, hearly, ↓reduceIte, writeLedger,
          Function.update_of_ne hne] using And.intro hw (And.intro ht hserial)
      · simp [record, reportedWriteLedger, hearly, writeLedger]
    | review | allocate | execute | advance | stop | abandon =>
      intro stage bit serial hm
      have hold : VisibleEvent.report stage bit serial ∈ before.history := by
        simpa [record, stopState] using hm
      simpa only [record, stopState, reviewLedger, allocateLedger, executeLedger, advanceLedger] using
        ih stage bit serial hold

theorem report_mem_of_historyReport (history : List (VisibleEvent I)) (stage : I.Stage)
    (truth : Bool) (serial : ℕ) (hr : historyReport history stage = some (truth, serial)) :
    VisibleEvent.report stage truth serial ∈ history := by
  have hm : (truth, serial) ∈ (history.filterMap (eventReport stage)).getLast? := by
    change (truth, serial) ∈ historyReport history stage
    rw [hr]
    rfl
  obtain ⟨event, he, hreport⟩ := List.mem_filterMap.mp (List.mem_of_mem_getLast? hm)
  cases event with
  | report current bit clock =>
    simp only [eventReport] at hreport
    split_ifs at hreport with hstage
    subst current
    have hp := Option.some.inj hreport
    simp only [Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩
    exact he
  | observation | wrote | committed | executed | advanced | stopped | abandoned => simp [eventReport] at hreport

theorem goodWriteMark_prefix_iff (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (source : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting source seed truth tapes n s) (stage : I.Stage) :
    HistoryMark.writeError stage false ∈ markedHistory s.history ↔
      s.ledger.written stage = some (s.ledger.truth stage) := by
  constructor
  · intro hm
    obtain ⟨event, he, hmark⟩ := List.mem_filterMap.mp hm
    cases event with
    | report current fact serial =>
      simp only at hmark
      cases hw : historyWrite s.history current with
      | none => simp only [hw] at hmark; contradiction
      | some pair =>
        simp only [hw] at hmark
        split_ifs at hmark with hserial
        · have hpair := HistoryMark.writeError.inj (Option.some.inj hmark)
          rcases hpair with ⟨hstage, herr⟩
          subst current
          obtain ⟨_, htruth, _⟩ := prefix_report_mem_sound input C hearly mode accounting source seed truth tapes hp stage fact serial he
          have hbit : pair.1 = fact := by cases hbit : pair.1 <;> cases fact <;> simp_all
          have hwritten := prefix_historyWrite input C mode accounting source seed truth tapes hp stage
          rw [hw] at hwritten
          have hfinal : s.ledger.written stage = some pair.1 := by
            cases hl : s.ledger.written stage with
            | none => simp only [hl, Option.map_none] at hwritten; contradiction
            | some bit =>
              have heq : pair = (bit, s.ledger.writeSerial stage) := by
                simpa only [hl, Option.map_some, Option.some.injEq] using hwritten
              exact congrArg some (congrArg Prod.fst heq).symm
          simpa only [hbit, ← htruth] using hfinal
    | observation | wrote | committed | executed | advanced | stopped | abandoned => simp at hmark
  · intro hwritten
    have hw := prefix_historyWrite input C mode accounting source seed truth tapes hp stage
    rw [hwritten] at hw
    obtain ⟨time, ht⟩ := prefix_early_written_reported input C hearly mode accounting source seed truth tapes hp stage (by rw [hwritten]; simp)
    have hr := prefix_historyReport_early input C hearly mode accounting source seed truth tapes hp stage
    rw [ht] at hr
    have hmem := report_mem_of_historyReport s.history stage (s.ledger.truth stage) (s.ledger.writeSerial stage) hr
    apply List.mem_filterMap.mpr
    refine ⟨.report stage (s.ledger.truth stage) (s.ledger.writeSerial stage), hmem, ?_⟩
    simp only [hw, Option.map_some, ↓reduceIte]
    cases s.ledger.truth stage <;> rfl





theorem correctionMark_mem_iff (marks : List (HistoryMark I)) (stage : I.Stage) (tool : I.Tool) :
    HistoryMark.correction stage tool ∈ marks ↔ (stage, tool) ∈ markedCorrectionPairs marks := by
  induction marks with
  | nil => simp [markedCorrectionPairs]
  | cons mark marks ih =>
    cases mark <;> simp [markedCorrectionPairs, ih]

theorem correctedMark_prefix_iff (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (source : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting source seed truth tapes n s) (stage : I.Stage) :
    (∃ tool, HistoryMark.correction stage tool ∈ markedHistory s.history) ↔
      ∃ execution ∈ s.ledger.executions, execution.handle.stage = stage := by
  simp only [correctionMark_mem_iff, markedCorrectionPairs_markedHistory, executedPairs,
    prefix_historyExecutions input C mode accounting source seed truth tapes hp,
    List.map_map, List.mem_map]
  constructor
  · rintro ⟨tool, execution, he, hp⟩
    exact ⟨execution, he, congrArg Prod.fst hp⟩
  · rintro ⟨execution, he, hs⟩
    exact ⟨execution.tool, execution, he, Prod.ext hs rfl⟩

/-- The final termination mark is false exactly for ordinary stop. -/
theorem markedLast_halted_prefix_iff (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (source : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting source seed truth tapes n s)
    (hh : s.halted = true) :
    (markedHistory s.history).getLast? = some (.terminate false) ↔ s.ledger.abandoned = false := by
  cases hp with
  | initial => cases hh
  | next earlier hs =>
    generalize haction : source seed _ = action at hs
    cases hs <;> try cases hh
    all_goals simp [stopState, markedHistory, List.filterMap_append]

/-- A marked finite execution succeeds only with a non-abandoning end and
one good original write or genuine correction for EVERY required stage. -/
def MarkedSuccess (marks : List (HistoryMark I)) : Prop :=
  marks.getLast? = some (.terminate false) ∧ ∀ stage : I.Stage,
    HistoryMark.writeError stage false ∈ marks ∨ ∃ tool, HistoryMark.correction stage tool ∈ marks

def MarkedCompletedSuccess : Option (List (HistoryMark I)) → Prop
  | none => False
  | some marks => MarkedSuccess marks

theorem success_halted_prefix_iff_marked (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (source : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting source seed truth tapes n s) (hh : s.halted = true) :
    s.ledger.success C ↔ MarkedSuccess (markedHistory s.history) := by
  rw [MarkedSuccess, markedLast_halted_prefix_iff input C mode accounting source seed truth tapes hp hh]
  simp only [goodWriteMark_prefix_iff input C hearly mode accounting source seed truth tapes hp,
    correctedMark_prefix_iff input C mode accounting source seed truth tapes hp]
  constructor
  · intro hs
    exact ⟨hs.2.1, hs.2.2.2⟩
  · rintro ⟨ha, hcorrect⟩
    have hall : allWritten s.ledger := by
      intro stage
      rcases hcorrect stage with hw | ⟨execution, he, hs⟩
      · rw [hw]; simp
      · have hg := (prefix_ledgerWellFormed input C mode accounting source seed truth tapes hp).genuine execution he
        rw [hs] at hg
        rw [hg.1]; simp
    have hf := prefix_halted_allWritten_finished input C mode accounting source seed truth tapes hp hh hall
    apply (prefix_success_iff_physical input C mode accounting source seed truth tapes hp).mpr
    exact ⟨hf, ha, fun stage => (finalOutput_correct_iff s.ledger stage).mpr (hcorrect stage)⟩

theorem runSuccess_iff_halted_success (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (source : PolicyRule I Seed) (sample : Seed × input.World) (n : ℕ)
    (hh : (run input C mode accounting source sample n).halted = true) :
    runSuccess input C mode accounting source sample ↔
      (run input C mode accounting source sample n).ledger.success C := by
  constructor
  · rintro ⟨k, hk, hs⟩
    by_cases hkn : k ≤ n
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hkn
      rw [run_after_halt input C mode accounting source sample k hk extra]
      exact hs
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_ge hkn)
      rw [run_after_halt input C mode accounting source sample n hh extra] at hs
      exact hs
  · intro hs
    exact ⟨n, hh, hs⟩

/-- A none completion is faithfully decoded as failure; no nonreturn is
silently turned into a successful or zero-cost history. -/
theorem runSuccess_iff_markedCompleted (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (source : PolicyRule I Seed) (hl : LegalRule input C mode accounting source)
    (sample : Seed × input.World) :
    runSuccess input C mode accounting source sample ↔
      MarkedCompletedSuccess ((completedHistory input C mode accounting source sample).map markedHistory) := by
  cases hc : completedHistory input C mode accounting source sample with
  | none =>
    simp only [Option.map_none, MarkedCompletedSuccess, iff_false]
    rintro ⟨n, hn, _⟩
    exact (completedHistory_none_iff input C mode accounting source sample).mp hc ⟨n, hn⟩
  | some history =>
    obtain ⟨n, hh, _, hhistory⟩ := (completedHistory_some_iff input C mode accounting source sample history).mp hc
    rw [runSuccess_iff_halted_success input C mode accounting source sample n hh]
    obtain ⟨k, _, hp⟩ := run_has_prefix input C mode accounting source hl sample n
    simpa only [Option.map_some, MarkedCompletedSuccess, hhistory] using
      success_halted_prefix_iff_marked input C hearly mode accounting source sample.1 _ _ hp hh




local instance markedRiskMeasurableSpace : MeasurableSpace (Option (List (HistoryMark I))) := ⊤
local instance markedRiskSingleton : MeasurableSingletonClass (Option (List (HistoryMark I))) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- Risk is the measure of the independently decoded marked failure event.
The none branch is itself failure, so this exact risk identity also includes
nonreturn and does not need a finite-bill or a.s.-return assumption. -/
theorem risk_eq_markedFailureMeasure (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} [MeasurableSpace Seed] (source : Policy input C mode accounting Seed) (ν : Measure Seed) :
    risk input C mode accounting source.rule ν =
      ((input.seededWorldLaw ν).map (fun sample =>
        (completedHistory input C mode accounting source.rule sample).map markedHistory))
          {history | ¬ MarkedCompletedSuccess history} := by
  have hm : Measurable (fun sample : Seed × input.World =>
      (completedHistory input C mode accounting source.rule sample).map markedHistory) :=
    (measurable_of_countable (fun history : EntryHistory I => history.map markedHistory)).comp
      (measurable_completedHistory input C mode accounting source.rule source.measurable_rule)
  rw [Measure.map_apply hm (MeasurableSpace.measurableSet_top)]
  unfold risk
  congr 1
  ext sample
  exact not_congr (runSuccess_iff_markedCompleted input C hearly mode accounting source.rule source.legal sample)

/-- Exact full marked-completion law, not a mean or successful-path law,
determines the risk for any two original early-report policies. -/
theorem risk_eq_of_markedCompletedLaw (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (modeA modeB : ResourceMode) (accounting : NormalAccounting I)
    {SeedA : Type*} {SeedB : Type*} [MeasurableSpace SeedA] [MeasurableSpace SeedB]
    (sourceA : Policy input C modeA accounting SeedA) (sourceB : Policy input C modeB accounting SeedB)
    (νA : Measure SeedA) (νB : Measure SeedB)
    (hlaw : (input.seededWorldLaw νA).map (fun sample =>
        (completedHistory input C modeA accounting sourceA.rule sample).map markedHistory) =
      (input.seededWorldLaw νB).map (fun sample =>
        (completedHistory input C modeB accounting sourceB.rule sample).map markedHistory)) :
    risk input C modeA accounting sourceA.rule νA = risk input C modeB accounting sourceB.rule νB := by
  rw [risk_eq_markedFailureMeasure input C hearly modeA accounting sourceA νA,
    risk_eq_markedFailureMeasure input C hearly modeB accounting sourceB νB, hlaw]

/-- D06's original joint virtual-history law plus the pathwise marked
coupling imply exact original risk equality. No successful-path conditioning
or risk-performance field is assumed; abandoned/unwritten/none runs fail. -/
theorem risk_eq_of_sourceHistoryLaw (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type*} {SimSeed : Type*} [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (νsource : Measure SourceSeed) (νactual : Measure SimSeed)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting SourceSeed)
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed)
    (hm : RecordSimulatorMeasurable data)
    (hlaw : P.SourceHistoryLaw fee hfee fee hfee C accounting νsource νactual source.rule actual.rule data)
    (hmarks : ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw νactual,
      (completedHistory (P.input fee hfee) C.val .uncapped accounting actual.rule sample).map markedHistory =
        (P.shadowCompletedHistory fee hfee C accounting actual.rule data sample).map markedHistory) :
    risk (P.input fee hfee) C.val .uncapped accounting actual.rule νactual =
      risk (P.input fee hfee) C.val .uncapped accounting source.rule νsource := by
  have hma : Measurable (fun sample : SimSeed × (P.input fee hfee).World =>
      (data.sourceSeed sample.1, P.shadowCompletedHistory fee hfee C accounting actual.rule data sample)) :=
    (hm.1.comp measurable_fst).prodMk hlaw.1
  have hms : Measurable (fun sample : SourceSeed × (P.input fee hfee).World =>
      (sample.1, completedHistory (P.input fee hfee) C.val .uncapped accounting source.rule sample)) :=
    measurable_fst.prodMk (measurable_completedHistory (P.input fee hfee) C.val .uncapped accounting
      source.rule source.measurable_rule)
  let project := fun pair : SourceSeed × EntryHistory P.sharedInstance => pair.2.map markedHistory
  have hmp : Measurable project := (measurable_of_countable
    (fun history : EntryHistory P.sharedInstance => history.map markedHistory)).comp measurable_snd
  have h := congrArg (fun μ => μ.map project) hlaw.2.2
  rw [Measure.map_map hmp hma, Measure.map_map hmp hms] at h
  apply risk_eq_of_markedCompletedLaw (P.input fee hfee) C.val C.property.1.1 .uncapped .uncapped accounting actual source νactual νsource
  exact (Measure.map_congr hmarks).trans h

end PDROC

