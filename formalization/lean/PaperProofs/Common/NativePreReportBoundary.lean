module

public import PaperProofs.Common.NativePreReportCausality

/-!
Full native pre-report cut-cylinder semantics, including its last late-write
packet. Its public prefix keeps the ordinary wrote event and removes reports.
Normal accounting may depend on the truth-bearing response packet, so full
States after that packet are not identified. Original all-world legality
supplies an actual legal write in each replacement world. This gives the
exact joint likelihood of any cut history and complete truth assignment,
uniformly over measurable events of the original private seed. Posterior
normalization remains separate. No observations or policy inputs are added.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace PaperProofs.Common.Native

variable {I : Instance}

theorem reportFree_append_singleton (history : List (VisibleEvent I)) (event : VisibleEvent I)
    (hf : ReportFree history) (he : beforeTruthReport event = true) :
    ReportFree (history ++ [event]) := by
  intro e hem
  rcases List.mem_append.mp hem with hem | hem
  · exact hf e hem
  · have heq : e = event := List.mem_singleton.mp hem
    exact heq ▸ he

theorem late_write_reportFree_iff (C : Contract I) (hlate : C.reporting = .late)
    (accounting : NormalAccounting I) (s : State I) (i : I.Stage) (bit : Bool)
    (hf : ReportFree s.history) :
    ReportFree (record accounting s (.write i bit) (writeResponses C s i bit)
      (reportedWriteLedger C s i bit) s.cursor false).history ↔
        ¬ allWritten (writeLedger s i bit) := by
  constructor
  · exact reportFree_write_not_allWritten C hlate accounting s i bit
  · intro hn
    have hrsp : writeResponses C s i bit = [.wrote i bit s.clock] := by
      simp [writeResponses, hlate, hn]
    change ReportFree (s.history ++ writeResponses C s i bit)
    rw [hrsp]
    exact reportFree_append_singleton _ _ hf rfl

theorem step_reportFree_or_write (input : StatisticalInput I) (C : Contract I)
    (hlate : C.reporting = .late) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s next : State I} {action : Action I}
    (hp : Prefix input C mode accounting rule seed truth tapes n s) (hf : ReportFree s.history)
    (hs : Step input C mode accounting tapes s action next) :
    ReportFree next.history ∨ ∃ i bit, action = .write i bit := by
  have haction := step_preReportAction input C hlate mode accounting rule seed truth tapes hp hf hs
  cases hs with
  | review => exact Or.inl (reportFree_append_singleton _ _ hf rfl)
  | write i bit => exact Or.inr ⟨i, bit, rfl⟩
  | allocate | execute => exact False.elim haction
  | advance => exact Or.inl (reportFree_append_singleton _ _ hf rfl)
  | stop => exact Or.inl (reportFree_append_singleton _ _ hf rfl)
  | abandon => exact Or.inl (reportFree_append_singleton _ _ hf rfl)

/-- Once a report is present, later visible events cannot change the cut. -/
theorem takeWhile_beforeTruthReport_append_of_not_reportFree
    (history suffix : List (VisibleEvent I)) (hf : ¬ ReportFree history) :
    (history ++ suffix).takeWhile beforeTruthReport = history.takeWhile beforeTruthReport := by
  induction history with
  | nil => exact False.elim (hf (by intro event he; cases he))
  | cons event history ih =>
    by_cases he : beforeTruthReport event = true
    · have hh : ¬ ReportFree history := by
        intro h
        exact hf (by
          intro e hem
          rcases List.mem_cons.mp hem with rfl | hem
          · exact he
          · exact h e hem)
      simpa only [List.cons_append, List.takeWhile_cons, he, ↓reduceIte] using
        congrArg (List.cons event) (ih hh)
    · simp [he]

theorem step_cut_eq_of_not_reportFree (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I} (hs : Step input C mode accounting tapes s action next)
    (hf : ¬ ReportFree s.history) :
    next.history.takeWhile beforeTruthReport = s.history.takeWhile beforeTruthReport := by
  obtain ⟨suffix, hh⟩ := step_history_extends input C mode accounting tapes hs
  rw [hh]
  exact takeWhile_beforeTruthReport_append_of_not_reportFree s.history suffix hf

/-- The first-report write is replayed by the SAME legal policy under all
replacement truth assignments and all tapes agreeing on bought observations.
Only the public cut is equated; actual normal calls after the reports need
not agree. Both native original caps and uncapped executions are covered. -/
theorem prefix_replay_late_write_cut (input : StatisticalInput I) (C : Contract I)
    (hlate : C.reporting = .late) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting rule)
    (seed : Seed) (truth truth' : I.Stage → Bool) (tapes tapes' : ReviewTapes input)
    {n : ℕ} {s next : State I} (i : I.Stage) (bit : Bool)
    (hp : Prefix input C mode accounting rule seed truth tapes n s) (hf : ReportFree s.history)
    (ha : rule seed s.history = .write i bit)
    (hs : Step input C mode accounting tapes s (.write i bit) next)
    (hcyl : tapes' ∈ publicWordCylinder input s.history) :
    ∃ next', Prefix input C mode accounting rule seed truth' tapes' (n + 1) next' ∧
      Step input C mode accounting tapes' (retargetTruth s truth') (.write i bit) next' ∧
      next'.history.takeWhile beforeTruthReport = next.history.takeWhile beforeTruthReport := by
  have hp' := prefix_replay_of_publicWordCylinder input C hlate mode accounting rule seed
    truth truth' tapes tapes' hp hf hcyl
  have hactive : (retargetTruth s truth').halted = false := by
    change s.halted = false
    exact step_source_active input C mode accounting tapes hs
  obtain ⟨next', hs'⟩ := hlegal seed truth' tapes' n (retargetTruth s truth') hp' hactive
  have ha' : rule seed (retargetTruth s truth').history = .write i bit := ha
  rw [ha'] at hs'
  refine ⟨next', .next hp' (ha'.symm ▸ hs'), hs', ?_⟩
  cases hs
  cases hs'
  rw [late_write_history_takeWhile C hlate accounting s i bit hf,
    late_write_history_takeWhile C hlate accounting (retargetTruth s truth') i bit hf]
  rfl

/-- A real finite public cut can always be replayed after changing hidden
truth and unobserved letters. Replay stops at its first report; later
truth-dependent normal accounting is allowed to differ. -/
theorem prefix_replay_public_cut (input : StatisticalInput I) (C : Contract I)
    (hlate : C.reporting = .late) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting rule)
    (seed : Seed) (truth truth' : I.Stage → Bool) (tapes tapes' : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (htape : ∀ i k, k < (historyObservations (s.history.takeWhile beforeTruthReport) i).length →
      tapes' i k = tapes i k) :
    ∃ k ≤ n, ∃ s', Prefix input C mode accounting rule seed truth' tapes' k s' ∧
      s'.history.takeWhile beforeTruthReport = s.history.takeWhile beforeTruthReport ∧
      (ReportFree s.history → s' = retargetTruth s truth') ∧
      (¬ ReportFree s.history → ¬ ReportFree s'.history) := by
  revert htape
  induction hp with
  | initial =>
    intro htape
    exact ⟨0, le_rfl, initial truth', .initial, rfl, fun _ => rfl,
      fun hn => False.elim (hn (by intro event he; cases he))⟩
  | @next n s next earlier step ih =>
    intro htape
    by_cases hnext : ReportFree next.history
    · have htape' : ∀ i k, k < (historyObservations next.history i).length → tapes' i k = tapes i k := by
        simpa only [List.takeWhile_eq_self_iff.mpr hnext] using htape
      have hp' := prefix_retarget_reportFree input C hlate mode accounting rule seed truth truth'
        tapes tapes' (.next earlier step) hnext htape'
      exact ⟨n + 1, le_rfl, retargetTruth next truth', hp', rfl, fun _ => rfl,
        fun hn => False.elim (hn hnext)⟩
    · by_cases hbefore : ReportFree s.history
      · obtain ⟨i, bit, ha⟩ := (step_reportFree_or_write input C hlate mode accounting rule seed
          truth tapes earlier hbefore step).resolve_left hnext
        have hs : Step input C mode accounting tapes s (.write i bit) next := ha ▸ step
        have hcut : next.history.takeWhile beforeTruthReport = s.history ++ [.wrote i bit s.clock] := by
          cases hs
          exact late_write_history_takeWhile C hlate accounting s i bit hbefore
        have hobs (j : I.Stage) : historyObservations (next.history.takeWhile beforeTruthReport) j =
            historyObservations s.history j := by
          rw [hcut]
          simp [historyObservations, eventObservation]
        have hcyl : tapes' ∈ publicWordCylinder input s.history := by
          intro j k hk
          have hletter := htape j k (by rw [hobs]; exact hk)
          rw [hletter]
          exact prefix_mem_publicWordCylinder input C mode accounting rule seed truth tapes earlier j k hk
        obtain ⟨next', hp', hs', hcut'⟩ := prefix_replay_late_write_cut input C hlate mode accounting
          rule hlegal seed truth truth' tapes tapes' i bit earlier hbefore ha hs hcyl
        have hnot : ¬ ReportFree next'.history := by
          cases hs
          cases hs'
          intro hf'
          apply hnext
          apply (late_write_reportFree_iff C hlate accounting s i bit hbefore).mpr
          exact reportFree_write_not_allWritten C hlate accounting (retargetTruth s truth') i bit hf'
        exact ⟨n + 1, le_rfl, next', hp', hcut', fun hf => False.elim (hnext hf), fun _ => hnot⟩
      · have hcut := step_cut_eq_of_not_reportFree input C mode accounting tapes step hbefore
        rw [hcut] at htape
        obtain ⟨k, hkn, s', hp', hcut', _, hn⟩ := ih htape
        exact ⟨k, hkn.trans (Nat.le_succ n), s', hp', hcut'.trans hcut.symm,
          fun hf => False.elim (hnext hf), fun _ => hn hbefore⟩

theorem run_cut_after_report {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World) (n : ℕ)
    (hn : ¬ ReportFree (run input C mode accounting rule sample n).history) (extra : ℕ) :
    (run input C mode accounting rule sample (n + extra)).history.takeWhile beforeTruthReport =
        (run input C mode accounting rule sample n).history.takeWhile beforeTruthReport ∧
      ¬ ReportFree (run input C mode accounting rule sample (n + extra)).history := by
  induction extra with
  | zero => exact ⟨rfl, hn⟩
  | succ extra ih =>
    by_cases hh : (run input C mode accounting rule sample (n + extra)).halted = true
    · rw [Nat.add_succ, run_succ_of_halted input C mode accounting rule sample (n + extra) hh]
      exact ih
    · have ha : (run input C mode accounting rule sample (n + extra)).halted = false :=
        Bool.eq_false_iff.mpr hh
      have hp := run_prefix_of_active input C mode accounting rule hlegal sample (n + extra) ha
      obtain ⟨next, hs⟩ := hlegal sample.1 (input.truthAt sample.2) (worldTapes input sample.2)
        (n + extra) _ hp ha
      rw [Nat.add_succ, run_succ_of_step input C mode accounting rule sample (n + extra) next ha hs]
      exact ⟨(step_cut_eq_of_not_reportFree input C mode accounting (worldTapes input sample.2) hs ih.2).trans ih.1,
        fun hf => ih.2 (step_reportFree_source input C mode accounting (worldTapes input sample.2) hs hf)⟩

/-- Full native pre-report records, including the first-report write,
are invariant under changing all hidden truths and every unbought letter.
The original seed and actual public event prefix are the only record data.
This is a deterministic causal bridge, not yet posterior normalization. -/
theorem preReportPublicHistory_replay {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hlate : C.reporting = .late) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .native accounting rule) (sample : Seed × input.World)
    (truth' : I.Stage → Bool) (tapes' : ReviewTapes input)
    (htape : ∀ i k, k < (historyObservations (preReportPublicHistory input C accounting rule sample) i).length →
      tapes' i k = worldTapes input sample.2 i k) :
    preReportPublicHistory input C accounting rule (sample.1, replayWorld input truth' tapes') =
      preReportPublicHistory input C accounting rule sample := by
  let horizon := nativeActionBound C + 1
  obtain ⟨m, hmh, hp⟩ := run_has_prefix input C .native accounting rule hlegal sample horizon
  obtain ⟨k, hkm, s', hp', hc, hf, hn⟩ := prefix_replay_public_cut input C hlate .native accounting
    rule hlegal sample.1 (input.truthAt sample.2) truth' (worldTapes input sample.2) tapes' hp htape
  have heq := prefix_eq_run input C .native accounting rule sample.1 truth' tapes' hp'
  obtain ⟨extra, hextra⟩ := Nat.exists_eq_add_of_le (hkm.trans hmh)
  by_cases hreport : ReportFree (run input C .native accounting rule sample horizon).history
  · have hhalt : s'.halted = true := by
      rw [hf hreport]
      exact run_halted_nativeActionBound_succ input C accounting rule hlegal sample
    have hh : (run input C .native accounting rule (sample.1, replayWorld input truth' tapes') k).halted = true := by
      rw [heq]
      exact hhalt
    have hafter := run_after_halt input C .native accounting rule (sample.1, replayWorld input truth' tapes') k hh extra
    change (run input C .native accounting rule (sample.1, replayWorld input truth' tapes') horizon).history.takeWhile
      beforeTruthReport = _
    rw [hextra, hafter, heq]
    exact hc
  · have hnot : ¬ ReportFree (run input C .native accounting rule (sample.1, replayWorld input truth' tapes') k).history := by
      rw [heq]
      exact hn hreport
    have hafter := run_cut_after_report input C .native accounting rule hlegal
      (sample.1, replayWorld input truth' tapes') k hnot extra
    change (run input C .native accounting rule (sample.1, replayWorld input truth' tapes') horizon).history.takeWhile
      beforeTruthReport = _
    rw [hextra]
    exact hafter.1.trans (by rw [heq]; exact hc)

theorem prefix_cut_mem_publicWordCylinder (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s) :
    tapes ∈ publicWordCylinder input (s.history.takeWhile beforeTruthReport) := by
  intro i k hk
  have hword : historyObservations (s.history.takeWhile beforeTruthReport) i <+:
      historyObservations s.history i :=
    (List.takeWhile_prefix beforeTruthReport).filterMap (eventObservation i)
  exact (prefix_mem_publicWordCylinder input C mode accounting rule seed truth tapes hp i k
    (lt_of_lt_of_le hk hword.length_le)).trans (hword.getElem hk).symm

theorem preReportPublicHistory_mem_publicWordCylinder {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C .native accounting rule)
    (sample : Seed × input.World) :
    worldTapes input sample.2 ∈ publicWordCylinder input (preReportPublicHistory input C accounting rule sample) := by
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .native accounting rule hlegal sample (nativeActionBound C + 1)
  exact prefix_cut_mem_publicWordCylinder input C .native accounting rule sample.1 _ _ hp

theorem prefix_cut_observation_alphabet (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (i : I.Stage) (symbol : ℕ) (hsymbol : symbol ∈ historyObservations (s.history.takeWhile beforeTruthReport) i) :
    symbol < (input.experiment i).alphabetSize := by
  have hword : historyObservations (s.history.takeWhile beforeTruthReport) i <+:
      historyObservations s.history i :=
    (List.takeWhile_prefix beforeTruthReport).filterMap (eventObservation i)
  exact prefix_historyObservation_alphabet input C mode accounting rule seed truth tapes hp i symbol
    (List.IsPrefix.mem hsymbol hword)

theorem preReportPublicHistory_observation_alphabet {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C .native accounting rule)
    (sample : Seed × input.World) (i : I.Stage) (symbol : ℕ)
    (hsymbol : symbol ∈ historyObservations (preReportPublicHistory input C accounting rule sample) i) :
    symbol < (input.experiment i).alphabetSize := by
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .native accounting rule hlegal sample (nativeActionBound C + 1)
  exact prefix_cut_observation_alphabet input C .native accounting rule sample.1 _ _ hp i symbol hsymbol

/-- The gate uses only the ORIGINAL private seed and a fixed reference
world in its mathematical definition. The reference world is not given to
the policy, and the resulting gate is common to every sampled truth vector. -/
noncomputable def preReportSeedGate {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) (history : List (VisibleEvent I)) : Set Seed :=
  {seed | preReportPublicHistory input C accounting rule (seed, replayWorld input truth tapes) = history}

theorem measurableSet_preReportSeedGate {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hm : MeasurableRule rule) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) (history : List (VisibleEvent I)) :
    MeasurableSet (preReportSeedGate input C accounting rule truth tapes history) :=
  ((measurable_preReportPublicHistory input C accounting rule hm).comp
    (measurable_id.prodMk measurable_const)) (measurableSet_singleton history)

/-- Exact full cut-cylinder equivalence, including pre-report abandonment
and the ordinary write in the first report packet. No complete State is
identified after that packet, and no event is selected by eventual success. -/
theorem preReportPublicHistory_eq_iff_gate_and_cylinder {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hlate : C.reporting = .late)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .native accounting rule) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) (history : List (VisibleEvent I))
    (htapes : tapes ∈ publicWordCylinder input history) (sample : Seed × input.World) :
    preReportPublicHistory input C accounting rule sample = history ↔
      sample.1 ∈ preReportSeedGate input C accounting rule truth tapes history ∧
        worldTapes input sample.2 ∈ publicWordCylinder input history := by
  constructor
  · intro hh
    have hc := preReportPublicHistory_mem_publicWordCylinder input C accounting rule hlegal sample
    rw [hh] at hc
    have ht : ∀ i k, k < (historyObservations (preReportPublicHistory input C accounting rule sample) i).length →
        tapes i k = worldTapes input sample.2 i k := by
      intro i k hk
      rw [hh] at hk
      exact Fin.ext ((htapes i k hk).trans (hc i k hk).symm)
    exact ⟨(preReportPublicHistory_replay input C hlate accounting rule hlegal sample truth tapes ht).trans hh, hc⟩
  · rintro ⟨hgate, hc⟩
    have hgate' : preReportPublicHistory input C accounting rule (sample.1, replayWorld input truth tapes) = history := hgate
    have ht : ∀ i k, k < (historyObservations
        (preReportPublicHistory input C accounting rule (sample.1, replayWorld input truth tapes)) i).length →
        worldTapes input sample.2 i k = worldTapes input (replayWorld input truth tapes) i k := by
      intro i k hk
      rw [hgate'] at hk
      exact Fin.ext ((hc i k hk).trans (htapes i k hk).symm)
    have hrep := preReportPublicHistory_replay input C hlate accounting rule hlegal
      (sample.1, replayWorld input truth tapes) (input.truthAt sample.2) (worldTapes input sample.2) ht
    have heta : replayWorld input (input.truthAt sample.2) (worldTapes input sample.2) = sample.2 := rfl
    rw [heta] at hrep
    exact hrep.trans hgate'

theorem preReport_jointTruth_seedEvent_eq_rectangle {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hlate : C.reporting = .late)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .native accounting rule) (truth truth' : I.Stage → Bool)
    (tapes : ReviewTapes input) (history : List (VisibleEvent I))
    (htapes : tapes ∈ publicWordCylinder input history)
    (hvalid : ∀ i symbol, symbol ∈ historyObservations history i → symbol < (input.experiment i).alphabetSize)
    (B : Set Seed) :
    {sample : Seed × input.World | sample.1 ∈ B ∧ input.truthAt sample.2 = truth' ∧
      preReportPublicHistory input C accounting rule sample = history} =
      (B ∩ preReportSeedGate input C accounting rule truth tapes history) ×ˢ
        worldWordCylinder input truth' (fun i => historyObservationWord input history i (hvalid i)) := by
  ext sample
  rw [Set.mem_ofPred_eq, preReportPublicHistory_eq_iff_gate_and_cylinder input C hlate accounting rule hlegal truth tapes history htapes sample]
  constructor
  · rintro ⟨hB, htruth, hgate, hc⟩
    refine ⟨⟨hB, hgate⟩, ?_⟩
    intro i _
    exact ⟨congrFun htruth i, ((publicWordCylinder_iff_prefixEvents input history hvalid _).mp hc) i⟩
  · rintro ⟨⟨hB, hgate⟩, hworld⟩
    have htruth : input.truthAt sample.2 = truth' := by
      funext i
      exact (hworld i (Set.mem_univ i)).1
    have hc : worldTapes input sample.2 ∈ publicWordCylinder input history :=
      (publicWordCylinder_iff_prefixEvents input history hvalid _).mpr
        (fun i => (hworld i (Set.mem_univ i)).2)
    exact ⟨hB, htruth, hgate, hc⟩

/-- Joint likelihood for the FULL actual pre-report cut, uniformly over all
measurable seed events and complete truth assignments. Posterior division
and summation over cut histories are deliberately not postulated here. -/
theorem preReport_jointTruth_seedEvent_law {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hlate : C.reporting = .late)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hm : MeasurableRule rule)
    (hlegal : LegalRule input C .native accounting rule) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (truth truth' : I.Stage → Bool) (tapes : ReviewTapes input) (history : List (VisibleEvent I))
    (htapes : tapes ∈ publicWordCylinder input history)
    (hvalid : ∀ i symbol, symbol ∈ historyObservations history i → symbol < (input.experiment i).alphabetSize)
    (B : Set Seed) (hB : MeasurableSet B) :
    let event := {sample : Seed × input.World | sample.1 ∈ B ∧ input.truthAt sample.2 = truth' ∧
      preReportPublicHistory input C accounting rule sample = history}
    MeasurableSet event ∧ input.seededWorldLaw ν event =
      ν (B ∩ preReportSeedGate input C accounting rule truth tapes history) *
        ∏ i, (input.experiment i).priorMass (truth' i) *
          ENNReal.ofReal ((input.experiment i).wordProbability (truth' i)
            (historyObservationWord input history i (hvalid i))) := by
  dsimp only
  rw [preReport_jointTruth_seedEvent_eq_rectangle input C hlate accounting rule hlegal truth truth' tapes history htapes hvalid B]
  constructor
  · exact (hB.inter (measurableSet_preReportSeedGate input C accounting rule hm truth tapes history)).prod
      (measurableSet_worldWordCylinder input truth' _)
  · rw [StatisticalInput.seededWorldLaw, Measure.prod_prod, worldLaw_worldWordCylinder]

end PaperProofs.Common.Native
