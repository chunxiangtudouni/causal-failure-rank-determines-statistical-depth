module

public import PaperProofs.Star.PreReportFailure

/-! The ACTUAL native observation-information bridge of frozen C:74--85.
Every late-report cut retains the original run's entire bought observation
word. Its per-stage count is a bounded stopping rule after fixing only the
original private seed and the OTHER stages' independent hidden samples.
No current hidden truth, complete State, eventual success, or MAP condition
is put into that external seed or required of the original policy.

The auxiliary local test's unused decision is constant; its stopping time
and word are exactly the original policy's bought word. Original finite
native quotas prove finite ET before the stopped-posterior identity is
applied. The product-law reassembly returns all integrals to the original
world law, and all costs remain ENNReal, including failed/abandoned paths.
Only the information identity is proved here; Jensen remains separate. -/

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace PaperProofs.Common.Native

variable {I : Instance}

@[simp] private theorem filterMap_reportAll_observation (L : Ledger I) (i : I.Stage) :
    (reportAll L).filterMap (eventObservation i) = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro event he
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp he
  rfl

@[simp] private theorem filterMap_writeResponses_observation (C : Contract I) (s : State I)
    (i j : I.Stage) (bit : Bool) :
    (writeResponses C s i bit).filterMap (eventObservation j) = [] := by
  classical
  simp only [writeResponses, List.filterMap_append, List.filterMap_cons,
    eventObservation, List.filterMap_nil, List.nil_append]
  split_ifs <;> simp only [List.filterMap_cons, eventObservation,
    List.filterMap_nil, filterMap_reportAll_observation]

theorem step_historyObservations_eq_of_allWritten (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I} (hs : Step input C mode accounting tapes s action next)
    (hw : allWritten s.ledger) (i : I.Stage) :
    historyObservations next.history i = historyObservations s.history i := by
  cases hs with
  | review j _ port => exact False.elim (hw j port)
  | write j bit _ port => exact False.elim (hw j port)
  | allocate | execute | advance | stop | abandon =>
    simp [record, stopState, historyObservations, List.filterMap_append, eventObservation]

theorem prefix_preReport_observations (input : StatisticalInput I) (C : Contract I)
    (hlate : C.reporting = .late) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes n s) (i : I.Stage) :
    historyObservations (s.history.takeWhile beforeTruthReport) i = historyObservations s.history i := by
  induction hp with
  | initial => rfl
  | @next n s next hp hs ih =>
    by_cases hnext : ReportFree next.history
    · rw [List.takeWhile_eq_self_iff.mpr hnext]
    · by_cases hsource : ReportFree s.history
      · obtain hf | ⟨j, bit, ha⟩ :=
          step_reportFree_or_write input C hlate mode accounting rule seed truth tapes hp hsource hs
        · exact False.elim (hnext hf)
        · generalize haction : rule seed s.history = action at hs ha
          cases hs with
          | write k b =>
            cases ha
            rw [late_write_history_takeWhile C hlate accounting s j bit hsource]
            simp [record, historyObservations, List.filterMap_append, List.filterMap_cons,
              List.filterMap_nil, eventObservation]
          | review | allocate | execute | advance | stop | abandon => cases ha
      · rw [step_cut_eq_of_not_reportFree input C mode accounting tapes hs hsource, ih,
          step_historyObservations_eq_of_allWritten input C mode accounting tapes hs
            (prefix_allWritten_of_not_reportFree input C hlate mode accounting rule seed truth tapes hp hsource)]

theorem preReport_observations (input : StatisticalInput I) (C : Contract I)
    (hlate : C.reporting = .late) (accounting : NormalAccounting I) {Seed : Type*}
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C .native accounting rule)
    (sample : Seed × input.World) (i : I.Stage) :
    historyObservations (preReportPublicHistory input C accounting rule sample) i =
      historyObservations (run input C .native accounting rule sample (nativeActionBound C + 1)).history i := by
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .native accounting rule hlegal sample (nativeActionBound C + 1)
  exact prefix_preReport_observations input C hlate .native accounting rule sample.1 _ _ hp i

theorem preReport_observations_length (input : StatisticalInput I) (C : Contract I)
    (hlate : C.reporting = .late) (accounting : NormalAccounting I) {Seed : Type*}
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C .native accounting rule)
    (sample : Seed × input.World) (i : I.Stage) :
    ((historyObservations (preReportPublicHistory input C accounting rule sample) i).length : ℕ∞) =
      (run input C .native accounting rule sample (nativeActionBound C + 1)).ledger.reviews i := by
  rw [preReport_observations input C hlate accounting rule hlegal sample i]
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .native accounting rule hlegal sample (nativeActionBound C + 1)
  exact prefix_historyObservations_length input C .native accounting rule sample.1 _ _ hp i

theorem preReport_observations_length_le (input : StatisticalInput I) (C : Contract I)
    (hlate : C.reporting = .late) (accounting : NormalAccounting I) {Seed : Type*}
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C .native accounting rule)
    (sample : Seed × input.World) (i : I.Stage) :
    (historyObservations (preReportPublicHistory input C accounting rule sample) i).length ≤ C.reviewQuota i := by
  have hcaps := (run_native_obeysCaps input C accounting rule hlegal sample (nativeActionBound C + 1)).1 i
  rw [← preReport_observations_length input C hlate accounting rule hlegal sample i] at hcaps
  exact ENat.natCast_le_natCast.mp hcaps

@[simp] private theorem reportedWrite_reviews (C : Contract I) (s : State I) (i : I.Stage) (bit : Bool) :
    (reportedWriteLedger C s i bit).reviews = s.ledger.reviews := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

theorem step_reviews_le (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I} (hs : Step input C mode accounting tapes s action next) (i : I.Stage) :
    s.ledger.reviews i ≤ next.ledger.reviews i := by
  cases hs with
  | review j =>
    by_cases hij : i = j
    · subst j
      simp only [record, reviewLedger, Function.update_self]
      exact le_self_add
    · simp [record, reviewLedger, Function.update_of_ne hij]
  | write => simp only [record, reportedWrite_reviews, le_refl]
  | allocate | execute | advance | stop | abandon => exact le_rfl

theorem step_observationBill_mono (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I} (hs : Step input C mode accounting tapes s action next) :
    s.ledger.observationBill input.fees ≤ next.ledger.observationBill input.fees := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_right (ENat.toENNReal_mono (step_reviews_le input C mode accounting tapes hs i)) _

theorem nextFromFrontier_observationBill_mono (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (s : State I)
    (action : Action I) (frontier : Frontier input) :
    s.ledger.observationBill input.fees ≤
      (nextFromFrontier input C mode accounting s action frontier).ledger.observationBill input.fees := by
  classical
  unfold nextFromFrontier
  split_ifs with hhalt hex
  · exact le_rfl
  · exact step_observationBill_mono input C mode accounting _ (Classical.choose_spec hex)
  · exact le_rfl

theorem run_observationBill_mono (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*} (rule : PolicyRule I Seed)
    (sample : Seed × input.World) :
    Monotone (fun n => (run input C mode accounting rule sample n).ledger.observationBill input.fees) := by
  apply monotone_nat_of_le_succ
  intro n
  exact nextFromFrontier_observationBill_mono input C mode accounting _ _ _

theorem runObservationBill_of_halted (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*} (rule : PolicyRule I Seed)
    (sample : Seed × input.World) (n : ℕ) (hhalt : (run input C mode accounting rule sample n).halted = true) :
    runObservationBill input C mode accounting rule sample =
      (run input C mode accounting rule sample n).ledger.observationBill input.fees := by
  apply le_antisymm
  · apply iSup_le
    intro k
    by_cases hkn : k ≤ n
    · exact run_observationBill_mono input C mode accounting rule sample hkn
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_ge hkn)
      rw [run_after_halt input C mode accounting rule sample n hhalt extra]
  · exact le_iSup (fun k => (run input C mode accounting rule sample k).ledger.observationBill input.fees) n

end PaperProofs.Common.Native

namespace PaperProofs.Common.StatisticalInput

open ProbabilityTheory

variable {I : Instance}

abbrev OtherStages (input : StatisticalInput I) (i : I.Stage) :=
  ∀ j : {j : I.Stage // j ≠ i}, input.StageSample j.val

def otherStagesView (input : StatisticalInput I) (i : I.Stage) (world : input.World) : input.OtherStages i :=
  fun j => world j.val

theorem measurable_otherStagesView (input : StatisticalInput I) (i : I.Stage) :
    Measurable (input.otherStagesView i) :=
  measurable_pi_iff.mpr fun j => measurable_pi_apply j.val

theorem otherStagesView_independent_current (input : StatisticalInput I) (i : I.Stage) :
    IndepFun (input.otherStagesView i) (fun world : input.World => world i) input.worldLaw := by
  have hd : Disjoint {j : I.Stage | j ≠ i} {i} := Set.disjoint_singleton_right.mpr (by simp)
  have h := (input.worldLaw_independent_stages).indepFun_set {j : I.Stage | j ≠ i} {i} hd
    (fun j => measurable_pi_apply j)
  exact h.comp measurable_id
    (measurable_pi_apply (⟨i, Set.mem_singleton i⟩ : ({i} : Set I.Stage)))

section Seed

variable {Seed : Type*} [MeasurableSpace Seed]

def externalStageView (input : StatisticalInput I) (i : I.Stage) (sample : Seed × input.World) :
    Seed × input.OtherStages i := (sample.1, input.otherStagesView i sample.2)

theorem measurable_externalStageView (input : StatisticalInput I) (i : I.Stage) :
    Measurable (input.externalStageView (Seed := Seed) i) :=
  measurable_fst.prodMk ((input.measurable_otherStagesView i).comp measurable_snd)

noncomputable def externalStageLaw (input : StatisticalInput I) (i : I.Stage) (ν : Measure Seed) :
    Measure (Seed × input.OtherStages i) :=
  (input.seededWorldLaw ν).map (input.externalStageView i)

instance externalStageLaw_probability (input : StatisticalInput I) (i : I.Stage) (ν : Measure Seed)
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (input.externalStageLaw i ν) :=
  (Measure.isProbabilityMeasure_map_iff (input.measurable_externalStageView i).aemeasurable).mpr inferInstance

theorem seededWorldLaw_externalStageView (input : StatisticalInput I) (i : I.Stage) (ν : Measure Seed) :
    input.externalStageLaw i ν = ν.prod (input.worldLaw.map (input.otherStagesView i)) := by
  unfold externalStageLaw StatisticalInput.seededWorldLaw
  have hmap : Prod.map (id : Seed → Seed) (input.otherStagesView i) = input.externalStageView i := rfl
  rw [← hmap]
  simpa only [Measure.map_id] using
    (Measure.map_prod_map ν input.worldLaw measurable_id (input.measurable_otherStagesView i)).symm

theorem seededWorldLaw_external_current (input : StatisticalInput I) (i : I.Stage) (ν : Measure Seed)
    [IsProbabilityMeasure ν] :
    (input.seededWorldLaw ν).map (fun sample => (input.externalStageView i sample, sample.2 i)) =
      (input.externalStageLaw i ν).prod (input.stageLaw i) := by
  have hp := input.measurable_otherStagesView i
  have hn : Measurable (fun world : input.World => world i) := measurable_pi_apply i
  have hworld : input.worldLaw.map (fun world => (input.otherStagesView i world, world i)) =
      (input.worldLaw.map (input.otherStagesView i)).prod (input.stageLaw i) := by
    rw [(input.otherStagesView_independent_current i).map_prod_eq_prod_map_map
      hp.aemeasurable hn.aemeasurable, input.worldLaw_coordinate]
  have hseeded : (input.seededWorldLaw ν).map
      (fun sample => (sample.1, (input.otherStagesView i sample.2, sample.2 i))) =
      ν.prod ((input.worldLaw.map (input.otherStagesView i)).prod (input.stageLaw i)) := by
    calc
      _ = ν.prod (input.worldLaw.map (fun world => (input.otherStagesView i world, world i))) := by
        have hmap : Prod.map (id : Seed → Seed)
            (fun world : input.World => (input.otherStagesView i world, world i)) =
            (fun sample : Seed × input.World => (sample.1, (input.otherStagesView i sample.2, sample.2 i))) := rfl
        unfold seededWorldLaw
        rw [← hmap]
        simpa only [Measure.map_id] using
          (Measure.map_prod_map ν input.worldLaw measurable_id (hp.prodMk hn)).symm
      _ = _ := by rw [hworld]
  rw [input.seededWorldLaw_externalStageView]
  apply (MeasurableEquiv.prodAssoc :
    (Seed × input.OtherStages i) × input.StageSample i ≃ᵐ
      Seed × input.OtherStages i × input.StageSample i).map_measurableEquiv_injective
  have hpair : Measurable (fun sample : Seed × input.World => (input.externalStageView i sample, sample.2 i)) :=
    (input.measurable_externalStageView i).prodMk (hn.comp measurable_snd)
  rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable hpair, Measure.prodAssoc_prod]
  exact hseeded

theorem lintegral_external_current (input : StatisticalInput I) (i : I.Stage)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (f : (Seed × input.OtherStages i) × input.StageSample i → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ sample, f (input.externalStageView i sample, sample.2 i) ∂input.seededWorldLaw ν) =
      ∑ x : Bool, (input.experiment i).priorMass x *
        ∫⁻ sample, f (sample.1, (x, sample.2))
          ∂((input.experiment i).conditionalLaw (input.externalStageLaw i ν) x) := by
  have hpair : Measurable (fun sample : Seed × input.World => (input.externalStageView i sample, sample.2 i)) :=
    (input.measurable_externalStageView i).prodMk ((measurable_pi_apply i).comp measurable_snd)
  rw [← lintegral_map hf hpair, input.seededWorldLaw_external_current]
  have hlocal (x : Bool) :
      (input.externalStageLaw i ν).prod ((Measure.dirac x).prod ((input.experiment i).tapeLaw x)) =
        (((input.experiment i).conditionalLaw (input.externalStageLaw i ν) x).map
          (fun sample : (Seed × input.OtherStages i) × (input.experiment i).Tape =>
            (sample.1, (x, sample.2)))) := by
    rw [Measure.dirac_prod]
    have hg : Measurable (fun tape : (input.experiment i).Tape => (x, tape)) :=
      measurable_const.prodMk measurable_id
    have h := Measure.map_prod_map (input.externalStageLaw i ν) ((input.experiment i).tapeLaw x) measurable_id hg
    have hmap : Prod.map (id : (Seed × input.OtherStages i) → (Seed × input.OtherStages i))
        (fun tape : (input.experiment i).Tape => (x, tape)) =
        (fun sample : (Seed × input.OtherStages i) × (input.experiment i).Tape => (sample.1, (x, sample.2))) := rfl
    rw [Measure.map_id, hmap] at h
    exact h
  rw [stageLaw, Measure.prod_add, Measure.prod_smul_right, Measure.prod_smul_right,
    lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  simp only [hlocal, lintegral_map hf (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)),
    Fintype.sum_bool, smul_eq_mul]

end Seed

end PaperProofs.Common.StatisticalInput

namespace PaperProofs.Star.Parameters

open Common Common.Native Statistics

universe u

abbrev OtherWorld (P : Star.Parameters) (order : Order) (i : (starInstance P.tools order).Stage) :=
  (P.input order).OtherStages i

def spliceWorld (P : Star.Parameters) (order : Order) (i : (starInstance P.tools order).Stage)
    (other : P.OtherWorld order i) (truth : Bool) (tape : P.channel.experiment.Tape) : (P.input order).World :=
  fun j => if h : j = i then (truth, tape) else other ⟨j, h⟩

theorem spliceWorld_current (P : Star.Parameters) (order : Order) (i : (starInstance P.tools order).Stage)
    (other : P.OtherWorld order i) (truth : Bool) (tape : P.channel.experiment.Tape) :
    P.spliceWorld order i other truth tape i = (truth, tape) := by
  simp [spliceWorld]
  rfl

theorem spliceWorld_other (P : Star.Parameters) (order : Order) (i : (starInstance P.tools order).Stage)
    (other : P.OtherWorld order i) (truth : Bool) (tape : P.channel.experiment.Tape)
    (j : {j : (starInstance P.tools order).Stage // j ≠ i}) :
    P.spliceWorld order i other truth tape j.val = other j := by
  simp [spliceWorld, j.property]

theorem cut_splice_replay (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (hlate : C.reporting = .late)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type u}
    (rule : PolicyRule (starInstance P.tools order) Seed)
    (hlegal : LegalRule (P.input order) C .native accounting rule)
    (seed : Seed) (i : (starInstance P.tools order).Stage) (other : P.OtherWorld order i)
    (x x' : Bool) (tape tape' : P.channel.experiment.Tape)
    (htape : ∀ k, k < (historyObservations (preReportPublicHistory (P.input order) C accounting rule
      (seed, P.spliceWorld order i other x tape)) i).length → tape' k = tape k) :
    preReportPublicHistory (P.input order) C accounting rule (seed, P.spliceWorld order i other x' tape') =
      preReportPublicHistory (P.input order) C accounting rule (seed, P.spliceWorld order i other x tape) := by
  have hworld : replayWorld (P.input order)
      ((P.input order).truthAt (P.spliceWorld order i other x' tape'))
      (worldTapes (P.input order) (P.spliceWorld order i other x' tape')) =
      P.spliceWorld order i other x' tape' := rfl
  rw [← hworld]
  apply preReportPublicHistory_replay (P.input order) C hlate accounting rule hlegal
    (seed, P.spliceWorld order i other x tape)
  intro j k hk
  by_cases hji : j = i
  · subst j
    simpa only [worldTapes, StatisticalInput.reviewAt, spliceWorld_current, input] using htape k hk
  · simp only [worldTapes, StatisticalInput.reviewAt, spliceWorld, hji, ↓reduceDIte]

noncomputable def nativeStageStop (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    {Seed : Type u} (rule : PolicyRule (starInstance P.tools order) Seed)
    (i : (starInstance P.tools order).Stage) (outer : Seed × P.OtherWorld order i)
    (tape : P.channel.experiment.Tape) : ℕ∞ :=
  (historyObservations (preReportPublicHistory (P.input order) C accounting rule
    (outer.1, P.spliceWorld order i outer.2 false tape)) i).length

theorem nativeStageStop_eq_of_prefix (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (hlate : C.reporting = .late)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type u}
    (rule : PolicyRule (starInstance P.tools order) Seed)
    (hlegal : LegalRule (P.input order) C .native accounting rule)
    (i : (starInstance P.tools order).Stage) (outer : Seed × P.OtherWorld order i)
    (tape tape' : P.channel.experiment.Tape) (n : ℕ)
    (hprefix : ∀ k < n, tape k = tape' k) (hn : P.nativeStageStop order C accounting rule i outer tape ≤ n) :
    P.nativeStageStop order C accounting rule i outer tape' = P.nativeStageStop order C accounting rule i outer tape := by
  unfold nativeStageStop at hn ⊢
  congr 3
  apply P.cut_splice_replay order C hlate accounting rule hlegal
  intro k hk
  exact (hprefix k (lt_of_lt_of_le hk (ENat.natCast_le_natCast.mp hn))).symm

theorem preReportWord_eq_tapePrefix (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    {Seed : Type u} (rule : PolicyRule (starInstance P.tools order) Seed)
    (hlegal : LegalRule (P.input order) C .native accounting rule)
    (sample : Seed × (P.input order).World) (i : (starInstance P.tools order).Stage) :
    P.preReportWord order (preReportPublicHistory (P.input order) C accounting rule sample) i =
      ⟨(historyObservations (preReportPublicHistory (P.input order) C accounting rule sample) i).length,
        fun k => worldTapes (P.input order) sample.2 i k.val⟩ := by
  have hv : P.ValidCutHistory order (preReportPublicHistory (P.input order) C accounting rule sample) :=
    preReportPublicHistory_observation_alphabet (P.input order) C accounting rule hlegal sample
  rw [P.preReportWord_eq_validWord order _ hv i]
  unfold historyObservationWord
  congr 1
  funext k
  apply Fin.ext
  exact (preReportPublicHistory_mem_publicWordCylinder (P.input order) C accounting rule hlegal sample i k.val k.isLt).symm

theorem measurable_spliceWorld (P : Star.Parameters) (order : Order) (i : (starInstance P.tools order).Stage) :
    Measurable (fun data : P.OtherWorld order i × (Bool × P.channel.experiment.Tape) =>
      P.spliceWorld order i data.1 data.2.1 data.2.2) := by
  apply measurable_pi_iff.mpr
  intro j
  dsimp only [StatisticalInput.StageSample, input]
  change Measurable (fun data : P.OtherWorld order i × (Bool × P.channel.experiment.Tape) =>
    if h : j = i then (data.2.1, data.2.2) else data.1 ⟨j, h⟩)
  by_cases hji : j = i
  · simpa only [hji, ↓reduceDIte] using
      (measurable_snd.fst.prodMk measurable_snd.snd : Measurable
        (fun data : P.OtherWorld order i × (Bool × P.channel.experiment.Tape) => (data.2.1, data.2.2)))
  · simp only [hji, ↓reduceDIte]
    fun_prop

section Measurable

variable {Seed : Type u} [MeasurableSpace Seed]

theorem measurable_stageSample (P : Star.Parameters) (order : Order) (i : (starInstance P.tools order).Stage)
    (x : Bool) : Measurable
      (fun sample : (Seed × P.OtherWorld order i) × P.channel.experiment.Tape =>
        (sample.1.1, P.spliceWorld order i sample.1.2 x sample.2)) :=
  measurable_fst.fst.prodMk ((P.measurable_spliceWorld order i).comp
    (measurable_fst.snd.prodMk (measurable_const.prodMk measurable_snd)))

def reassembleStage (P : Star.Parameters) (order : Order) (i : (starInstance P.tools order).Stage)
    (data : (Seed × P.OtherWorld order i) × (P.input order).StageSample i) : Seed × (P.input order).World :=
  (data.1.1, P.spliceWorld order i data.1.2 data.2.1 data.2.2)

theorem measurable_reassembleStage (P : Star.Parameters) (order : Order) (i : (starInstance P.tools order).Stage) :
    Measurable (P.reassembleStage (Seed := Seed) order i) :=
  measurable_fst.fst.prodMk ((P.measurable_spliceWorld order i).comp
    (measurable_fst.snd.prodMk measurable_snd))

omit [MeasurableSpace Seed] in
theorem reassembleStage_external_current (P : Star.Parameters) (order : Order)
    (i : (starInstance P.tools order).Stage) (sample : Seed × (P.input order).World) :
    P.reassembleStage order i ((P.input order).externalStageView i sample, sample.2 i) = sample := by
  unfold reassembleStage StatisticalInput.externalStageView
  refine Prod.ext (by rfl) ?_
  funext j
  change P.spliceWorld order i ((P.input order).otherStagesView i sample.2) (sample.2 i).1 (sample.2 i).2 j = sample.2 j
  by_cases hji : j = i
  · subst j
    simp only [spliceWorld, ↓reduceDIte]
  · simp only [spliceWorld, hji, ↓reduceDIte, StatisticalInput.otherStagesView]

theorem lintegral_world_stage (P : Star.Parameters) (order : Order)
    (i : (starInstance P.tools order).Stage) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (g : Seed × (P.input order).World → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ sample, g sample ∂(P.input order).seededWorldLaw ν) =
      ∑ x : Bool, P.channel.experiment.priorMass x *
        ∫⁻ sample, g (sample.1.1, P.spliceWorld order i sample.1.2 x sample.2)
          ∂(P.channel.experiment.conditionalLaw ((P.input order).externalStageLaw i ν) x) := by
  have h := (P.input order).lintegral_external_current i ν
    (fun data => g (P.reassembleStage order i data)) (hg.comp (P.measurable_reassembleStage order i))
  simp only [P.reassembleStage_external_current] at h
  exact h

noncomputable def nativeStageTest (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (hlate : C.reporting = .late)
    (accounting : NormalAccounting (starInstance P.tools order))
    (rule : PolicyRule (starInstance P.tools order) Seed) (hm : MeasurableRule rule)
    (hlegal : LegalRule (P.input order) C .native accounting rule)
    (i : (starInstance P.tools order).Stage) : P.channel.experiment.AdmissibleRule (Seed × P.OtherWorld order i) where
  rule := {
    stop := P.nativeStageStop order C accounting rule i
    -- Only a local stopped-word container: information does not use this decision.
    -- The original Native policy's arbitrary, possibly non-MAP writes are preserved.
    decision := fun _ _ => false
    stopping := by
      intro outer tape tape' n hprefix
      constructor
      · intro hn
        rw [P.nativeStageStop_eq_of_prefix order C hlate accounting rule hlegal i outer tape tape' n hprefix hn]
        exact hn
      · intro hn
        rw [P.nativeStageStop_eq_of_prefix order C hlate accounting rule hlegal i outer tape' tape n
          (fun k hk => (hprefix k hk).symm) hn]
        exact hn
    stoppedDecision := by intro seed tape tape' n hn hn' hp; rfl }
  measurable_stop :=
    ((measurable_of_countable (fun history : List (VisibleEvent (starInstance P.tools order)) =>
      ((historyObservations history i).length : ℕ∞))).comp
      (measurable_preReportPublicHistory (P.input order) C accounting rule hm)).comp
        (P.measurable_stageSample order i false)
  measurable_decision := measurable_const

theorem nativeStageTest_stop_le (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (hlate : C.reporting = .late)
    (accounting : NormalAccounting (starInstance P.tools order))
    (rule : PolicyRule (starInstance P.tools order) Seed) (hm : MeasurableRule rule)
    (hlegal : LegalRule (P.input order) C .native accounting rule)
    (i : (starInstance P.tools order).Stage) (outer : Seed × P.OtherWorld order i) (tape : P.channel.experiment.Tape) :
    (P.nativeStageTest order C hlate accounting rule hm hlegal i).rule.stop outer tape ≤ C.reviewQuota i := by
  change ((historyObservations (preReportPublicHistory (P.input order) C accounting rule
    (outer.1, P.spliceWorld order i outer.2 false tape)) i).length : ℕ∞) ≤ _
  exact_mod_cast preReport_observations_length_le (P.input order) C hlate accounting rule hlegal
    (outer.1, P.spliceWorld order i outer.2 false tape) i

theorem nativeStageTest_finiteET (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (hlate : C.reporting = .late)
    (accounting : NormalAccounting (starInstance P.tools order))
    (rule : PolicyRule (starInstance P.tools order) Seed) (hm : MeasurableRule rule)
    (hlegal : LegalRule (P.input order) C .native accounting rule)
    (i : (starInstance P.tools order).Stage) (ν : Measure (Seed × P.OtherWorld order i))
    [IsProbabilityMeasure ν] (x : Bool) :
    P.channel.experiment.expectedSamples ν (P.nativeStageTest order C hlate accounting rule hm hlegal i) x ≠ ⊤ := by
  have hbound : P.channel.experiment.expectedSamples ν (P.nativeStageTest order C hlate accounting rule hm hlegal i) x ≤
      (C.reviewQuota i : ℝ≥0∞) := by
    unfold BinaryExperiment.expectedSamples
    calc
      _ ≤ ∫⁻ _sample, (C.reviewQuota i : ℝ≥0∞) ∂(P.channel.experiment.conditionalLaw ν x) := by
        apply lintegral_mono
        intro sample
        have hstop := P.nativeStageTest_stop_le order C hlate accounting rule hm hlegal i sample.1 sample.2
        have hfinite : (P.nativeStageTest order C hlate accounting rule hm hlegal i).rule.stop sample.1 sample.2 ≠ ⊤ :=
          ne_top_of_le_ne_top (ENat.natCast_ne_top _) hstop
        simp only [BinaryExperiment.sampleCountENNReal, hfinite, ↓reduceIte]
        exact_mod_cast ENat.toNat_le_toNat hstop (ENat.natCast_ne_top _)
      _ = _ := by simp
  exact ne_top_of_le_ne_top (by simp) hbound

theorem nativeStageTest_word_eq (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (hlate : C.reporting = .late)
    (accounting : NormalAccounting (starInstance P.tools order))
    (rule : PolicyRule (starInstance P.tools order) Seed) (hm : MeasurableRule rule)
    (hlegal : LegalRule (P.input order) C .native accounting rule)
    (i : (starInstance P.tools order).Stage) (outer : Seed × P.OtherWorld order i)
    (x : Bool) (tape : P.channel.experiment.Tape) :
    (P.channel.experiment.stoppedTranscript (P.nativeStageTest order C hlate accounting rule hm hlegal i) (outer, tape)).2 =
      P.preReportWord order (preReportPublicHistory (P.input order) C accounting rule
        (outer.1, P.spliceWorld order i outer.2 x tape)) i := by
  have hcut := P.cut_splice_replay order C hlate accounting rule hlegal outer.1 i outer.2 false x tape tape
    (by intros; rfl)
  rw [hcut, P.preReportWord_eq_tapePrefix order C accounting rule hlegal]
  simp only [BinaryExperiment.stoppedTranscript, nativeStageTest, nativeStageStop, ENat.toNat_natCast]
  congr 1
  funext k
  rw [worldTapes, StatisticalInput.reviewAt, P.spliceWorld_current]

theorem nativeStageTest_stop_eq_cut (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (hlate : C.reporting = .late)
    (accounting : NormalAccounting (starInstance P.tools order))
    (rule : PolicyRule (starInstance P.tools order) Seed) (hm : MeasurableRule rule)
    (hlegal : LegalRule (P.input order) C .native accounting rule)
    (i : (starInstance P.tools order).Stage) (outer : Seed × P.OtherWorld order i)
    (x : Bool) (tape : P.channel.experiment.Tape) :
    (P.nativeStageTest order C hlate accounting rule hm hlegal i).rule.stop outer tape =
      ((historyObservations (preReportPublicHistory (P.input order) C accounting rule
        (outer.1, P.spliceWorld order i outer.2 x tape)) i).length : ℕ∞) := by
  have hcut := P.cut_splice_replay order C hlate accounting rule hlegal outer.1 i outer.2 false x tape tape
    (by intros; rfl)
  rw [hcut]
  rfl

theorem nativeStageTest_information_eq_cut (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (hlate : C.reporting = .late)
    (accounting : NormalAccounting (starInstance P.tools order))
    (rule : PolicyRule (starInstance P.tools order) Seed) (hm : MeasurableRule rule)
    (hlegal : LegalRule (P.input order) C .native accounting rule)
    (i : (starInstance P.tools order).Stage) (outer : Seed × P.OtherWorld order i)
    (x : Bool) (tape : P.channel.experiment.Tape) :
    P.channel.stoppedPosteriorInformation (P.nativeStageTest order C hlate accounting rule hm hlegal i) (outer, tape) =
      BinarySymmetric.phi (P.preReportMAPError order
        (preReportPublicHistory (P.input order) C accounting rule (outer.1, P.spliceWorld order i outer.2 x tape)) i) := by
  have hs : (P.nativeStageTest order C hlate accounting rule hm hlegal i).rule.stop outer tape ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) (P.nativeStageTest_stop_le order C hlate accounting rule hm hlegal i outer tape)
  rw [P.channel.stoppedPosteriorInformation_of_finite _ _ hs,
    P.nativeStageTest_word_eq order C hlate accounting rule hm hlegal i outer x tape]
  rfl

theorem measurable_nativeStageCharge (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (rule : PolicyRule (starInstance P.tools order) Seed) (hm : MeasurableRule rule)
    (i : (starInstance P.tools order).Stage) :
    Measurable (fun sample : Seed × (P.input order).World => P.channel.experiment.observationCharge
      ((historyObservations (preReportPublicHistory (P.input order) C accounting rule sample) i).length : ℕ∞)) :=
  (measurable_of_countable (fun history : List (VisibleEvent (starInstance P.tools order)) =>
    P.channel.experiment.observationCharge ((historyObservations history i).length : ℕ∞))).comp
      (measurable_preReportPublicHistory (P.input order) C accounting rule hm)

theorem measurable_nativeStageInformation (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (rule : PolicyRule (starInstance P.tools order) Seed) (hm : MeasurableRule rule)
    (i : (starInstance P.tools order).Stage) :
    Measurable (fun sample : Seed × (P.input order).World => BinarySymmetric.phi
      (P.preReportMAPError order (preReportPublicHistory (P.input order) C accounting rule sample) i)) :=
  (measurable_of_countable (fun history => BinarySymmetric.phi (P.preReportMAPError order history i))).comp
    (measurable_preReportPublicHistory (P.input order) C accounting rule hm)

theorem nativeStage_information (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (hlate : C.reporting = .late)
    (accounting : NormalAccounting (starInstance P.tools order))
    (rule : PolicyRule (starInstance P.tools order) Seed) (hm : MeasurableRule rule)
    (hlegal : LegalRule (P.input order) C .native accounting rule)
    (i : (starInstance P.tools order).Stage) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (∫⁻ sample, P.channel.experiment.observationCharge
      ((historyObservations (preReportPublicHistory (P.input order) C accounting rule sample) i).length : ℕ∞)
      ∂(P.input order).seededWorldLaw ν) =
        ENNReal.ofReal P.channel.a * ∫⁻ sample, BinarySymmetric.phi
          (P.preReportMAPError order (preReportPublicHistory (P.input order) C accounting rule sample) i)
          ∂(P.input order).seededWorldLaw ν := by
  let test := P.nativeStageTest order C hlate accounting rule hm hlegal i
  let outerLaw := (P.input order).externalStageLaw i ν
  have hobs : (∫⁻ sample, P.channel.experiment.observationCharge
      ((historyObservations (preReportPublicHistory (P.input order) C accounting rule sample) i).length : ℕ∞)
      ∂(P.input order).seededWorldLaw ν) = P.channel.experiment.bayesObservationCharge outerLaw test := by
    rw [P.lintegral_world_stage order i ν _ (P.measurable_nativeStageCharge order C accounting rule hm i)]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    apply lintegral_congr
    intro sample
    rw [← P.nativeStageTest_stop_eq_cut order C hlate accounting rule hm hlegal i sample.1 x sample.2]
  have hinfo : (∫⁻ sample, BinarySymmetric.phi
      (P.preReportMAPError order (preReportPublicHistory (P.input order) C accounting rule sample) i)
      ∂(P.input order).seededWorldLaw ν) = P.channel.expectedPosteriorInformation outerLaw test := by
    rw [P.lintegral_world_stage order i ν _ (P.measurable_nativeStageInformation order C accounting rule hm i)]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    apply lintegral_congr
    intro sample
    exact (P.nativeStageTest_information_eq_cut order C hlate accounting rule hm hlegal i sample.1 x sample.2).symm
  rw [hobs, hinfo]
  exact P.channel.bayesObservationCharge_eq_posteriorInformation outerLaw test
    (fun x => P.nativeStageTest_finiteET order C hlate accounting rule hm hlegal i outerLaw x)

omit [MeasurableSpace Seed] in
theorem runObservationBill_eq_stageCharges (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (hlate : C.reporting = .late)
    (accounting : NormalAccounting (starInstance P.tools order))
    (rule : PolicyRule (starInstance P.tools order) Seed)
    (hlegal : LegalRule (P.input order) C .native accounting rule)
    (sample : Seed × (P.input order).World) :
    runObservationBill (P.input order) C .native accounting rule sample =
      ∑ i, P.channel.experiment.observationCharge
        ((historyObservations (preReportPublicHistory (P.input order) C accounting rule sample) i).length : ℕ∞) := by
  rw [runObservationBill_of_halted (P.input order) C .native accounting rule sample _
    (run_halted_nativeActionBound_succ (P.input order) C accounting rule hlegal sample)]
  unfold Ledger.observationBill
  apply Finset.sum_congr rfl
  intro i _
  rw [← preReport_observations_length (P.input order) C hlate accounting rule hlegal sample i]
  simp only [P.observationFee_eq, BinaryExperiment.observationCharge_nat]
  rfl

theorem native_late_observation_information (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (hlate : C.reporting = .late)
    (accounting : NormalAccounting (starInstance P.tools order))
    (rule : PolicyRule (starInstance P.tools order) Seed) (hm : MeasurableRule rule)
    (hlegal : LegalRule (P.input order) C .native accounting rule)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    expectedObservationBill (P.input order) C .native accounting rule ν =
      ENNReal.ofReal P.channel.a * ∫⁻ record,
        ∑ i, BinarySymmetric.phi (P.preReportMAPError order record.2 i)
        ∂preReportLaw (P.input order) C accounting rule ν := by
  have hrecord : Measurable (fun record : Seed × List (VisibleEvent (starInstance P.tools order)) =>
      ∑ i, BinarySymmetric.phi (P.preReportMAPError order record.2 i)) :=
    (measurable_of_countable (fun history => ∑ i, BinarySymmetric.phi (P.preReportMAPError order history i))).comp measurable_snd
  calc
    _ = ∫⁻ sample, ∑ i, P.channel.experiment.observationCharge
        ((historyObservations (preReportPublicHistory (P.input order) C accounting rule sample) i).length : ℕ∞)
        ∂(P.input order).seededWorldLaw ν := by
      unfold expectedObservationBill
      apply lintegral_congr
      intro sample
      exact P.runObservationBill_eq_stageCharges order C hlate accounting rule hlegal sample
    _ = ∑ i, ∫⁻ sample, P.channel.experiment.observationCharge
        ((historyObservations (preReportPublicHistory (P.input order) C accounting rule sample) i).length : ℕ∞)
        ∂(P.input order).seededWorldLaw ν :=
      lintegral_finsetSum _ (fun i _ => P.measurable_nativeStageCharge order C accounting rule hm i)
    _ = ∑ i, ENNReal.ofReal P.channel.a * ∫⁻ sample, BinarySymmetric.phi
        (P.preReportMAPError order (preReportPublicHistory (P.input order) C accounting rule sample) i)
        ∂(P.input order).seededWorldLaw ν := by
      apply Finset.sum_congr rfl
      intro i _
      exact P.nativeStage_information order C hlate accounting rule hm hlegal i ν
    _ = ENNReal.ofReal P.channel.a * (∑ i, ∫⁻ sample, BinarySymmetric.phi
        (P.preReportMAPError order (preReportPublicHistory (P.input order) C accounting rule sample) i)
        ∂(P.input order).seededWorldLaw ν) := by rw [Finset.mul_sum]
    _ = ENNReal.ofReal P.channel.a * ∫⁻ sample, ∑ i, BinarySymmetric.phi
        (P.preReportMAPError order (preReportPublicHistory (P.input order) C accounting rule sample) i)
        ∂(P.input order).seededWorldLaw ν := by
      rw [lintegral_finsetSum _ (fun i _ => P.measurable_nativeStageInformation order C accounting rule hm i)]
    _ = _ := by
      congr 1
      rw [preReportLaw, lintegral_map hrecord (measurable_preReportRecord (P.input order) C accounting rule hm)]
      rfl

end Measurable

theorem nativeLateObservationInformation (P : Star.Parameters) : P.NativeLateObservationInformation.{u} := by
  intro order C hlate accounting Seed m ν hν policy
  exact P.native_late_observation_information order C hlate.1 accounting policy.rule
    policy.measurable_rule policy.legal ν

end PaperProofs.Star.Parameters
