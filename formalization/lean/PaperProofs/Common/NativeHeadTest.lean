module

public import PaperProofs.Common.HistorySuffixBridge
public import PaperProofs.Common.AvailablePartial
import Lean.Elab.Tactic.Omega

/-!
B08 lower-bound extraction component. The local rule replays exactly the
native policy's first-stage all-review histories. Its first non-review action
is a stopping event; actual legal writes retain their original (possibly
non-MAP) bit, while stop/abandon/nonreturn can be completed by a fixed guess.
No local-test performance or Bellman equation is assumed.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

open PaperProofs.Statistics

variable {I : Instance} {Seed : Type*}

def headReviewHistory (input : StatisticalInput I) (stage : I.Stage)
    (tape : (input.experiment stage).Tape) (n : ℕ) : List (VisibleEvent I) :=
  List.ofFn (fun k : Fin n => .observation stage (tape k.val).val)

theorem headReviewHistory_prefix (input : StatisticalInput I) (stage : I.Stage)
    (left right : (input.experiment stage).Tape) (n : ℕ)
    (hp : ∀ k < n, left k = right k) :
    headReviewHistory input stage left n = headReviewHistory input stage right n := by
  unfold headReviewHistory
  congr 1
  funext k
  rw [hp k.val k.isLt]

theorem headReviewHistory_succ (input : StatisticalInput I) (stage : I.Stage)
    (tape : (input.experiment stage).Tape) (n : ℕ) :
    headReviewHistory input stage tape (n + 1) =
      headReviewHistory input stage tape n ++ [.observation stage (tape n).val] := by
  simp only [headReviewHistory, List.ofFn_succ_last, Fin.val_castSucc, Fin.val_last]

theorem measurable_headReviewHistory (input : StatisticalInput I) (stage : I.Stage) (n : ℕ) :
    Measurable (fun tape : (input.experiment stage).Tape => headReviewHistory input stage tape n) := by
  let letters : (input.experiment stage).Tape → (Fin n → Fin (input.experiment stage).alphabetSize) :=
    fun tape k => tape k.val
  have hm : Measurable letters := measurable_pi_iff.mpr (fun k => measurable_pi_apply k.val)
  exact (measurable_of_countable (fun word : Fin n → Fin (input.experiment stage).alphabetSize =>
    List.ofFn (fun k => (VisibleEvent.observation stage (word k).val)))).comp hm

noncomputable def headExitStop (input : StatisticalInput I) (stage : I.Stage)
    (rule : PolicyRule I Seed) (seed : Seed) (tape : (input.experiment stage).Tape) : ℕ∞ :=
  sInf {t | ∃ n : ℕ, t = n ∧ rule seed (headReviewHistory input stage tape n) ≠ .review stage}

theorem headExitStop_le_iff (input : StatisticalInput I) (stage : I.Stage)
    (rule : PolicyRule I Seed) (seed : Seed) (tape : (input.experiment stage).Tape) (n : ℕ) :
    headExitStop input stage rule seed tape ≤ n ↔
      ∃ k ≤ n, rule seed (headReviewHistory input stage tape k) ≠ .review stage := by
  classical
  let hits : Set ℕ∞ := {t | ∃ k : ℕ, t = k ∧ rule seed (headReviewHistory input stage tape k) ≠ .review stage}
  change sInf hits ≤ (n : ℕ∞) ↔ _
  constructor
  · intro hs
    have hnonempty : hits.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty.mp h, sInf_empty] at hs
      exact ENat.top_ne_natCast n (top_le_iff.mp hs).symm
    obtain ⟨k, hk, hh⟩ := csInf_mem hnonempty
    refine ⟨k, ?_, hh⟩
    rw [hk] at hs
    exact ENat.natCast_le_natCast.mp hs
  · rintro ⟨k, hkn, hh⟩
    exact (sInf_le (show (k : ℕ∞) ∈ hits from ⟨k, rfl, hh⟩)).trans (by exact_mod_cast hkn)

theorem headExitStop_stopping (input : StatisticalInput I) (stage : I.Stage)
    (rule : PolicyRule I Seed) :
    (input.experiment stage).IsStoppingRule (headExitStop input stage rule) := by
  intro seed tape tape' n hp
  rw [headExitStop_le_iff, headExitStop_le_iff]
  constructor <;> rintro ⟨k, hk, he⟩ <;> refine ⟨k, hk, ?_⟩
  · rwa [← headReviewHistory_prefix input stage tape tape' k (fun j hj => hp j (hj.trans_le hk))]
  · rwa [headReviewHistory_prefix input stage tape tape' k (fun j hj => hp j (hj.trans_le hk))]

def actionWriteBit : Action I → Bool
  | .write _ bit => bit
  | _ => false

noncomputable def headExitDecision (input : StatisticalInput I) (stage : I.Stage)
    (rule : PolicyRule I Seed) (seed : Seed) (tape : (input.experiment stage).Tape) : Bool :=
  actionWriteBit (rule seed (headReviewHistory input stage tape (headExitStop input stage rule seed tape).toNat))

section Measurable

variable [MeasurableSpace Seed]

theorem measurable_headExitStop (input : StatisticalInput I) (stage : I.Stage)
    (rule : PolicyRule I Seed) (hm : MeasurableRule rule) :
    Measurable (fun sample : Seed × (input.experiment stage).Tape => headExitStop input stage rule sample.1 sample.2) := by
  apply ENat.measurable_iff.mpr
  have hsets (n : ℕ) : MeasurableSet {sample : Seed × (input.experiment stage).Tape | headExitStop input stage rule sample.1 sample.2 ≤ n} := by
    have heq : {sample : Seed × (input.experiment stage).Tape | headExitStop input stage rule sample.1 sample.2 ≤ n} =
        ⋃ k : Fin (n + 1), {sample | rule sample.1 (headReviewHistory input stage sample.2 k.val) ≠ .review stage} := by
      ext sample
      simp only [Set.mem_ofPred_eq, headExitStop_le_iff, Set.mem_iUnion]
      constructor
      · rintro ⟨k, hk, hh⟩
        exact ⟨⟨k, Nat.lt_succ_iff.mpr hk⟩, hh⟩
      · rintro ⟨k, hh⟩
        exact ⟨k.val, Nat.lt_succ_iff.mp k.isLt, hh⟩
    rw [heq]
    apply MeasurableSet.iUnion
    intro k
    have hma : Measurable (fun sample : Seed × (input.experiment stage).Tape =>
        rule sample.1 (headReviewHistory input stage sample.2 k.val)) := hm.comp
      (measurable_fst.prodMk ((measurable_headReviewHistory input stage k.val).comp measurable_snd))
    exact (hma (measurableSet_singleton (Action.review stage))).compl
  intro n
  cases n with
  | zero =>
    have heq : (fun sample : Seed × (input.experiment stage).Tape => headExitStop input stage rule sample.1 sample.2) ⁻¹' {(0 : ℕ∞)} =
        {sample | headExitStop input stage rule sample.1 sample.2 ≤ 0} := by
      ext sample
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, nonpos_iff_eq_zero]
    simpa only [Nat.cast_zero, heq] using hsets 0
  | succ n =>
    have heq : (fun sample : Seed × (input.experiment stage).Tape => headExitStop input stage rule sample.1 sample.2) ⁻¹' {(n + 1 : ℕ∞)} =
        {sample | headExitStop input stage rule sample.1 sample.2 ≤ n + 1} \
          {sample | headExitStop input stage rule sample.1 sample.2 ≤ n} := by
      ext sample
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
      constructor
      · intro h
        rw [h]
        exact ⟨le_rfl, not_le.mpr (by exact_mod_cast Nat.lt_succ_self n)⟩
      · rintro ⟨hle, hnot⟩
        apply le_antisymm hle
        exact ENat.natCast_add_one_le_iff.mpr (lt_of_not_ge hnot)
    simp only [Nat.cast_add, Nat.cast_one]
    rw [heq]
    exact (hsets (n + 1)).diff (hsets n)

noncomputable def nativeHeadTest (input : StatisticalInput I) (stage : I.Stage)
    (rule : PolicyRule I Seed) (hm : MeasurableRule rule) : (input.experiment stage).AdmissibleRule Seed where
  rule := {
    stop := headExitStop input stage rule
    decision := headExitDecision input stage rule
    stopping := headExitStop_stopping input stage rule
    stoppedDecision := by
      intro seed tape tape' n hs hs' hp
      simp only [headExitDecision, hs, hs', ENat.toNat_natCast]
      rw [headReviewHistory_prefix input stage tape tape' n hp]
  }
  measurable_stop := measurable_headExitStop input stage rule hm
  measurable_decision := by
    have hn : Measurable (fun sample : Seed × (input.experiment stage).Tape =>
        (headExitStop input stage rule sample.1 sample.2).toNat) :=
      (measurable_of_countable ENat.toNat).comp (measurable_headExitStop input stage rule hm)
    have hh : Measurable (fun pair : (input.experiment stage).Tape × ℕ => headReviewHistory input stage pair.1 pair.2) :=
      measurable_from_prod_countable_left (fun n => measurable_headReviewHistory input stage n)
    exact (measurable_of_countable actionWriteBit).comp (hm.comp
      (measurable_fst.prodMk (hh.comp (measurable_snd.prodMk hn))))

end Measurable

def headReviewState (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (truth : I.Stage → Bool) (tape : (input.experiment stage).Tape) : ℕ → State I
  | 0 => initial truth
  | n + 1 =>
    let s := headReviewState input accounting stage truth tape n
    record accounting s (.review stage) [.observation stage (tape n).val] (reviewLedger s stage) 0 false

theorem headReviewState_cursor (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (truth : I.Stage → Bool) (tape : (input.experiment stage).Tape) (n : ℕ) :
    (headReviewState input accounting stage truth tape n).cursor = 0 := by cases n <;> rfl

theorem headReviewState_active (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (truth : I.Stage → Bool) (tape : (input.experiment stage).Tape) (n : ℕ) :
    (headReviewState input accounting stage truth tape n).halted = false := by cases n <;> rfl

theorem headReviewState_written (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (truth : I.Stage → Bool) (tape : (input.experiment stage).Tape) (n : ℕ) :
    (headReviewState input accounting stage truth tape n).ledger.written = fun _ => none := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem headReviewState_reviews (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (truth : I.Stage → Bool) (tape : (input.experiment stage).Tape) (n : ℕ) :
    (headReviewState input accounting stage truth tape n).ledger.reviews stage = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [headReviewState, record, reviewLedger, Function.update_self, ih, Nat.cast_add, Nat.cast_one]

theorem headReviewState_history (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (truth : I.Stage → Bool) (tape : (input.experiment stage).Tape) (n : ℕ) :
    (headReviewState input accounting stage truth tape n).history = headReviewHistory input stage tape n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [headReviewState, record, ih, headReviewHistory_succ]

theorem headExitStop_prior_review (input : StatisticalInput I) (stage : I.Stage)
    (rule : PolicyRule I Seed) (seed : Seed) (tape : (input.experiment stage).Tape) (n : ℕ)
    (hbound : (n : ℕ∞) ≤ headExitStop input stage rule seed tape) :
    ∀ k < n, rule seed (headReviewHistory input stage tape k) = .review stage := by
  intro k hk
  by_contra he
  have hs := (headExitStop_le_iff input stage rule seed tape k).mpr ⟨k, le_rfl, he⟩
  have hnk := ENat.natCast_le_natCast.mp (hbound.trans hs)
  omega

/-- Every local all-review prefix is the genuine native interpreter prefix
on the original sample. No truth or unused tape is added to the private seed. -/
theorem run_eq_headReviewState (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (stage : I.Stage) (hhead : stage.val = 0)
    (sample : Seed × input.World) (n : ℕ)
    (hbound : (n : ℕ∞) ≤ headExitStop input stage rule sample.1 (worldTapes input sample.2 stage)) :
    run input C .uncapped accounting rule sample n =
      headReviewState input accounting stage (input.truthAt sample.2) (worldTapes input sample.2 stage) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hnsucc : (n : ℕ∞) ≤ (n + 1 : ℕ∞) := by exact_mod_cast Nat.le_succ n
    have hn : (n : ℕ∞) ≤ headExitStop input stage rule sample.1 (worldTapes input sample.2 stage) :=
      hnsucc.trans hbound
    have hr := ih hn
    have haction := headExitStop_prior_review input stage rule sample.1 (worldTapes input sample.2 stage) (n + 1) hbound n (Nat.lt_succ_self n)
    let s := headReviewState input accounting stage (input.truthAt sample.2) (worldTapes input sample.2 stage) n
    have ha : s.halted = false := headReviewState_active input accounting stage _ _ n
    have hl : liveStage s stage := ⟨ha, (headReviewState_cursor input accounting stage _ _ n).trans hhead.symm⟩
    have hw : s.ledger.written stage = none := congrFun (headReviewState_written input accounting stage _ _ n) stage
    have hc : s.ledger.reviews stage = n := headReviewState_reviews input accounting stage _ _ n
    have hsc : s.cursor = 0 := headReviewState_cursor input accounting stage _ _ n
    have hs : Step input C .uncapped accounting (worldTapes input sample.2) s (.review stage)
        (headReviewState input accounting stage (input.truthAt sample.2) (worldTapes input sample.2 stage) (n + 1)) := by
      have h := Step.review (input := input) (C := C) (mode := .uncapped) (accounting := accounting)
        (tapes := worldTapes input sample.2) s stage hl hw (.inl rfl)
      rw [headReviewState]
      simpa only [hc, ENat.toNat_natCast, hsc] using h
    apply run_succ_of_step input C .uncapped accounting rule sample n _
    · rw [hr]
      exact ha
    · rw [hr, headReviewState_history]
      rw [haction]
      exact hs

theorem headExitStop_hits (input : StatisticalInput I) (stage : I.Stage)
    (rule : PolicyRule I Seed) (seed : Seed) (tape : (input.experiment stage).Tape) (n : ℕ)
    (hstop : headExitStop input stage rule seed tape = n) :
    rule seed (headReviewHistory input stage tape n) ≠ .review stage := by
  obtain ⟨k, hkn, hk⟩ := (headExitStop_le_iff input stage rule seed tape n).mp (by rw [hstop])
  have hnk : n ≤ k := by
    have hh := (headExitStop_le_iff input stage rule seed tape k).mpr ⟨k, le_rfl, hk⟩
    rw [hstop] at hh
    exact ENat.natCast_le_natCast.mp hh
  have heq := Nat.le_antisymm hkn hnk
  simpa only [heq] using hk

theorem headReviewState_reportTime (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (truth : I.Stage → Bool) (tape : (input.experiment stage).Tape) (n : ℕ) :
    (headReviewState input accounting stage truth tape n).ledger.reportTime = fun _ => none := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- At the extracted finite exit, legality permits only the actual head
write, stop or abandon. In particular no other stage's review or hidden truth
response has entered the local test. -/
theorem nativeHead_exit_classification (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule)
    (stage : I.Stage) (hhead : stage.val = 0) (sample : Seed × input.World) (n : ℕ)
    (hstop : headExitStop input stage rule sample.1 (worldTapes input sample.2 stage) = n) :
    (∃ bit, rule sample.1 (headReviewHistory input stage (worldTapes input sample.2 stage) n) = .write stage bit) ∨
      rule sample.1 (headReviewHistory input stage (worldTapes input sample.2 stage) n) = .stop ∨
      rule sample.1 (headReviewHistory input stage (worldTapes input sample.2 stage) n) = .abandon := by
  have hr := run_eq_headReviewState input C accounting rule stage hhead sample n (by rw [hstop])
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting rule hlegal sample n
  have ha : (run input C .uncapped accounting rule sample n).halted = false := by rw [hr]; exact headReviewState_active input accounting stage _ _ n
  obtain ⟨next, hs⟩ := hlegal sample.1 _ _ m _ hp ha
  have hcursor : (run input C .uncapped accounting rule sample n).cursor = 0 := by rw [hr]; exact headReviewState_cursor input accounting stage _ _ n
  have hw : (run input C .uncapped accounting rule sample n).ledger.written = fun _ => none := by rw [hr]; exact headReviewState_written input accounting stage _ _ n
  have hreport : (run input C .uncapped accounting rule sample n).ledger.reportTime = fun _ => none := by rw [hr]; exact headReviewState_reportTime input accounting stage _ _ n
  have hhistory : (run input C .uncapped accounting rule sample n).history =
      headReviewHistory input stage (worldTapes input sample.2 stage) n := by rw [hr]; exact headReviewState_history input accounting stage _ _ n
  rw [hhistory] at hs
  have hnot := headExitStop_hits input stage rule sample.1 (worldTapes input sample.2 stage) n hstop
  generalize haction : rule sample.1 (headReviewHistory input stage (worldTapes input sample.2 stage) n) = action at hs hnot ⊢
  cases hs with
  | review current live port resources =>
    have he : current = stage := by apply Fin.ext; have hc := live.2; omega
    subst current
    exact (hnot rfl).elim
  | write current bit live port resources =>
    have he : current = stage := by apply Fin.ext; have hc := live.2; omega
    subst current
    exact .inl ⟨bit, rfl⟩
  | allocate handle tool active valid compatible unused unallocated window resources =>
    obtain ⟨time, ht⟩ := valid.2.2
    rw [hreport] at ht
    cases ht
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    obtain ⟨time, ht⟩ := valid.2.2
    rw [hreport] at ht
    cases ht
  | advance current live written resources => exact (written (congrFun hw current)).elim
  | stop active => exact .inr (.inl rfl)
  | abandon active => exact .inr (.inr rfl)

theorem headReviewPrefix_charge_le (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (stage : I.Stage) (hhead : stage.val = 0)
    (sample : Seed × input.World) (n : ℕ)
    (hbound : (n : ℕ∞) ≤ headExitStop input stage rule sample.1 (worldTapes input sample.2 stage)) :
    ENNReal.ofReal ((input.experiment stage).observationFee : ℝ) * n ≤
      runObservationBill input C .uncapped accounting rule sample := by
  have hr := run_eq_headReviewState input C accounting rule stage hhead sample n hbound
  have hc : (run input C .uncapped accounting rule sample n).ledger.reviews stage = n := by
    rw [hr]
    exact headReviewState_reviews input accounting stage _ _ n
  have h := Finset.single_le_sum (s := (Finset.univ : Finset I.Stage))
    (f := fun i => ENNReal.ofReal (input.fees.observation i : ℝ) *
      ((run input C .uncapped accounting rule sample n).ledger.reviews i : ℝ≥0∞))
    (fun _ _ => bot_le) (Finset.mem_univ stage)
  rw [hc] at h
  have hprefix : ENNReal.ofReal ((input.experiment stage).observationFee : ℝ) * n ≤
      (run input C .uncapped accounting rule sample n).ledger.observationBill input.fees := by
    simpa only [StatisticalInput.fees, Ledger.observationBill, ENat.toENNReal_coe] using h
  exact hprefix.trans (le_iSup (fun k => (run input C .uncapped accounting rule sample k).ledger.observationBill input.fees) n)

/-- Every extracted sample is charged by the original run. A never-exiting
review path has infinite real observation bill; finite abandon/nonreturn exits
keep their finite already-paid observations. -/
theorem nativeHead_observationCharge_le (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (stage : I.Stage) (hhead : stage.val = 0)
    (sample : Seed × input.World) :
    (input.experiment stage).observationCharge (headExitStop input stage rule sample.1 (worldTapes input sample.2 stage)) ≤
      runObservationBill input C .uncapped accounting rule sample := by
  by_cases htop : headExitStop input stage rule sample.1 (worldTapes input sample.2 stage) = ⊤
  · have hb (n : ℕ) : ENNReal.ofReal ((input.experiment stage).observationFee : ℝ) * n ≤
        runObservationBill input C .uncapped accounting rule sample :=
      headReviewPrefix_charge_le input C accounting rule stage hhead sample n (by rw [htop]; exact le_top)
    have hsup := iSup_le hb
    rw [← ENNReal.mul_iSup, ENNReal.iSup_natCast] at hsup
    have hfee : ENNReal.ofReal ((input.experiment stage).observationFee : ℝ) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (input.experiment stage).observationFee_real_pos)
    simpa only [htop, BinaryExperiment.observationCharge_top, ENNReal.mul_top hfee] using hsup
  · generalize hstop : headExitStop input stage rule sample.1 (worldTapes input sample.2 stage) = stop at htop ⊢
    lift stop to ℕ using htop with n
    rw [BinaryExperiment.observationCharge_nat]
    exact headReviewPrefix_charge_le input C accounting rule stage hhead sample n (by rw [hstop])

theorem headExitDecision_of_write (input : StatisticalInput I) (stage : I.Stage)
    (rule : PolicyRule I Seed) (seed : Seed) (tape : (input.experiment stage).Tape) (n : ℕ) (bit : Bool)
    (hstop : headExitStop input stage rule seed tape = n)
    (hwrite : rule seed (headReviewHistory input stage tape n) = .write stage bit) :
    headExitDecision input stage rule seed tape = bit := by
  simp only [headExitDecision, hstop, ENat.toNat_natCast, hwrite, actionWriteBit]

theorem headExitStop_partial_nonreturn (input : StatisticalInput I) (stage : I.Stage)
    (rule : PartialRule I Seed) (seed : Seed) (tape : (input.experiment stage).Tape) (n : ℕ)
    (hnone : rule seed (headReviewHistory input stage tape n) = none) :
    headExitStop input stage (totalizeRule rule) seed tape ≤ n := by
  apply (headExitStop_le_iff input stage (totalizeRule rule) seed tape n).mpr
  refine ⟨n, le_rfl, ?_⟩
  simp only [totalizeRule, hnone, Option.getD_none]
  intro he
  cases he

theorem nativePartialHead_observationCharge_le (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PartialRule I Seed) (stage : I.Stage) (hhead : stage.val = 0)
    (sample : Seed × input.World) :
    (input.experiment stage).observationCharge (headExitStop input stage (totalizeRule rule) sample.1 (worldTapes input sample.2 stage)) ≤
      partialRunObservationBill input C accounting rule sample := by
  rw [partialRunObservationBill_eq_totalized]
  exact nativeHead_observationCharge_le input C accounting (totalizeRule rule) stage hhead sample

section ExpectedCharge

variable [MeasurableSpace Seed]

/-- An arbitrary randomized local test uses the original stage's mixed
truth/tape law. This identity is not restricted to deterministic/MAP tests. -/
theorem bayesObservationCharge_eq_seededWorld_integral (input : StatisticalInput I) (stage : I.Stage)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (test : (input.experiment stage).AdmissibleRule Seed) :
    (input.experiment stage).bayesObservationCharge ν test =
      ∫⁻ sample, (input.experiment stage).observationCharge
        (test.rule.stop sample.1 (worldTapes input sample.2 stage)) ∂input.seededWorldLaw ν := by
  let E := input.experiment stage
  let f : Seed × E.Tape → ℝ≥0∞ := fun sample => E.observationCharge (test.rule.stop sample.1 sample.2)
  have hf : Measurable f := (measurable_of_countable E.observationCharge).comp test.measurable_stop
  let g : input.StageSample stage → ℝ≥0∞ := fun localSample => ∫⁻ seed, f (seed, localSample.2) ∂ν
  have hg : Measurable g := (hf.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).lintegral_prod_right'
  have hworld : Measurable (fun sample : Seed × input.World => f (sample.1, worldTapes input sample.2 stage)) :=
    hf.comp (measurable_fst.prodMk ((measurable_pi_apply stage).comp measurable_snd).snd)
  have hp (truth : Bool) :
      (∫⁻ localSample, g localSample ∂(Measure.dirac truth).prod (E.tapeLaw truth)) = E.expectedObservationCharge ν test truth := by
    rw [Measure.dirac_prod, lintegral_map hg measurable_prodMk_left]
    exact (lintegral_prod_symm f hf.aemeasurable).symm
  have hstage : (∫⁻ localSample, g localSample ∂input.stageLaw stage) = E.bayesObservationCharge ν test := by
    rw [StatisticalInput.stageLaw, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
    simp only [smul_eq_mul, BinaryExperiment.bayesObservationCharge, Fintype.sum_bool]
    rw [hp true, hp false]
  symm
  change (∫⁻ sample, f (sample.1, worldTapes input sample.2 stage) ∂input.seededWorldLaw ν) = _
  rw [StatisticalInput.seededWorldLaw, lintegral_prod_symm _ hworld.aemeasurable]
  change (∫⁻ world, g (world stage) ∂input.worldLaw) = _
  rw [← lintegral_map hg (measurable_pi_apply stage), input.worldLaw_coordinate]
  exact hstage

/-- The extracted local test's entire Bayes observation charge is paid by
the original all-policy native objective, including all failed paths. -/
theorem nativeHead_bayesObservationCharge_le (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hm : MeasurableRule rule)
    (stage : I.Stage) (hhead : stage.val = 0) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (input.experiment stage).bayesObservationCharge ν (nativeHeadTest input stage rule hm) ≤
      expectedObservationBill input C .uncapped accounting rule ν := by
  rw [bayesObservationCharge_eq_seededWorld_integral]
  exact lintegral_mono (nativeHead_observationCharge_le input C accounting rule stage hhead)

end ExpectedCharge

end PaperProofs.Common.Native
