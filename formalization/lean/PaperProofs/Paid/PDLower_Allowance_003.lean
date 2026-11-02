module

public import PaperProofs.Paid.PDLower_Allowance_002
public import Mathlib.Algebra.Order.Floor.Extended

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDLower

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

local instance : MeasurableSpace (Option Bool) := ⊤
local instance : MeasurableSingletonClass (Option Bool) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

theorem measurable_actualOrdinaryDecision (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule) (stage : P.sharedInstance.Stage) :
    Measurable (fun sample => P.actualOrdinaryDecision fee hf C mode accounting rule sample stage) := by
  classical
  have hset (bit : Bool) : MeasurableSet {sample : Seed × (P.input fee hf).World |
      ∃ n, (run (P.input fee hf) C.val mode accounting rule sample n).ledger.written stage = some bit} := by
    have heq : {sample : Seed × (P.input fee hf).World |
        ∃ n, (run (P.input fee hf) C.val mode accounting rule sample n).ledger.written stage = some bit} =
        ⋃ n : ℕ, {sample : Seed × (P.input fee hf).World |
          (run (P.input fee hf) C.val mode accounting rule sample n).ledger.written stage = some bit} := by
      ext sample
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    rw [heq]
    apply MeasurableSet.iUnion
    intro n
    exact (measurable_run (P.input fee hf) C.val mode accounting rule hm n)
      (MeasurableSpace.measurableSet_top (s := {s : State P.sharedInstance | s.ledger.written stage = some bit}))
  exact Measurable.ite (hset true) measurable_const (Measurable.ite (hset false) measurable_const measurable_const)

theorem measurable_paidRunReviewCount (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule) (stage : P.sharedInstance.Stage) :
    Measurable (fun sample => P.paidRunReviewCount fee hf C mode accounting rule sample stage) := by
  have hc : Measurable (fun sample =>
      (P.paidRunReviewCount fee hf C mode accounting rule sample stage : ℝ≥0∞)) := by
    simp only [Parameters.paidRunReviewCount, ENat.toENNReal_iSup]
    apply Measurable.iSup
    intro n
    exact (measurable_of_countable (fun s : State P.sharedInstance => (s.ledger.reviews stage : ℝ≥0∞))).comp
      (measurable_run (P.input fee hf) C.val mode accounting rule hm n)
  apply measurable_to_countable'
  intro count
  have hs := hc (measurableSet_singleton (count : ℝ≥0∞))
  convert hs using 1
  ext sample
  exact ENat.toENNReal_inj.symm

theorem measurable_filledOrdinaryDecision (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule) (stage : P.sharedInstance.Stage) :
    Measurable (fun sample => P.filledOrdinaryDecision fee hf C mode accounting rule sample stage) := by
  classical
  have hword : Measurable (fun pair : ℕ∞ × P.experiment.Tape =>
      (⟨pair.1.toNat, fun k => pair.2 k.val⟩ : P.experiment.StoppedWord)) := by
    apply measurable_from_prod_countable_right
    intro count
    have hv : Measurable (fun tape : P.experiment.Tape => fun k : Fin count.toNat => tape k.val) :=
      measurable_pi_iff.mpr (fun k => measurable_pi_apply k.val)
    exact (measurable_of_countable (fun word : Fin count.toNat → Fin P.experiment.alphabetSize =>
      (⟨count.toNat, word⟩ : P.experiment.StoppedWord))).comp hv
  have hmap : Measurable (fun sample : Seed × (P.input fee hf).World =>
      P.experiment.posteriorRecordDecision
        ((), (⟨(P.paidRunReviewCount fee hf C mode accounting rule sample stage).toNat,
          fun k => (sample.2 stage).2 k.val⟩ : P.experiment.StoppedWord))) :=
    (measurable_of_countable (fun word : P.experiment.StoppedWord =>
      P.experiment.posteriorRecordDecision ((), word))).comp
      (hword.comp ((measurable_paidRunReviewCount P fee hf C mode accounting rule hm stage).prodMk
        ((measurable_pi_apply stage).comp measurable_snd).snd))
  have hcount := measurable_paidRunReviewCount P fee hf C mode accounting rule hm stage
  have hfilled : Measurable (fun sample : Seed × (P.input fee hf).World =>
      if P.paidRunReviewCount fee hf C mode accounting rule sample stage = ⊤ then false else
        P.experiment.posteriorRecordDecision
          ((), ⟨(P.paidRunReviewCount fee hf C mode accounting rule sample stage).toNat,
            fun k => (sample.2 stage).2 k.val⟩)) :=
    measurable_const.ite ((measurableSet_singleton (⊤ : ℕ∞)).preimage hcount) hmap
  have hdecision := measurable_actualOrdinaryDecision P fee hf C mode accounting rule hm stage
  have hchoose : Measurable (fun pair : Option Bool × Bool => pair.1.getD pair.2) := measurable_of_countable _
  convert hchoose.comp (hdecision.prodMk hfilled) using 1
  funext sample
  cases hdec : P.actualOrdinaryDecision fee hf C mode accounting rule sample stage <;>
    simp only [Function.comp_apply, Parameters.filledOrdinaryDecision, hdec, Option.getD_none, Option.getD_some]

theorem measurableSet_markedErrorEvent (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule) (stage : P.sharedInstance.Stage) :
    MeasurableSet (P.markedErrorEvent fee hf C mode accounting rule stage) :=
  (P.measurableSet_survivingEntry fee hf C mode accounting rule hm stage).inter
    (measurableSet_eq_fun (measurable_filledOrdinaryDecision P fee hf C mode accounting rule hm stage)
      (((measurable_pi_apply stage).comp measurable_snd).fst)).compl

theorem markedError_expected_allowance (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (policy : Policy (P.input fee hf) C.val mode accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hrisk : risk (P.input fee hf) C.val mode accounting policy.rule ν ≤ P.targetRisk) :
    (∑ stage : P.sharedInstance.Stage, (P.input fee hf).seededWorldLaw ν
      (P.markedErrorEvent fee hf C mode accounting policy.rule stage)) ≤
      expectedRepairCount (P.input fee hf) C.val mode accounting policy.rule ν + P.targetRisk := by
  let μ := (P.input fee hf).seededWorldLaw ν
  have hset (stage : P.sharedInstance.Stage) := measurableSet_markedErrorEvent P fee hf C mode accounting
    policy.rule policy.measurable_rule stage
  have hsum : (∑ stage : P.sharedInstance.Stage, μ (P.markedErrorEvent fee hf C mode accounting policy.rule stage)) =
      ∫⁻ sample, (∑ stage : P.sharedInstance.Stage, (P.markedErrorEvent fee hf C mode accounting policy.rule stage).indicator
        (fun _ => (1 : ℝ≥0∞)) sample) ∂μ := by
    rw [lintegral_finsetSum _ (fun stage _ => measurable_const.indicator (hset stage))]
    apply Finset.sum_congr rfl
    intro stage _
    simp only [lintegral_indicator_const (hset stage), one_mul]
  rw [hsum]
  calc
    _ ≤ ∫⁻ sample, runRepairCount (P.input fee hf) C.val mode accounting policy.rule sample +
        {sample | ¬ runSuccess (P.input fee hf) C.val mode accounting policy.rule sample}.indicator
          (fun _ => (1 : ℝ≥0∞)) sample ∂μ :=
      lintegral_mono (markedError_pathwise_allowance P fee hf C mode accounting policy)
    _ = expectedRepairCount (P.input fee hf) C.val mode accounting policy.rule ν +
        risk (P.input fee hf) C.val mode accounting policy.rule ν := by
      have hfail : {sample | ¬ runSuccess (P.input fee hf) C.val mode accounting policy.rule sample} =
          {sample | runSuccess (P.input fee hf) C.val mode accounting policy.rule sample}ᶜ := rfl
      rw [lintegral_add_left (measurable_runRepairCount (P.input fee hf) C.val mode accounting policy.rule policy.measurable_rule), hfail,
        lintegral_indicator_const (measurableSet_runSuccess (P.input fee hf) C.val mode accounting policy.rule policy.measurable_rule).compl]
      rw [one_mul]
      rfl
    _ ≤ _ := add_le_add le_rfl hrisk

theorem markedFailureAllowance (P : Parameters) : P.MarkedFailureAllowance.{u} := by
  intro fee hf C mode accounting Seed m
  let : MeasurableSpace Seed := m
  intro ν hν
  let : IsProbabilityMeasure ν := hν
  intro policy
  exact ⟨markedError_pathwise_allowance P fee hf C mode accounting policy,
    markedError_expected_allowance P fee hf C mode accounting policy ν⟩

end PDLower
