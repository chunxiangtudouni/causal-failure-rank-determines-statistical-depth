module

public import PaperProofs.Paid.PDLower_Survival_001
public import PaperProofs.Paid.PDROC_FirstFailure_002
public import PaperProofs.Paid.PDROC_TruthfulContinuation_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDLower

universe u
variable {I : Instance} {Seed : Type u}

theorem entry_exists_of_success (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hl : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (stage : I.Stage) (hs : runSuccess input C mode accounting rule sample) :
    ∃ history, entryHistory input C mode accounting rule stage sample = some history := by
  classical
  obtain ⟨n, _, hsucc⟩ := hs
  have hbound : stage.val ≤ (run input C mode accounting rule sample n).cursor := by
    by_contra hnot
    have hw := (run_cursorInvariant input C mode accounting rule hl sample n).future_written stage
      (Nat.lt_of_not_ge hnot)
    rcases hsucc.2.2.2 stage with hcorrect | ⟨e, he, hstage⟩
    · rw [hw] at hcorrect
      cases hcorrect
    · have hg := (run_ledgerWellFormed input C mode accounting rule hl sample n).genuine e he
      rw [hstage, hw] at hg
      cases hg.1
  have hex : ∃ n, stage.val ≤ (run input C mode accounting rule sample n).cursor := ⟨n, hbound⟩
  have heq : (run input C mode accounting rule sample (Nat.find hex)).cursor = stage.val := by
    have hle := Nat.find_spec hex
    cases hn : Nat.find hex with
    | zero =>
      have hz : stage.val ≤ 0 := by simpa only [hn, run, initial] using hle
      simpa only [run, initial] using (Nat.eq_zero_of_le_zero hz).symm
    | succ k =>
      have hprev := Nat.find_min hex (show k < Nat.find hex by omega)
      have hstep := (run_cursor_step_bounds input C mode accounting rule hl sample k).2
      rw [hn] at hle
      omega
  cases he : entryHistory input C mode accounting rule stage sample with
  | some history => exact ⟨history, rfl⟩
  | none => exact ((entryHistory_none_iff input C mode accounting rule stage sample).mp he ⟨_, heq⟩).elim

theorem not_permanentlyFailed_of_runSuccess [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : Policy input C mode accounting Seed)
    (sample : Seed × input.World) (n : ℕ) (hs : runSuccess input C mode accounting policy.rule sample) :
    ¬ PermanentlyFailed input C accounting sample.2 (run input C mode accounting policy.rule sample n) := by
  obtain ⟨last, hhalt, hsuccess⟩ := hs
  intro hfailed
  by_cases hn : n ≤ last
  · obtain ⟨extra, he⟩ := Nat.exists_eq_add_of_le hn
    apply hfailed
    refine ⟨run input C mode accounting policy.rule sample last, ?_, hhalt, hsuccess⟩
    have hr := PDROC.run_reachable input C accounting (PDROC.uncappedSourcePolicy input C mode accounting policy).rule
      (PDROC.uncappedSourcePolicy input C mode accounting policy).legal sample n extra
    simpa only [PDROC.uncappedSourcePolicy_run, ← he] using hr
  · obtain ⟨extra, he⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hn))
    have heq : run input C mode accounting policy.rule sample n =
        run input C mode accounting policy.rule sample last := by
      rw [he, run_after_halt input C mode accounting policy.rule sample last hhalt]
    apply hfailed
    refine ⟨run input C mode accounting policy.rule sample n, .refl, ?_, ?_⟩
    · simpa only [heq] using hhalt
    · simpa only [heq] using hsuccess

theorem healthyEntryHistory_of_success_prefix (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    [MeasurableSpace Seed] (policy : Policy (P.input fee hf) C.val mode accounting Seed)
    (sample : Seed × (P.input fee hf).World) (n : ℕ) (stage : P.sharedInstance.Stage)
    (hc : (run (P.input fee hf) C.val mode accounting policy.rule sample n).cursor = stage.val)
    (hs : runSuccess (P.input fee hf) C.val mode accounting policy.rule sample) :
    Parameters.healthyEntryHistory P.sharedInstance stage
      (run (P.input fee hf) C.val mode accounting policy.rule sample n).history = true := by
  classical
  apply decide_eq_true
  intro earlier hearlier
  obtain ⟨_, _, hp⟩ := run_has_prefix (P.input fee hf) C.val mode accounting policy.rule policy.legal sample n
  let s := run (P.input fee hf) C.val mode accounting policy.rule sample n
  have hwritten : s.ledger.written earlier ≠ none :=
    PDROC.prefix_pastPortsWritten (P.input fee hf) C.val mode accounting policy.rule sample.1 _ _ hp earlier
      (hc ▸ hearlier)
  have hnopast : ¬ PDROC.PastUnrepairedError s earlier := by
    intro herror
    exact not_permanentlyFailed_of_runSuccess (P.input fee hf) C.val mode accounting policy sample n hs
      (PDROC.pastUnrepairedError_permanentlyFailed (P.input fee hf) C.val C.property.2 accounting sample.2 herror)
  have hcorrect : s.ledger.written earlier = some (s.ledger.truth earlier) ∨
      ∃ e ∈ s.ledger.executions, e.handle.stage = earlier := by
    by_cases hex : ∃ e ∈ s.ledger.executions, e.handle.stage = earlier
    · exact Or.inr hex
    left
    cases hb : s.ledger.written earlier with
    | none => exact (hwritten hb).elim
    | some bit =>
      have hbcorrect : bit = s.ledger.truth earlier := by
        by_contra hwrong
        have hnot : bit = !s.ledger.truth earlier := Bool.eq_not_iff.mpr hwrong
        exact hnopast ⟨hc ▸ hearlier, hb.trans (congrArg some hnot), fun e he hstage => hex ⟨e, he, hstage⟩⟩
      exact congrArg some hbcorrect
  obtain ⟨bit, hbit'⟩ := Option.ne_none_iff_exists.mp hwritten
  have hbit := hbit'.symm
  obtain ⟨time, htime⟩ := prefix_early_written_reported (P.input fee hf) C.val C.property.1.1 mode accounting
    policy.rule sample.1 _ _ hp earlier hwritten
  have hw := prefix_historyWrite (P.input fee hf) C.val mode accounting policy.rule sample.1 _ _ hp earlier
  have hr := prefix_historyReport_early (P.input fee hf) C.val C.property.1.1 mode accounting policy.rule sample.1 _ _ hp earlier
  have hx := prefix_historyExecutions (P.input fee hf) C.val mode accounting policy.rule sample.1 _ _ hp
  change s.ledger.written earlier = some bit at hbit
  change s.ledger.reportTime earlier = some time at htime
  change historyWrite s.history earlier = _ at hw
  change historyReport s.history earlier = _ at hr
  change historyExecutions s.history = _ at hx
  rw [hbit] at hw
  rw [htime] at hr
  change Parameters.historyStageResolved P.sharedInstance s.history earlier = true
  simp only [Parameters.historyStageResolved, hw, hr, Option.map_some, beq_self_eq_true, Bool.true_and]
  change (bit == s.ledger.truth earlier || (historyExecutions s.history).any (fun execution =>
    execution.1.stage == earlier && execution.1.writeSerial == s.ledger.writeSerial earlier)) = true
  rcases hcorrect with hbitcorrect | ⟨e, he, hstage⟩
  · have heq : bit = s.ledger.truth earlier := Option.some.inj (hbit.symm.trans hbitcorrect)
    simp [heq]
  · rw [Bool.or_eq_true_eq_eq_true_or_eq_true]
    right
    rw [hx, List.any_map, List.any_eq_true]
    refine ⟨e, he, ?_⟩
    have hgen := (prefix_invariant (P.input fee hf) C.val mode accounting policy.rule sample.1 _ _ hp).wellFormed.genuine e he
    simp only [Function.comp_apply, hstage, beq_self_eq_true, Bool.true_and]
    exact beq_iff_eq.mpr (by simpa only [hstage] using hgen.2)

theorem success_mem_survivingEntry (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    [MeasurableSpace Seed] (policy : Policy (P.input fee hf) C.val mode accounting Seed)
    (sample : Seed × (P.input fee hf).World) (stage : P.sharedInstance.Stage)
    (hs : runSuccess (P.input fee hf) C.val mode accounting policy.rule sample) :
    sample ∈ P.survivingEntry fee hf C mode accounting policy.rule stage := by
  obtain ⟨history, hentry⟩ := entry_exists_of_success (P.input fee hf) C.val mode accounting policy.rule policy.legal sample stage hs
  obtain ⟨n, hn, _, hhistory⟩ := (entryHistory_some_iff (P.input fee hf) C.val mode accounting policy.rule stage sample history).mp hentry
  apply Or.inl
  simp only [Parameters.actualSurvivingEntry, Set.mem_ofPred_eq, hentry, Parameters.healthyEntryRecord]
  rw [← hhistory]
  exact healthyEntryHistory_of_success_prefix P fee hf C mode accounting policy sample n stage hn hs

theorem survivingEntry_mass_lower (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (policy : Policy (P.input fee hf) C.val mode accounting Seed)
    (hrisk : risk (P.input fee hf) C.val mode accounting policy.rule ν ≤ P.targetRisk)
    (stage : P.sharedInstance.Stage) :
    1 - P.targetRisk ≤ (P.input fee hf).seededWorldLaw ν
      (P.survivingEntry fee hf C mode accounting policy.rule stage) := by
  have hsucc := measurableSet_runSuccess (P.input fee hf) C.val mode accounting policy.rule policy.measurable_rule
  have hbound : (P.input fee hf).seededWorldLaw ν
      {sample | runSuccess (P.input fee hf) C.val mode accounting policy.rule sample} ≤
      (P.input fee hf).seededWorldLaw ν (P.survivingEntry fee hf C mode accounting policy.rule stage) :=
    measure_mono (fun sample hs => success_mem_survivingEntry P fee hf C mode accounting policy sample stage hs)
  have hcomp := measure_compl (μ := (P.input fee hf).seededWorldLaw ν) hsucc
  have hr : risk (P.input fee hf) C.val mode accounting policy.rule ν =
      1 - (P.input fee hf).seededWorldLaw ν {sample | runSuccess (P.input fee hf) C.val mode accounting policy.rule sample} := by
    change (P.input fee hf).seededWorldLaw ν
      {sample | runSuccess (P.input fee hf) C.val mode accounting policy.rule sample}ᶜ = _
    simpa only [measure_univ] using hcomp (measure_ne_top _ _)
  rw [hr] at hrisk
  exact (tsub_le_iff_right.mpr ((tsub_le_iff_right.mp hrisk).trans_eq (add_comm _ _))).trans hbound

theorem survivingEntryClaims (P : Parameters) : P.SurvivingEntryClaims.{u} := by
  intro fee hf C mode accounting Seed m
  let : MeasurableSpace Seed := m
  intro ν hν
  let : IsProbabilityMeasure ν := hν
  intro policy
  exact ⟨fun stage => survivingEntry_preBirthGate P fee hf C mode accounting policy stage,
    fun sample stage hs => nextStageFilledEntry_unentered_zero_reviews P fee hf C mode accounting policy.rule policy.legal sample stage hs,
    fun sample => unwrittenSurvivingStages_card_le_one P fee hf C mode accounting policy.rule policy.legal sample,
    fun hr stage => survivingEntry_mass_lower P fee hf C mode accounting ν policy hr stage⟩

end PDLower
