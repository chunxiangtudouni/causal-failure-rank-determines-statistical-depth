module

public import PaperProofs.Paid.Survival
public import PaperProofs.Common.NativeCausality

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDLower

universe u

variable {I : Instance} {Seed : Type u}

theorem run_cursor_lt_of_halt_before (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hl : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (n : ℕ) (hh : (run input C mode accounting rule sample n).halted = true)
    (stage : I.Stage) (hb : (run input C mode accounting rule sample n).cursor < stage.val) :
    ∀ k, (run input C mode accounting rule sample k).cursor < stage.val := by
  intro k
  by_cases hk : k ≤ n
  · exact lt_of_le_of_lt (run_cursor_monotone input C mode accounting rule hl sample hk) hb
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hk))
    simpa only [run_after_halt input C mode accounting rule sample n hh] using hb

theorem nextStageFilledEntry_transport (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hl : LegalRule (P.input fee hf) C.val mode accounting rule)
    (seed : Seed) (world world' : (P.input fee hf).World) (stage : P.sharedInstance.Stage)
    (hpast : ∀ i : P.sharedInstance.Stage, i.val < stage.val → world' i = world i)
    (hs : (seed, world) ∈ P.nextStageFilledEntry fee hf C mode accounting rule stage) :
    (seed, world') ∈ P.nextStageFilledEntry fee hf C mode accounting rule stage := by
  obtain ⟨n, hh, hc, hhealthy⟩ := hs
  have hb : (run (P.input fee hf) C.val mode accounting rule (seed, world) n).cursor < stage.val := by omega
  have hall := run_cursor_lt_of_halt_before (P.input fee hf) C.val mode accounting rule hl
    (seed, world) n hh stage hb
  have heq := run_retarget_of_before (P.input fee hf) C.val mode accounting rule hl seed world world'
    stage hpast n (fun k _ => hall k)
  refine ⟨n, ?_, ?_, ?_⟩
  · simpa only [heq, retargetTruth] using hh
  · simpa only [heq, retargetTruth] using hc
  · simpa only [heq, retargetTruth] using hhealthy

theorem survivingEntry_eq_of_past (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hl : LegalRule (P.input fee hf) C.val mode accounting rule)
    (seed : Seed) (world world' : (P.input fee hf).World) (stage : P.sharedInstance.Stage)
    (hpast : ∀ i : P.sharedInstance.Stage, i.val < stage.val → world' i = world i) :
    (seed, world') ∈ P.survivingEntry fee hf C mode accounting rule stage ↔
      (seed, world) ∈ P.survivingEntry fee hf C mode accounting rule stage := by
  have he := entryHistory_eq_of_past (P.input fee hf) C.val mode accounting rule hl seed world world' stage hpast
  have actual : (seed, world') ∈ P.actualSurvivingEntry fee hf C mode accounting rule stage ↔
      (seed, world) ∈ P.actualSurvivingEntry fee hf C mode accounting rule stage := by
    simp only [Parameters.actualSurvivingEntry, Set.mem_ofPred_eq, he]
  constructor
  · rintro (ha | hn)
    · exact Or.inl (actual.mp ha)
    · exact Or.inr (nextStageFilledEntry_transport P fee hf C mode accounting rule hl seed world' world
        stage (fun i hi => (hpast i hi).symm) hn)
  · rintro (ha | hn)
    · exact Or.inl (actual.mpr ha)
    · exact Or.inr (nextStageFilledEntry_transport P fee hf C mode accounting rule hl seed world world' stage hpast hn)

theorem survivingEntry_preBirthGate (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    [MeasurableSpace Seed] (policy : Policy (P.input fee hf) C.val mode accounting Seed)
    (stage : P.sharedInstance.Stage) :
    ∃ gate : Seed × (P.input fee hf).PastWorld stage → Bool,
      Measurable gate ∧ ∀ sample,
        sample ∈ P.survivingEntry fee hf C mode accounting policy.rule stage ↔
          gate ((P.input fee hf).preBirthView stage sample) = true := by
  classical
  let complete : Seed × (P.input fee hf).PastWorld stage → Seed × (P.input fee hf).World :=
    fun v => (v.1, completePastWorld (P.input fee hf) stage v.2)
  have hm : Measurable complete :=
    measurable_fst.prodMk ((measurable_completePastWorld (P.input fee hf) stage).comp measurable_snd)
  let gate : Seed × (P.input fee hf).PastWorld stage → Bool := fun v =>
    if complete v ∈ P.survivingEntry fee hf C mode accounting policy.rule stage then true else false
  refine ⟨gate, ?_, ?_⟩
  · exact Measurable.ite
      ((P.measurableSet_survivingEntry fee hf C mode accounting policy.rule policy.measurable_rule stage).preimage hm)
      measurable_const measurable_const
  · rintro ⟨seed, world⟩
    have he := survivingEntry_eq_of_past P fee hf C mode accounting policy.rule policy.legal seed world
      (completePastWorld (P.input fee hf) stage (fun i => world i.val)) stage
      (fun i hi => completePastWorld_apply_past (P.input fee hf) stage (fun i => world i.val) i hi)
    simpa [gate, complete, StatisticalInput.preBirthView] using he.symm

theorem nextStageFilledEntry_unentered_zero_reviews (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hl : LegalRule (P.input fee hf) C.val mode accounting rule)
    (sample : Seed × (P.input fee hf).World) (stage : P.sharedInstance.Stage)
    (hs : sample ∈ P.nextStageFilledEntry fee hf C mode accounting rule stage) :
    entryHistory (P.input fee hf) C.val mode accounting rule stage sample = none ∧
      P.paidRunReviewCount fee hf C mode accounting rule sample stage = 0 := by
  obtain ⟨n, hh, hc, _⟩ := hs
  have hb : (run (P.input fee hf) C.val mode accounting rule sample n).cursor < stage.val := by omega
  have hall := run_cursor_lt_of_halt_before (P.input fee hf) C.val mode accounting rule hl sample n hh stage hb
  constructor
  · apply (entryHistory_none_iff (P.input fee hf) C.val mode accounting rule stage sample).mpr
    rintro ⟨k, hk⟩
    exact (Nat.ne_of_lt (hall k)) hk
  · apply le_antisymm ?_ bot_le
    apply iSup_le
    intro k
    exact le_of_eq ((run_cursorInvariant (P.input fee hf) C.val mode accounting rule hl sample k).future_reviews stage (hall k))

theorem survivingEntry_earlier_written (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hl : LegalRule (P.input fee hf) C.val mode accounting rule)
    (sample : Seed × (P.input fee hf).World) (stage earlier : P.sharedInstance.Stage)
    (hs : sample ∈ P.survivingEntry fee hf C mode accounting rule stage) (he : earlier.val < stage.val) :
    ∃ (n : ℕ) (bit : Bool), (run (P.input fee hf) C.val mode accounting rule sample n).ledger.written earlier = some bit := by
  have hhealthy : ∃ n, Parameters.healthyEntryHistory P.sharedInstance stage
      (run (P.input fee hf) C.val mode accounting rule sample n).history = true := by
    rcases hs with ha | hn
    · cases hh : entryHistory (P.input fee hf) C.val mode accounting rule stage sample with
      | none => simp [Parameters.actualSurvivingEntry, hh, Parameters.healthyEntryRecord] at ha
      | some history =>
        have hhhealthy : Parameters.healthyEntryHistory P.sharedInstance stage history = true := by
          simpa only [Parameters.actualSurvivingEntry, Set.mem_ofPred_eq, hh, Parameters.healthyEntryRecord] using ha
        obtain ⟨n, _, _, hh⟩ := (entryHistory_some_iff (P.input fee hf) C.val mode accounting rule stage sample history).mp hh
        exact ⟨n, hh ▸ hhhealthy⟩
    · obtain ⟨n, _, _, hh⟩ := hn
      exact ⟨n, hh⟩
  obtain ⟨n, hh⟩ := hhealthy
  have hres := (of_decide_eq_true hh) earlier he
  obtain ⟨_, _, hp⟩ := run_has_prefix (P.input fee hf) C.val mode accounting rule hl sample n
  have hw := prefix_historyWrite (P.input fee hf) C.val mode accounting rule sample.1 _ _ hp earlier
  cases hwrite : (run (P.input fee hf) C.val mode accounting rule sample n).ledger.written earlier with
  | none =>
    rw [hwrite] at hw
    simp only [Option.map_none] at hw
    simp [Parameters.historyStageResolved, hw] at hres
  | some bit => exact ⟨n, bit, hwrite⟩

theorem unwrittenSurvivingStages_card_le_one (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hl : LegalRule (P.input fee hf) C.val mode accounting rule)
    (sample : Seed × (P.input fee hf).World) :
    (P.unwrittenSurvivingStages fee hf C mode accounting rule sample).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hij | hji
  · exact hi'.2 (survivingEntry_earlier_written P fee hf C mode accounting rule hl sample j i hj'.1 hij)
  · exact hj'.2 (survivingEntry_earlier_written P fee hf C mode accounting rule hl sample i j hi'.1 hji)

end PDLower
