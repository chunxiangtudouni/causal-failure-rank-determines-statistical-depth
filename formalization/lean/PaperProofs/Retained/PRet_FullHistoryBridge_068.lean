module

public import PaperProofs.Retained.PRet_EntryRow_067
public import PaperProofs.Common.EntryContinuationPartition

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFullHistoryBridge068

open Common Common.Native MeasureTheory PRetEntryRow067 PRetEntryPenalty066
open scoped ENNReal Function

variable {I : Instance}

universe uBridge

/-- The ORIGINAL full-history retained lower bridge: arbitrary source
normal accounting, original complete policies and seeds, exact old H,
full prebirth gates, and all failed/nonreturn path costs. -/
theorem fullHistoryPenaltyBridge (input : StatisticalInput I) : FullHistoryPenaltyBridge.{uBridge} input := by
  intro stage old _hhealthy C hC accounting mode Seed m
  let : MeasurableSpace Seed := m
  intro ν hν
  let : IsProbabilityMeasure ν := hν
  intro source A hmA hgate penalty
  classical
  let μ := input.seededWorldLaw ν
  let G := {sample : Seed × input.World | input.preBirthView stage sample ∈ A}
  let E := fun record : EntryContinuationPartition.Record I =>
    {sample : Seed × input.World | input.preBirthView stage sample ∈ A ∧
      entryStartupAt input C mode accounting source.rule stage record.1 sample = some record.2}
  have hmG : MeasurableSet G := (input.measurable_preBirthView stage) hmA
  have hmE (record : EntryContinuationPartition.Record I) : MeasurableSet (E record) := hmG.inter
    ((measurable_entryStartupAt input C mode accounting source.rule source.measurable_rule stage record.1)
      (measurableSet_singleton _))
  have hd : Pairwise (Disjoint on E) := by
    intro left right hne
    apply Set.disjoint_left.mpr
    intro sample hl hr
    apply hne
    exact EntryContinuationPartition.recordEvent_unique input C mode accounting source.rule stage Set.univ sample left right
      ⟨Set.mem_univ _, hl.2⟩ ⟨Set.mem_univ _, hr.2⟩
  have hUnion : (⋃ record : EntryContinuationPartition.Record I, E record) = G := by
    ext sample
    constructor
    · intro hs
      obtain ⟨record, hr⟩ := Set.mem_iUnion.mp hs
      exact hr.1
    · intro hs
      obtain ⟨history, hh, _⟩ := hgate sample hs
      obtain ⟨n, hc, hbefore, _⟩ := (entryHistory_some_iff input C mode accounting source.rule stage sample history).mp hh
      apply Set.mem_iUnion.mpr
      refine ⟨(n, publicStartup (run input C mode accounting source.rule sample n)), hs, ?_⟩
      exact (entryStartupAt_some_iff input C mode accounting source.rule stage n sample _).mpr ⟨⟨hc, hbefore⟩, rfl⟩
  have hmass : μ G = ∑' record : EntryContinuationPartition.Record I, μ (E record) := by
    rw [← hUnion]
    simpa only [setLIntegral_const, one_mul] using lintegral_iUnion hmE hd (fun _ => (1 : ℝ≥0∞))
  have hintegral : (∫⁻ sample in G, fullCharge input C mode accounting source.rule stage.val penalty sample ∂μ) =
      ∑' record : EntryContinuationPartition.Record I,
        ∫⁻ sample in E record, fullCharge input C mode accounting source.rule stage.val penalty sample ∂μ := by
    rw [← hUnion]
    exact lintegral_iUnion hmE hd _
  have hrow (record : EntryContinuationPartition.Record I) :
      μ (E record) * freshPenalty input stage.val old penalty ≤
        ∫⁻ sample in E record, fullCharge input C mode accounting source.rule stage.val penalty sample ∂μ := by
    apply entry_row_lower input C hC.1 mode accounting source ν stage record.1 record.2 old A hmA
    intro sample hs hrecord
    obtain ⟨history, hh, herr⟩ := hgate sample hs
    obtain ⟨hentry, _⟩ := (entryStartupAt_some_iff input C mode accounting source.rule stage record.1 sample record.2).mp hrecord
    have hh' : entryHistory input C mode accounting source.rule stage sample =
        some (run input C mode accounting source.rule sample record.1).history :=
      (entryHistory_some_iff input C mode accounting source.rule stage sample _).mpr
        ⟨record.1, hentry.1, hentry.2, rfl⟩
    have heq := Option.some.inj (hh'.symm.trans hh)
    rw [heq]
    exact herr
  have hbound : μ G * freshPenalty input stage.val old penalty ≤
      ∫⁻ sample in G, fullCharge input C mode accounting source.rule stage.val penalty sample ∂μ := by
    rw [hmass, ← ENNReal.tsum_mul_right, hintegral]
    exact ENNReal.tsum_le_tsum hrow
  have hfail : MeasurableSet {sample | ¬ runSuccess input C mode accounting source.rule sample} :=
    (measurableSet_runSuccess input C mode accounting source.rule source.measurable_rule).compl
  have hcharge : (fun sample => fullCharge input C mode accounting source.rule stage.val penalty sample) =
      fun sample => runFutureObservationBill input C mode accounting source.rule stage.val sample +
        {sample | ¬ runSuccess input C mode accounting source.rule sample}.indicator (fun _ => penalty) sample := by
    funext sample
    by_cases hs : runSuccess input C mode accounting source.rule sample <;>
      simp only [fullCharge, hs, ↓reduceIte, Set.indicator, Set.mem_ofPred_eq, not_true_eq_false,
        not_false_eq_true, add_zero]
  rw [hcharge, lintegral_add_left (measurable_futureBill input C mode accounting source.rule source.measurable_rule stage.val),
    lintegral_indicator_const hfail, Measure.restrict_apply hfail] at hbound
  have hset : {sample : Seed × input.World | ¬ runSuccess input C mode accounting source.rule sample} ∩ G =
      {sample | input.preBirthView stage sample ∈ A ∧ ¬ runSuccess input C mode accounting source.rule sample} := by
    ext sample
    exact and_comm
  rw [hset] at hbound
  change μ G * freshPenalty input stage.val old penalty ≤
    (∫⁻ sample, G.indicator (runFutureObservationBill input C mode accounting source.rule stage.val) sample ∂μ) +
      penalty * μ {sample | input.preBirthView stage sample ∈ A ∧ ¬ runSuccess input C mode accounting source.rule sample}
  rw [lintegral_indicator hmG]
  exact hbound

end PaperProofs.Retained.PRetFullHistoryBridge068


