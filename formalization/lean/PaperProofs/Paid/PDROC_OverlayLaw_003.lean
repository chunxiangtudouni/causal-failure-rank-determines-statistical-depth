module

public import PaperProofs.Paid.PDROC_OverlayLaw_002
public import PaperProofs.Paid.PDROC_SimulatorLaw_016

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

theorem overlaySeedLaw_source (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (ν : Measure Seed) : (overlaySeedLaw P fee hfee ν).map Prod.fst = ν := by
  unfold overlaySeedLaw overlayFreshSeedLaw
  rw [Measure.map_fst_prod, measure_univ, one_smul]

theorem overlaySeededWorldLaw_sourceSeed (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map (fun sample => sample.1.1) = ν := by
  calc
    _ = (((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map Prod.fst).map Prod.fst :=
      (Measure.map_map measurable_fst measurable_fst).symm
    _ = ν := by rw [StatisticalInput.seededWorldLaw_seed, overlaySeedLaw_source]

theorem overlayVirtualEntryGate_stageZero_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) (hzero : stage.val = 0) :
    ((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
      (overlayVirtualEntryGate P fee hfee C accounting source.rule stage) =
        sourceEventualEntrySeedLaw P 0 (by norm_num) C accounting source ν stage := by
  let tag := fun seed : Seed => (seed, (some [] : EntryHistory P.sharedInstance))
  have ht : Measurable tag := measurable_id.prodMk measurable_const
  have ha : overlayVirtualEntryGate P fee hfee C accounting source.rule stage =
      tag ∘ (fun sample : OverlaySeed P Seed × (P.input fee hfee).World => sample.1.1) := by
    funext sample
    change (sample.1.1, (entryHistory (P.input fee hfee) C.val .uncapped accounting
      (overlayRule P fee hfee source.rule) stage sample).map (overlayShadow P source.rule sample.1)) = _
    rw [entryHistory_stageZero (P.input fee hfee) C.val .uncapped accounting
      (overlayRule P fee hfee source.rule) stage hzero sample]
    rfl
  have hs : entryHistorySeedRecord (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule stage =
      tag ∘ Prod.fst := by
    funext sample
    change (sample.1, entryHistory (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule stage sample) = _
    rw [entryHistory_stageZero (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule stage hzero sample]
    rfl
  have hm : Measurable (fun sample : OverlaySeed P Seed × (P.input fee hfee).World => sample.1.1) :=
    measurable_fst.comp measurable_fst
  rw [ha, ← Measure.map_map ht hm, overlaySeededWorldLaw_sourceSeed]
  unfold sourceEventualEntrySeedLaw
  rw [hs, ← Measure.map_map ht measurable_fst, StatisticalInput.seededWorldLaw_seed]

/-- The complete stage kernel supplies the next entry law once its actual
pathwise projection has been identified. This is the measure-composition
step used by finite-stage induction, with no conditional normalization. -/
theorem overlayVirtualEntryGate_next_law_of_flow (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage next : P.sharedInstance.Stage)
    (hnext : next.val = stage.val + 1)
    (hfinite : expectedBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hentry : ((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
      (overlayVirtualEntryGate P fee hfee C accounting source.rule stage) =
        sourceEventualEntrySeedLaw P 0 (by norm_num) C accounting source ν stage)
    (hflow : ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν),
      overlayVirtualEntryGate P fee hfee C accounting source.rule next sample =
        simulatorNextEntryOptionalProjection next
          (overlayEventualStageExit P fee hfee C accounting source.rule stage sample)) :
    ((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
      (overlayVirtualEntryGate P fee hfee C accounting source.rule next) =
        sourceEventualEntrySeedLaw P 0 (by norm_num) C accounting source ν next := by
  have hp := measurable_simulatorNextEntryOptionalProjection (Seed := Seed) next
  have hsource := sourceEventualStageExitSome_nextEntry_ae P 0 (by norm_num) C accounting source ν stage next hnext hfinite
  calc
    _ = ((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
        (fun sample => simulatorNextEntryOptionalProjection next
          (overlayEventualStageExit P fee hfee C accounting source.rule stage sample)) := Measure.map_congr hflow
    _ = (((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
        (overlayEventualStageExit P fee hfee C accounting source.rule stage)).map
          (simulatorNextEntryOptionalProjection next) :=
      (Measure.map_map hp (measurable_overlayEventualStageExit P fee hfee C accounting source.rule source.measurable_rule stage)).symm
    _ = (((P.input 0 (by norm_num)).seededWorldLaw ν).map
        (sourceEventualStageExitSome P 0 (by norm_num) C accounting source stage)).map
          (simulatorNextEntryOptionalProjection next) := by
      rw [overlayEventualStageExit_law_of_entryLaw P fee hfee C accounting source ν stage hfinite hentry]
    _ = ((P.input 0 (by norm_num)).seededWorldLaw ν).map
        (fun sample => simulatorNextEntryOptionalProjection next
          (sourceEventualStageExitSome P 0 (by norm_num) C accounting source stage sample)) :=
      Measure.map_map hp (measurable_sourceEventualStageExitSome P 0 (by norm_num) C accounting source stage)
    _ = ((P.input 0 (by norm_num)).seededWorldLaw ν).map
        (entryHistorySeedRecord (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule next) :=
      Measure.map_congr (hsource.mono (fun _ h => h.symm))
    _ = _ := rfl

/-- Finite-stage composition, retaining the original private seed and
every eventual full entry history, including all never-entry branches. -/
theorem overlayVirtualEntryGate_all_law_of_next_flow (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hfinite : expectedBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hflow : ∀ stage next : P.sharedInstance.Stage, next.val = stage.val + 1 →
      (((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
        (overlayVirtualEntryGate P fee hfee C accounting source.rule stage) =
          sourceEventualEntrySeedLaw P 0 (by norm_num) C accounting source ν stage) →
      ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν),
        overlayVirtualEntryGate P fee hfee C accounting source.rule next sample =
          simulatorNextEntryOptionalProjection next
            (overlayEventualStageExit P fee hfee C accounting source.rule stage sample)) :
    ∀ stage : P.sharedInstance.Stage,
      ((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
        (overlayVirtualEntryGate P fee hfee C accounting source.rule stage) =
          sourceEventualEntrySeedLaw P 0 (by norm_num) C accounting source ν stage := by
  have hnat : ∀ n : ℕ, ∀ stage : P.sharedInstance.Stage, stage.val = n →
      ((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
        (overlayVirtualEntryGate P fee hfee C accounting source.rule stage) =
          sourceEventualEntrySeedLaw P 0 (by norm_num) C accounting source ν stage := by
    intro n
    induction n with
    | zero =>
      intro stage hzero
      exact overlayVirtualEntryGate_stageZero_law P fee hfee C accounting source ν stage hzero
    | succ n ih =>
      intro next hn
      let stage : P.sharedInstance.Stage := ⟨n, by have h := next.isLt; omega⟩
      have hentry := ih stage rfl
      have hnext : next.val = stage.val + 1 := hn
      exact overlayVirtualEntryGate_next_law_of_flow P fee hfee C accounting source ν stage next hnext hfinite hentry
        (hflow stage next hnext hentry)
  intro stage
  exact hnat stage.val stage rfl

end PDROC
