module

public import PaperProofs.Paid.PDROC_OverlayLaw_003
public import PaperProofs.Paid.PDROC_OverlaySimulator_021
public import PaperProofs.Paid.PDROC_OverlaySimulator_023
public import PaperProofs.Paid.PDROC_TerminalLaw_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

theorem measurable_overlayShadowCompletedHistory (P : Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) :
    Measurable (P.shadowCompletedHistory fee hfee C accounting (overlayRule P fee hfee source)
      (overlayData P source).toRecordSimulatorData) := by
  let build := fun pair : OverlaySeed P Seed × EntryHistory P.sharedInstance =>
    pair.2.map (overlayShadow P source pair.1)
  have hb : Measurable build := by
    apply measurable_from_prod_countable_left
    intro entry
    cases entry with
    | none => exact measurable_const
    | some history =>
      change Measurable (fun seed : OverlaySeed P Seed => some (overlayShadow P source seed history))
      have hs := (measurable_overlayShadow P source hm).comp
        (measurable_id.prodMk (measurable_const (a := history)))
      change Measurable (fun seed : OverlaySeed P Seed => overlayShadow P source seed history) at hs
      exact (measurable_of_countable (some : List (VisibleEvent P.sharedInstance) → EntryHistory P.sharedInstance)).comp hs
  change Measurable (fun sample : OverlaySeed P Seed × (P.input fee hfee).World =>
    build (sample.1, completedHistory (P.input fee hfee) C.val .uncapped accounting
      (overlayRule P fee hfee source) sample))
  exact hb.comp (measurable_fst.prodMk (measurable_completedHistory (P.input fee hfee) C.val .uncapped accounting
    (overlayRule P fee hfee source) (measurable_overlayRule P fee hfee source hm)))

/-- Full original old-seed × completed-history law from finite terminal
cursor restrictions for the concrete overlay. Return and cursor support
are discharged independently of SourceHistoryLaw, avoiding a circular use
of expected-bill or risk conclusions. -/
theorem overlaySourceHistoryLaw_of_cursor_restrictions (P : Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hfinite : expectedBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hcursor : ∀ cursor : Fin (P.sharedInstance.stageCount + 1),
      (((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map (fun sample =>
        (sample.1.1, P.shadowCompletedHistory fee hfee C accounting (overlayRule P fee hfee source.rule)
          (overlayData P source.rule).toRecordSimulatorData sample))).restrict
            (completedCursorCell P.sharedInstance Seed cursor.val) =
      (((P.input 0 (by norm_num)).seededWorldLaw ν).map (fun sample =>
        (sample.1, completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule sample))).restrict
          (completedCursorCell P.sharedInstance Seed cursor.val)) :
    P.SourceHistoryLaw 0 (by norm_num) fee hfee C accounting ν (overlaySeedLaw P fee hfee ν) source.rule
      (overlayRule P fee hfee source.rule) (overlayData P source.rule).toRecordSimulatorData := by
  let input := P.input fee hfee
  let sourceInput := P.input 0 (by norm_num)
  let actual := overlayPolicy P fee hfee C accounting source
  let data := overlayData P source.rule
  let actualJoint := fun sample : OverlaySeed P Seed × input.World =>
    (sample.1.1, P.shadowCompletedHistory fee hfee C accounting actual.rule data.toRecordSimulatorData sample)
  let sourceJoint := fun sample : Seed × sourceInput.World =>
    (sample.1, completedHistory sourceInput C.val .uncapped accounting source.rule sample)
  have hma : Measurable actualJoint := (measurable_fst.comp measurable_fst).prodMk
    (measurable_overlayShadowCompletedHistory P fee hfee C accounting source.rule source.measurable_rule)
  have hms : Measurable sourceJoint := measurable_fst.prodMk
    (measurable_completedHistory sourceInput C.val .uncapped accounting source.rule source.measurable_rule)
  let supported := fun pair : Seed × EntryHistory P.sharedInstance =>
    ∃ history, pair.2 = some history ∧ historyCursor history ≤ P.sharedInstance.stageCount
  have hsupport : MeasurableSet {pair | supported pair} :=
    measurable_snd (MeasurableSpace.measurableSet_top
      (s := {entry : EntryHistory P.sharedInstance | ∃ history, entry = some history ∧ historyCursor history ≤ P.sharedInstance.stageCount}))
  have hsnone := paid_finiteExpectedBill_completedHistory P 0 (by norm_num) C.val .uncapped accounting source ν hfinite
  have hanone := overlay_completedHistory_none_zero P fee hfee C accounting source (overlaySeedLaw P fee hfee ν)
  have hsreturns : ∀ᵐ sample ∂sourceInput.seededWorldLaw ν,
      completedHistory sourceInput C.val .uncapped accounting source.rule sample ≠ none := by
    apply ae_iff.mpr
    simpa only [not_not] using hsnone
  have hareturns : ∀ᵐ sample ∂input.seededWorldLaw (overlaySeedLaw P fee hfee ν),
      completedHistory input C.val .uncapped accounting actual.rule sample ≠ none := by
    apply ae_iff.mpr
    simpa only [not_not] using hanone
  have hsource : ∀ᵐ pair ∂(sourceInput.seededWorldLaw ν).map sourceJoint, supported pair := by
    apply (ae_map_iff hms.aemeasurable hsupport).mpr
    filter_upwards [hsreturns] with sample hs
    obtain ⟨history, hh⟩ := Option.ne_none_iff_exists'.mp hs
    exact ⟨history, hh, completedHistory_cursor_bound sourceInput C.val .uncapped accounting source.rule source.legal sample history hh⟩
  have hactual : ∀ᵐ pair ∂(input.seededWorldLaw (overlaySeedLaw P fee hfee ν)).map actualJoint, supported pair := by
    apply (ae_map_iff hma.aemeasurable hsupport).mpr
    filter_upwards [hareturns] with sample hs
    obtain ⟨history, hh⟩ := Option.ne_none_iff_exists'.mp hs
    refine ⟨overlayShadow P source.rule sample.1 history, ?_, ?_⟩
    · change (completedHistory input C.val .uncapped accounting actual.rule sample).map
        (overlayShadow P source.rule sample.1) = some (overlayShadow P source.rule sample.1 history)
      rw [hh]
      rfl
    · have hprojection := (overlayReplay_historyProjection (overlaySeedDraw P source.rule)
        (overlaySeedMark P) (overlaySeedGhost P source.rule) sample.1 history).1
      rw [show historyCursor (overlayShadow P source.rule sample.1 history) = historyCursor history from hprojection.symm]
      exact completedHistory_cursor_bound input C.val .uncapped accounting actual.rule actual.legal sample history hh
  refine ⟨measurable_overlayShadowCompletedHistory P fee hfee C accounting source.rule source.measurable_rule,
    overlaySeedLaw_source P fee hfee ν, ?_⟩
  exact completedJointLaw_eq_of_cursor_restrictions _ _ hactual hsource hcursor

end PDROC
