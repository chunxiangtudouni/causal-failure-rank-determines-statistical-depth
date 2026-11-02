module

public import PaperProofs.Paid.PDROC_TerminalLaw_001
public import PaperProofs.Paid.PDROC_SimulatorReturns_001
public import PaperProofs.Paid.PDROC_Simulator_010
public import PaperProofs.Paid.PDROC_Termination_001
public import PaperProofs.Paid.PDROC_SimulatorProjection_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

theorem measurable_simulatorShadowCompletedHistory (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) :
    Measurable (P.shadowCompletedHistory fee hfee C accounting (simulatorRule P fee hfee source)
      (simulatorData P fee hfee source)) := by
  let build := fun pair : SimulatorSeed P Seed × EntryHistory P.sharedInstance =>
    pair.2.map (simulatorShadow P fee hfee source pair.1)
  have hb : Measurable build := by
    apply measurable_from_prod_countable_left
    intro entry
    cases entry with
    | none => exact measurable_const
    | some history =>
      change Measurable (fun seed : SimulatorSeed P Seed => some (simulatorShadow P fee hfee source seed history))
      have hs := (measurable_simulatorShadow P fee hfee source hm).comp
        (measurable_id.prodMk (measurable_const (a := history)))
      change Measurable (fun seed : SimulatorSeed P Seed => simulatorShadow P fee hfee source seed history) at hs
      exact (measurable_of_countable (some : List (VisibleEvent P.sharedInstance) → EntryHistory P.sharedInstance)).comp hs
  change Measurable (fun sample : SimulatorSeed P Seed × (P.input fee hfee).World =>
    build (sample.1, completedHistory (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) sample))
  exact hb.comp (measurable_fst.prodMk (measurable_completedHistory (P.input fee hfee) C.val .uncapped accounting
    (simulatorRule P fee hfee source) (measurable_simulatorRule P fee hfee source hm)))

/-- Full ORIGINAL SourceHistoryLaw follows from the terminal-cursor joint
restrictions. All measurability, old-seed marginal, and no-return mass inputs
are discharged for the concrete native policies, preserving arbitrary Seed. -/
theorem simulatorSourceHistoryLaw_of_cursor_restrictions
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hf : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hcursor : ∀ cursor : Fin (P.sharedInstance.stageCount + 1),
      (((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map (fun sample =>
        (sample.1.1, P.shadowCompletedHistory fee hfee C accounting (simulatorRule P fee hfee source.rule)
          (simulatorData P fee hfee source.rule) sample))).restrict
            (completedCursorCell P.sharedInstance Seed cursor.val) =
      (((P.input fee hfee).seededWorldLaw ν).map (fun sample =>
        (sample.1, completedHistory (P.input fee hfee) C.val .uncapped accounting source.rule sample))).restrict
          (completedCursorCell P.sharedInstance Seed cursor.val)) :
    P.SourceHistoryLaw fee hfee fee hfee C accounting ν (simulatorSeedLaw P ν) source.rule
      (simulatorRule P fee hfee source.rule) (simulatorData P fee hfee source.rule) := by
  let input := P.input fee hfee
  let actual := simulatorPolicy P fee hfee C accounting source
  let data := simulatorData P fee hfee source.rule
  let actualJoint := fun sample : SimulatorSeed P Seed × input.World =>
    (sample.1.1, P.shadowCompletedHistory fee hfee C accounting actual.rule data sample)
  let sourceJoint := fun sample : Seed × input.World =>
    (sample.1, completedHistory input C.val .uncapped accounting source.rule sample)
  have hma : Measurable actualJoint := (measurable_fst.comp measurable_fst).prodMk
    (measurable_simulatorShadowCompletedHistory P fee hfee C accounting source.rule source.measurable_rule)
  have hms : Measurable sourceJoint := measurable_fst.prodMk
    (measurable_completedHistory input C.val .uncapped accounting source.rule source.measurable_rule)
  let supported := fun pair : Seed × EntryHistory P.sharedInstance =>
    ∃ history, pair.2 = some history ∧ historyCursor history ≤ P.sharedInstance.stageCount
  have hsupport : MeasurableSet {pair | supported pair} :=
    measurable_snd (MeasurableSpace.measurableSet_top
      (s := {entry : EntryHistory P.sharedInstance | ∃ history, entry = some history ∧ historyCursor history ≤ P.sharedInstance.stageCount}))
  have hsnone := paid_finiteExpectedBill_completedHistory P fee hfee C.val .uncapped accounting source ν hf
  have hanone := simulator_completedHistory_none_zero P fee hfee C accounting source (simulatorSeedLaw P ν)
  have hsreturns : ∀ᵐ sample ∂input.seededWorldLaw ν, completedHistory input C.val .uncapped accounting source.rule sample ≠ none := by
    apply ae_iff.mpr
    simpa only [not_not] using hsnone
  have hareturns : ∀ᵐ sample ∂input.seededWorldLaw (simulatorSeedLaw P ν),
      completedHistory input C.val .uncapped accounting actual.rule sample ≠ none := by
    apply ae_iff.mpr
    simpa only [not_not] using hanone
  have hsource : ∀ᵐ pair ∂(input.seededWorldLaw ν).map sourceJoint, supported pair := by
    apply (ae_map_iff hms.aemeasurable hsupport).mpr
    filter_upwards [hsreturns] with sample hs
    obtain ⟨history, hh⟩ := Option.ne_none_iff_exists'.mp hs
    exact ⟨history, hh, completedHistory_cursor_bound input C.val .uncapped accounting source.rule source.legal sample history hh⟩
  have hactual : ∀ᵐ pair ∂(input.seededWorldLaw (simulatorSeedLaw P ν)).map actualJoint, supported pair := by
    apply (ae_map_iff hma.aemeasurable hsupport).mpr
    filter_upwards [hareturns] with sample hs
    obtain ⟨history, hh⟩ := Option.ne_none_iff_exists'.mp hs
    refine ⟨simulatorShadow P fee hfee source.rule sample.1 history, ?_, ?_⟩
    · change (completedHistory input C.val .uncapped accounting actual.rule sample).map
        (simulatorShadow P fee hfee source.rule sample.1) = some (simulatorShadow P fee hfee source.rule sample.1 history)
      rw [hh]
      rfl
    · have hprojection := (simulatorReplay_sameProjection (simulatorSeedDraw P fee hfee source.rule) sample.1 history).1
      rw [show historyCursor (simulatorShadow P fee hfee source.rule sample.1 history) = historyCursor history from hprojection.symm]
      exact completedHistory_cursor_bound input C.val .uncapped accounting actual.rule actual.legal sample history hh
  refine ⟨measurable_simulatorShadowCompletedHistory P fee hfee C accounting source.rule source.measurable_rule,
    simulatorSeedLaw_source P ν, ?_⟩
  exact completedJointLaw_eq_of_cursor_restrictions _ _ hactual hsource hcursor

end PDROC
