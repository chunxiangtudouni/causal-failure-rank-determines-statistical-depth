module

public import PaperProofs.Paid.RepresentationClaims

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u

variable {I : Instance} {Seed : Type} [MeasurableSpace Seed]

def liftPolicy (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : Policy input C mode accounting Seed) :
    Policy input C mode accounting (ULift.{u} Seed) where
  rule seed history := policy.rule seed.down history
  measurable_rule := policy.measurable_rule.comp
    ((measurable_down.comp measurable_fst).prodMk measurable_snd)
  legal := by
    intro seed truth tapes n s hp hactive
    have hp' := prefix_rule_transport input C mode accounting
      (fun seed : ULift.{u} Seed => policy.rule seed.down) policy.rule
      seed seed.down (fun _ => rfl) truth tapes hp
    exact policy.legal seed.down truth tapes n s hp' hactive

theorem run_liftPolicy (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : Policy input C mode accounting Seed)
    (sample : Seed × input.World) (n : ℕ) :
    run input C mode accounting (liftPolicy.{u} input C mode accounting policy).rule
      (ULift.up sample.1, sample.2) n = run input C mode accounting policy.rule sample n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run, ih]; rfl

theorem seededWorldLaw_lift (input : StatisticalInput I) (ν : Measure Seed) :
    input.seededWorldLaw (ν.map (ULift.up : Seed → ULift.{u} Seed)) =
      (input.seededWorldLaw ν).map (fun sample => (ULift.up sample.1, sample.2)) := by
  have h := Measure.map_prod_map ν input.worldLaw (measurable_up (α := Seed)) measurable_id
  rw [Measure.map_id] at h
  exact h

theorem expectedBill_liftPolicy (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : Policy input C mode accounting Seed) (ν : Measure Seed) :
    expectedBill input C mode accounting (liftPolicy.{u} input C mode accounting policy).rule
      (ν.map ULift.up) = expectedBill input C mode accounting policy.rule ν := by
  unfold expectedBill
  have hm : Measurable (fun sample : Seed × input.World =>
      ((ULift.up sample.1 : ULift.{u} Seed), sample.2)) :=
    (measurable_up.comp measurable_fst).prodMk measurable_snd
  rw [seededWorldLaw_lift,
    lintegral_map (measurable_runActualBill input C mode accounting _
      (liftPolicy.{u} input C mode accounting policy).measurable_rule) hm]
  apply lintegral_congr
  intro sample
  simp only [runActualBill, run_liftPolicy]

theorem risk_liftPolicy (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : Policy input C mode accounting Seed) (ν : Measure Seed) :
    risk input C mode accounting (liftPolicy.{u} input C mode accounting policy).rule
      (ν.map ULift.up) = risk input C mode accounting policy.rule ν := by
  unfold risk
  have hm : Measurable (fun sample : Seed × input.World =>
      ((ULift.up sample.1 : ULift.{u} Seed), sample.2)) :=
    (measurable_up.comp measurable_fst).prodMk measurable_snd
  have hs : MeasurableSet {sample | ¬ runSuccess input C mode accounting
      (liftPolicy.{u} input C mode accounting policy).rule sample} :=
    (measurableSet_runSuccess input C mode accounting _
      (liftPolicy.{u} input C mode accounting policy).measurable_rule).compl
  rw [seededWorldLaw_lift, Measure.map_apply hm hs]
  congr 1
  ext sample
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, runSuccess, run_liftPolicy]

variable {SourceSeed SimSeed : Type*}

def eraseRecordSource (data : RecordSimulatorData I SourceSeed SimSeed) :
    RecordSimulatorData I Unit SimSeed where
  sourceSeed := fun _ => ()
  shadow := data.shadow
  record := data.record
  endpointCoin := data.endpointCoin
  mixtureCoins := data.mixtureCoins
  falsePositiveCoin := data.falsePositiveCoin

theorem eraseRecordSource_measurable [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (data : RecordSimulatorData I SourceSeed SimSeed) (hm : RecordSimulatorMeasurable data) :
    RecordSimulatorMeasurable (eraseRecordSource data) :=
  ⟨measurable_const, hm.2⟩

/-- Once the actual record-level representation exists, its full-policy
infimum consequence needs no truncation, finite penalty, or restriction of
the original seed universe. The infinity-objective branch is retained. -/
theorem representationAtPenaltyInfima_of_recordRepresentation (P : PaperProofs.Paid.Parameters)
    (hrep : P.RecordRepresentationClaims.{u}) : P.RepresentationAtPenaltyInfima.{u} := by
  intro fee hfee C accounting penalty
  apply le_antisymm
  · unfold paidPenaltyValue
    refine le_iInf fun Seed => le_iInf fun ms => ?_
    let : MeasurableSpace Seed := ms
    refine le_iInf fun ν => le_iInf fun hν => ?_
    let : IsProbabilityMeasure ν := hν
    refine le_iInf fun original => ?_
    by_cases hf : expectedBill (P.input fee hfee) C.val .uncapped accounting original.rule ν ≠ ⊤
    · let lifted := liftPolicy.{u} (P.input fee hfee) C.val .uncapped accounting original
      let νlift : Measure (ULift.{u} Seed) := ν.map ULift.up
      have hνlift : IsProbabilityMeasure νlift := by dsimp [νlift]; infer_instance
      have hliftbill : expectedBill (P.input fee hfee) C.val .uncapped accounting lifted.rule νlift =
          expectedBill (P.input fee hfee) C.val .uncapped accounting original.rule ν :=
        expectedBill_liftPolicy (P.input fee hfee) C.val .uncapped accounting original ν
      obtain ⟨stopped, _hstop, SimSeed, msim, νs, hνs, actual, data, hboundary, hobj⟩ :=
        hrep.2 fee hfee C accounting .uncapped (ULift.{u} Seed) inferInstance νlift hνlift lifted
          (hliftbill ▸ hf)
      let : MeasurableSpace SimSeed := msim
      let : IsProbabilityMeasure νs := hνs
      rcases hboundary with ⟨hm, _hcausal, _halign, _hlaw, hshape, _hrest⟩
      calc
        _ ≤ paidPenaltyObjective (P.input fee hfee) C.val accounting actual.rule νs penalty := by
          unfold PaperProofs.Paid.Parameters.symmetricRecordPenaltyValue
          exact iInf_le_of_le SimSeed (iInf_le_of_le msim
            (iInf_le_of_le νs (iInf_le_of_le hνs (iInf_le_of_le actual
              (iInf_le_of_le (eraseRecordSource data)
                (iInf_le_of_le (eraseRecordSource_measurable data hm)
                  (iInf_le_of_le hshape le_rfl)))))))
        _ ≤ expectedBill (P.input fee hfee) C.val .uncapped accounting lifted.rule νlift +
            penalty * risk (P.input fee hfee) C.val .uncapped accounting lifted.rule νlift := hobj penalty
        _ = paidPenaltyObjective (P.input fee hfee) C.val accounting original.rule ν penalty := by
          rw [hliftbill, risk_liftPolicy]
          rfl
    · have htop : expectedBill (P.input fee hfee) C.val .uncapped accounting original.rule ν = ⊤ :=
        not_ne_iff.mp hf
      simp only [paidPenaltyObjective, htop, top_add]
      exact le_top
  · exact P.paidPenaltyValue_le_symmetricRecordPenaltyValue fee hfee C accounting penalty

end PDROC
