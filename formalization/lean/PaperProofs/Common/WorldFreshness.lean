module

public import PaperProofs.Common.World

/-!
Pre-birth freshness derived from the actual finite independent world law and
its independent private seed. This closes `PreBirthFreshness` as a probability
theorem. A native controller's generated visible history must still be proved
to factor through `preBirthView`; that operational obligation is not assumed
or proved by this module.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace PaperProofs.Common.StatisticalInput

variable {I : Instance}

theorem pastWorld_independent_next (input : StatisticalInput I) (next : I.Stage) :
    IndepFun (fun world : input.World =>
        fun i : {i : I.Stage // i.val < next.val} => world i.val)
      (fun world => world next) input.worldLaw := by
  have hdisjoint : Disjoint {i : I.Stage | i.val < next.val} {next} :=
    Set.disjoint_singleton_right.mpr (Nat.lt_irrefl next.val)
  have h := (input.worldLaw_independent_stages).indepFun_set
    {i : I.Stage | i.val < next.val} {next} hdisjoint (fun i => measurable_pi_apply i)
  exact h.comp measurable_id
    (measurable_pi_apply (⟨next, Set.mem_singleton next⟩ : ({next} : Set I.Stage)))

section PrivateSeed

variable {Seed : Type*} [MeasurableSpace Seed]

theorem seededWorldLaw_preBirthView (input : StatisticalInput I) (ν : Measure Seed)
    (next : I.Stage) :
    (input.seededWorldLaw ν).map (input.preBirthView next) =
      ν.prod (input.worldLaw.map (fun world =>
        fun i : {i : I.Stage // i.val < next.val} => world i.val)) := by
  have hp : Measurable (fun world : input.World =>
      fun i : {i : I.Stage // i.val < next.val} => world i.val) :=
    measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val)
  have hmap : Prod.map (id : Seed → Seed)
      (fun world : input.World => fun i : {i : I.Stage // i.val < next.val} => world i.val) =
      input.preBirthView next := by
    funext sample
    rcases sample with ⟨seed, world⟩
    rfl
  unfold seededWorldLaw
  rw [← hmap]
  simpa only [Measure.map_id] using
    (Measure.map_prod_map ν input.worldLaw measurable_id hp).symm

theorem preBirthView_independent_next (input : StatisticalInput I) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (next : I.Stage) :
    IndepFun (input.preBirthView (Seed := Seed) next)
      (fun sample : Seed × input.World => sample.2 next) (input.seededWorldLaw ν) := by
  let past : input.World → input.PastWorld next := fun world i => world i.val
  have hp : Measurable past := measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val)
  have hn : Measurable (fun world : input.World => world next) := measurable_pi_apply next
  have hnext : Measurable (fun sample : Seed × input.World => sample.2 next) :=
    hn.comp measurable_snd
  have hworld : input.worldLaw.map (fun world => (past world, world next)) =
      (input.worldLaw.map past).prod (input.stageLaw next) := by
    rw [(input.pastWorld_independent_next next).map_prod_eq_prod_map_map
      hp.aemeasurable hn.aemeasurable, input.worldLaw_coordinate]
  have hseeded : (input.seededWorldLaw ν).map
      (fun sample => (sample.1, (past sample.2, sample.2 next))) =
      ν.prod ((input.worldLaw.map past).prod (input.stageLaw next)) := by
    calc
      _ = ν.prod (input.worldLaw.map (fun world => (past world, world next))) := by
        have hmap : Prod.map (id : Seed → Seed)
            (fun world : input.World => (past world, world next)) =
            (fun sample : Seed × input.World =>
              (sample.1, (past sample.2, sample.2 next))) := by
          funext sample
          rcases sample with ⟨seed, world⟩
          rfl
        unfold seededWorldLaw
        rw [← hmap]
        simpa only [Measure.map_id] using
          (Measure.map_prod_map ν input.worldLaw measurable_id (hp.prodMk hn)).symm
      _ = _ := by rw [hworld]
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (input.measurable_preBirthView next).aemeasurable
    hnext.aemeasurable).mpr
  rw [input.seededWorldLaw_preBirthView, input.seededWorldLaw_coordinate]
  apply (MeasurableEquiv.prodAssoc :
    (Seed × input.PastWorld next) × input.StageSample next ≃ᵐ
      Seed × input.PastWorld next × input.StageSample next).map_measurableEquiv_injective
  rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable
    ((input.measurable_preBirthView next).prodMk hnext),
    Measure.prodAssoc_prod]
  exact hseeded

theorem preBirthRecord_independent_next (input : StatisticalInput I) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (next : I.Stage) {History : Type*} [MeasurableSpace History]
    (record : Seed × input.PastWorld next → History) (hrecord : Measurable record) :
    IndepFun (fun sample : Seed × input.World => record (input.preBirthView next sample))
      (fun sample => sample.2 next) (input.seededWorldLaw ν) :=
  (input.preBirthView_independent_next ν next).comp hrecord measurable_id

theorem preBirthFreshness (input : StatisticalInput I) (ν : Measure Seed) :
    input.PreBirthFreshness ν := by
  intro hν next History m
  let : MeasurableSpace History := m
  have : IsProbabilityMeasure ν := hν
  intro record hrecord
  exact input.preBirthRecord_independent_next ν next record hrecord

end PrivateSeed

end PaperProofs.Common.StatisticalInput
