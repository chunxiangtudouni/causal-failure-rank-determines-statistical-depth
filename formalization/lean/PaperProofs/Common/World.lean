module

public import PaperProofs.Common.Input
public import PaperProofs.Statistics.LocalTest
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Independence.Basic

/-!
A single probability space for the frozen manuscript's independent fresh
facts and conditionally iid reviews, model.tex:11--18. Each stage uses the
same `StatisticalInput.experiment` as the local sequential-test comparator.

The hidden world is available to system execution and analysis. Neither the
world nor its truth/tape lookup functions are policy-visible history fields.
Independence after a generated native history additionally needs a proof
that this history uses only the seed and earlier stages; no such performance
or freshness theorem is assumed as part of the input data.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace PaperProofs.Common.StatisticalInput

variable {I : Instance}

/-- A hidden truth together with the complete potential observation tape. -/
abbrev StageSample (input : StatisticalInput I) (i : I.Stage) :=
  Bool × (input.experiment i).Tape

/-- All stages' hidden data; observing it directly is not a policy action. -/
abbrev World (input : StatisticalInput I) :=
  ∀ i : I.Stage, input.StageSample i

/-- The truth-conditioned tape law mixed with this exact experiment's prior. -/
noncomputable def stageLaw (input : StatisticalInput I) (i : I.Stage) :
    Measure (input.StageSample i) :=
  (input.experiment i).priorMass true •
      (Measure.dirac true).prod ((input.experiment i).tapeLaw true) +
    (input.experiment i).priorMass false •
      (Measure.dirac false).prod ((input.experiment i).tapeLaw false)

instance stageLaw_probability (input : StatisticalInput I) (i : I.Stage) :
    IsProbabilityMeasure (input.stageLaw i) := by
  apply isProbabilityMeasure_iff.mpr
  simp only [stageLaw, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  simpa only [Fintype.sum_bool] using (input.experiment i).priorMass_sum

/-- This rectangle identity binds the mixed joint law to the original local
truth-conditional iid tape law. It does not introduce a new channel model. -/
theorem stageLaw_truth_tape (input : StatisticalInput I) (i : I.Stage)
    (truth : Bool) (tapes : Set (input.experiment i).Tape) :
    input.stageLaw i ({truth} ×ˢ tapes) =
      (input.experiment i).priorMass truth * (input.experiment i).tapeLaw truth tapes := by
  cases truth <;>
    simp [stageLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul]

/-- The finite product includes the empty-stage input, where it is the
probability measure on the unique empty world. -/
noncomputable def worldLaw (input : StatisticalInput I) : Measure input.World :=
  Measure.pi (fun i => input.stageLaw i)

instance worldLaw_probability (input : StatisticalInput I) :
    IsProbabilityMeasure input.worldLaw := by
  unfold worldLaw
  infer_instance

theorem worldLaw_coordinate (input : StatisticalInput I) (i : I.Stage) :
    input.worldLaw.map (fun world => world i) = input.stageLaw i := by
  exact (measurePreserving_eval (fun i => input.stageLaw i) i).map_eq

theorem worldLaw_independent_stages (input : StatisticalInput I) :
    iIndepFun (fun i (world : input.World) => world i) input.worldLaw := by
  exact iIndepFun_pi (μ := fun i => input.stageLaw i)
    (X := fun _ sample => sample) (fun _ => aemeasurable_id)

def truthAt (input : StatisticalInput I) (world : input.World) (i : I.Stage) : Bool :=
  (world i).1

def reviewAt (input : StatisticalInput I) (world : input.World) (i : I.Stage) (n : ℕ) :
    Fin (input.experiment i).alphabetSize :=
  (world i).2 n

theorem measurable_truthAt (input : StatisticalInput I) (i : I.Stage) :
    Measurable (fun world => input.truthAt world i) :=
  (measurable_pi_apply i).fst

theorem measurable_reviewAt (input : StatisticalInput I) (i : I.Stage) (n : ℕ) :
    Measurable (fun world => input.reviewAt world i n) :=
  (measurable_pi_apply n).comp (measurable_pi_apply i).snd

theorem worldLaw_truth_tape (input : StatisticalInput I) (i : I.Stage)
    (truth : Bool) (tapes : Set (input.experiment i).Tape) (htapes : MeasurableSet tapes) :
    input.worldLaw {world | world i ∈ ({truth} ×ˢ tapes)} =
      (input.experiment i).priorMass truth * (input.experiment i).tapeLaw truth tapes := by
  calc
    _ = (input.worldLaw.map (fun world => world i)) ({truth} ×ˢ tapes) :=
      (Measure.map_apply (measurable_pi_apply i)
        ((measurableSet_singleton truth).prod htapes)).symm
    _ = input.stageLaw i ({truth} ×ˢ tapes) := by rw [worldLaw_coordinate]
    _ = _ := stageLaw_truth_tape input i truth tapes

theorem worldLaw_truth (input : StatisticalInput I) (i : I.Stage) (truth : Bool) :
    input.worldLaw {world | input.truthAt world i = truth} =
      (input.experiment i).priorMass truth := by
  simpa [truthAt] using
    worldLaw_truth_tape input i truth Set.univ MeasurableSet.univ

theorem worldLaw_truth_pos (input : StatisticalInput I) (i : I.Stage) (truth : Bool) :
    0 < input.worldLaw {world | input.truthAt world i = truth} := by
  rw [worldLaw_truth]
  exact ENNReal.ofReal_pos.mpr ((input.experiment i).priorReal_pos truth)

/-- Earlier stages' complete hidden data, used only to prove that an actually
visible pre-birth history cannot depend on the next stage. -/
abbrev PastWorld (input : StatisticalInput I) (next : I.Stage) :=
  ∀ i : {i : I.Stage // i.val < next.val}, input.StageSample i.val

section PrivateSeed

variable {Seed : Type*} [MeasurableSpace Seed]

/-- Arbitrary private randomness, independent of all hidden stage data. -/
noncomputable def seededWorldLaw (input : StatisticalInput I) (ν : Measure Seed) :
    Measure (Seed × input.World) :=
  ν.prod input.worldLaw

instance seededWorldLaw_probability (input : StatisticalInput I) (ν : Measure Seed)
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (input.seededWorldLaw ν) := by
  unfold seededWorldLaw
  infer_instance

theorem seed_independent_world (input : StatisticalInput I) (ν : Measure Seed)
    [IsProbabilityMeasure ν] :
    IndepFun (fun sample : Seed × input.World => sample.1)
      (fun sample => sample.2) (input.seededWorldLaw ν) := by
  exact indepFun_prod measurable_id measurable_id

theorem seededWorldLaw_seed (input : StatisticalInput I) (ν : Measure Seed) :
    (input.seededWorldLaw ν).map Prod.fst = ν := by
  simp [seededWorldLaw]

theorem seededWorldLaw_world (input : StatisticalInput I) (ν : Measure Seed)
    [IsProbabilityMeasure ν] :
    (input.seededWorldLaw ν).map Prod.snd = input.worldLaw := by
  simp [seededWorldLaw]

theorem seededWorldLaw_coordinate (input : StatisticalInput I) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : I.Stage) :
    (input.seededWorldLaw ν).map (fun sample => sample.2 i) = input.stageLaw i := by
  calc
    _ = ((input.seededWorldLaw ν).map Prod.snd).map (fun world => world i) :=
      (Measure.map_map (measurable_pi_apply i) measurable_snd).symm
    _ = input.worldLaw.map (fun world => world i) := by rw [seededWorldLaw_world]
    _ = _ := worldLaw_coordinate input i

def preBirthView (input : StatisticalInput I) (next : I.Stage)
    (sample : Seed × input.World) : Seed × input.PastWorld next :=
  (sample.1, fun i => sample.2 i.val)

theorem measurable_preBirthView (input : StatisticalInput I) (next : I.Stage) :
    Measurable (input.preBirthView (Seed := Seed) next) := by
  apply Measurable.prodMk measurable_fst
  exact measurable_pi_iff.mpr (fun i => (measurable_pi_apply i.val).comp measurable_snd)

/-- An outstanding freshness proposition, not an assumed input field.
It states independence from every measurable function of the private seed
and the earlier stages. Connecting this assertion to a native policy also
requires proving that its generated pre-birth visible history factors
through `preBirthView`; neither obligation is silently assumed here. -/
def PreBirthFreshness (input : StatisticalInput I) (ν : Measure Seed) : Prop :=
  IsProbabilityMeasure ν →
    ∀ (next : I.Stage) (History : Type) (m : MeasurableSpace History),
      letI : MeasurableSpace History := m
      ∀ record : Seed × input.PastWorld next → History,
        Measurable record →
        IndepFun (fun sample : Seed × input.World => record (input.preBirthView next sample))
          (fun sample => sample.2 next) (input.seededWorldLaw ν)

end PrivateSeed

end PaperProofs.Common.StatisticalInput
