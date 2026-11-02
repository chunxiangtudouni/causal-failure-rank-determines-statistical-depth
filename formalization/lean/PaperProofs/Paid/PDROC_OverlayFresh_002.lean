module

public import PaperProofs.Paid.PDROC_OverlayFresh_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u v
variable {Seed : Type u} {Row : Type v} [MeasurableSpace Seed] [MeasurableSpace Row]

/-- Reconstruct a full sample with specified current row and world. The
remaining coordinates are actual data, so no measurable range hypothesis is needed. -/
def overlayFreshRebuild (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (row : Row) (world : Bool × P.experiment.Tape)
    (base : OverlayFreshBase P Seed Row stage × SimulatorOtherWorld P stage) :
    OverlayFreshSeed P Seed Row × (P.input fee hfee).World :=
  ((base.1.1, (base.1.2.1, fun i => if h : i = stage then row else base.1.2.2 ⟨i, h⟩)),
    fun i => if h : i = stage then world else base.2 ⟨i, h⟩)

theorem measurable_overlayFreshRebuild (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (row : Row) (world : Bool × P.experiment.Tape) :
    Measurable (overlayFreshRebuild (Seed := Seed) P fee hfee stage row world) := by
  have hr : Measurable (fun base : OverlayFreshBase P Seed Row stage × SimulatorOtherWorld P stage =>
      fun i : P.sharedInstance.Stage => if h : i = stage then row else base.1.2.2 ⟨i, h⟩) := by
    apply measurable_pi_iff.mpr
    intro i
    by_cases hi : i = stage
    · simp only [hi, ↓reduceDIte]
      exact measurable_const
    · simp only [hi, ↓reduceDIte]
      exact (measurable_pi_apply (⟨i, hi⟩ : {j : P.sharedInstance.Stage // j ≠ stage})).comp
        ((measurable_snd.comp measurable_snd).comp measurable_fst)
  have hw : Measurable (fun base : OverlayFreshBase P Seed Row stage × SimulatorOtherWorld P stage =>
      fun i : P.sharedInstance.Stage => if h : i = stage then world else base.2 ⟨i, h⟩) := by
    apply measurable_pi_iff.mpr
    intro i
    by_cases hi : i = stage
    · simp only [hi, ↓reduceDIte]
      exact measurable_const
    · simp only [hi, ↓reduceDIte]
      exact (measurable_pi_apply (⟨i, hi⟩ : {j : P.sharedInstance.Stage // j ≠ stage})).comp measurable_snd
  exact ((measurable_fst.comp measurable_fst).prodMk
    (((measurable_fst.comp measurable_snd).comp measurable_fst).prodMk hr)).prodMk hw

/-- Replacement touches only genuinely fresh current coordinates. -/
def overlayFreshReplace (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (row : Row) (world : Bool × P.experiment.Tape)
    (sample : OverlayFreshSeed P Seed Row × (P.input fee hfee).World) :
    OverlayFreshSeed P Seed Row × (P.input fee hfee).World :=
  ((sample.1.1, (sample.1.2.1, fun i => if i = stage then row else sample.1.2.2 i)),
    fun i => if i = stage then world else sample.2 i)

omit [MeasurableSpace Seed] [MeasurableSpace Row] in
theorem overlayFreshRebuild_allOther_eq_replace (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (row : Row) (world : Bool × P.experiment.Tape)
    (sample : OverlayFreshSeed P Seed Row × (P.input fee hfee).World) :
    overlayFreshRebuild P fee hfee stage row world (overlayFreshAllOther P fee hfee stage sample) =
      overlayFreshReplace P fee hfee stage row world sample := by
  rfl

def overlayFreshGateFactor {Gate : Type*} (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (row : Row) (world : Bool × P.experiment.Tape)
    (gate : OverlayFreshSeed P Seed Row × (P.input fee hfee).World → Gate) :
    OverlayFreshBase P Seed Row stage × SimulatorOtherWorld P stage → Gate :=
  gate ∘ overlayFreshRebuild P fee hfee stage row world

/-- Pointwise current-coordinate noninterference supplies a concrete measurable
base factor. This avoids conditioning on a singleton seed or on a semantic history range. -/
theorem overlayFreshGate_factor {Gate : Type*} [MeasurableSpace Gate]
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (stage : P.sharedInstance.Stage)
    (row : Row) (world : Bool × P.experiment.Tape)
    (gate : OverlayFreshSeed P Seed Row × (P.input fee hfee).World → Gate)
    (hg : Measurable gate)
    (hinvariant : ∀ sample newRow newWorld,
      gate (overlayFreshReplace P fee hfee stage newRow newWorld sample) = gate sample) :
    Measurable (overlayFreshGateFactor P fee hfee stage row world gate) ∧
      ∀ sample, overlayFreshGateFactor P fee hfee stage row world gate
        (overlayFreshAllOther P fee hfee stage sample) = gate sample := by
  constructor
  · exact hg.comp (measurable_overlayFreshRebuild P fee hfee stage row world)
  · intro sample
    change gate (overlayFreshRebuild P fee hfee stage row world
      (overlayFreshAllOther P fee hfee stage sample)) = gate sample
    rw [overlayFreshRebuild_allOther_eq_replace]
    exact hinvariant sample row world

/-- Final fresh-stage law for a concrete measurable noninterfering observable.
The invariance premise is an explicit remaining implementation obligation. -/
theorem overlayFreshWorldLaw_invariantGate {Gate : Type*} [MeasurableSpace Gate]
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (ν : Measure Seed) (rowLaw : Measure Row)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure rowLaw] (stage : P.sharedInstance.Stage)
    (row : Row) (world : Bool × P.experiment.Tape)
    (gate : OverlayFreshSeed P Seed Row × (P.input fee hfee).World → Gate)
    (hg : Measurable gate)
    (hinvariant : ∀ sample newRow newWorld,
      gate (overlayFreshReplace P fee hfee stage newRow newWorld sample) = gate sample) :
    ((P.input fee hfee).seededWorldLaw (overlayFreshSeedLaw P ν rowLaw)).map (fun sample =>
      (gate sample, overlayFreshCurrent P fee hfee stage sample)) =
        ((overlayFreshAllOtherLaw P fee hfee ν rowLaw stage).map
          (overlayFreshGateFactor P fee hfee stage row world gate)).prod
            (rowLaw.prod ((P.input fee hfee).stageLaw stage)) := by
  have hf := overlayFreshGate_factor P fee hfee stage row world gate hg hinvariant
  have h := overlayFreshWorldLaw_recordGate P fee hfee ν rowLaw stage
    (overlayFreshGateFactor P fee hfee stage row world gate) hf.1
  simpa only [hf.2] using h

end PDROC
