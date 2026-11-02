module

public import PaperProofs.Statistics.Experiment
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Basic.ENNReal.BigOperators

/-!
The local comparator of `price-proofs.tex:5-55` is an infimum over actual
measurable randomized sequential rules. Observation counts and expectations
take values in ENNReal, including infinity. The stopped-information, SPRT and
logarithmic-price propositions at the end are declarations of outstanding
proof obligations, not axioms and not fields of the admissible test class.
-/

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory Filter

namespace PaperProofs.Statistics.BinaryExperiment

theorem priorReal_sum (E : BinaryExperiment) : ∑ x : Bool, E.priorReal x = 1 := by
  simp [priorReal, prior]

noncomputable def priorMass (E : BinaryExperiment) (x : Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (E.priorReal x)

theorem priorMass_sum (E : BinaryExperiment) : ∑ x : Bool, E.priorMass x = 1 := by
  unfold priorMass
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => (E.priorReal_pos x).le)]
  rw [E.priorReal_sum]
  simp

noncomputable def channelPMF (E : BinaryExperiment) (x : Bool) : PMF (Fin E.alphabetSize) :=
  PMF.ofFintype (fun y => ENNReal.ofReal (E.channelReal x y)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => (E.channelReal_pos x y).le)]
    rw [E.channelReal_sum]
    simp)

noncomputable def channelLaw (E : BinaryExperiment) (x : Bool) : Measure (Fin E.alphabetSize) :=
  (E.channelPMF x).toMeasure

instance channelLaw_probability (E : BinaryExperiment) (x : Bool) :
    IsProbabilityMeasure (E.channelLaw x) := by
  unfold channelLaw
  infer_instance

/-- Conditional on the true bit, all reviews are an actual infinite iid tape. -/
noncomputable def tapeLaw (E : BinaryExperiment) (x : Bool) : Measure E.Tape :=
  Measure.infinitePi (fun _ : ℕ => E.channelLaw x)

instance tapeLaw_probability (E : BinaryExperiment) (x : Bool) :
    IsProbabilityMeasure (E.tapeLaw x) := by
  unfold tapeLaw
  infer_instance

theorem tapeLaw_coordinate (E : BinaryExperiment) (x : Bool) (n : ℕ) :
    (E.tapeLaw x).map (fun tape => tape n) = E.channelLaw x := by
  exact Measure.infinitePi_map_eval (fun _ : ℕ => E.channelLaw x) n

theorem tapeLaw_independent (E : BinaryExperiment) (x : Bool) :
    ProbabilityTheory.iIndepFun (fun n (tape : E.Tape) => tape n) (E.tapeLaw x) := by
  exact ProbabilityTheory.iIndepFun_infinitePi
    (P := fun _ : ℕ => E.channelLaw x) (X := fun _ y => y) (fun _ => measurable_id)

section PrivateSeed

variable {Seed : Type*} [MeasurableSpace Seed]

/-- The private seed has the same law under both truths and is independent of the tape. -/
noncomputable def conditionalLaw (E : BinaryExperiment) (ν : Measure Seed) (x : Bool) :
    Measure (Seed × E.Tape) := ν.prod (E.tapeLaw x)

instance conditionalLaw_probability (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (x : Bool) : IsProbabilityMeasure (E.conditionalLaw ν x) := by
  unfold conditionalLaw
  infer_instance

theorem seed_independent_tape (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (x : Bool) :
    ProbabilityTheory.IndepFun (fun ω : Seed × E.Tape => ω.1)
      (fun ω : Seed × E.Tape => ω.2) (E.conditionalLaw ν x) := by
  exact ProbabilityTheory.indepFun_prod measurable_id measurable_id

/-- Measurability and prefix causality only; no information or performance bound is assumed. -/
structure AdmissibleRule (E : BinaryExperiment) (Seed : Type*) [MeasurableSpace Seed] where
  rule : E.SequentialRule Seed
  measurable_stop : Measurable (fun ω : Seed × E.Tape => rule.stop ω.1 ω.2)
  measurable_decision : Measurable (fun ω : Seed × E.Tape => rule.decision ω.1 ω.2)

def constantGuess (E : BinaryExperiment) (Seed : Type*) [MeasurableSpace Seed] (bit : Bool) :
    E.AdmissibleRule Seed where
  rule := {
    stop := fun _ _ => 0
    decision := fun _ _ => bit
    stopping := by intro seed tape tape' n _; rfl
    stoppedDecision := by intro seed tape tape' n _ _ _; rfl
  }
  measurable_stop := measurable_const
  measurable_decision := measurable_const

noncomputable def sampleCountENNReal (n : ℕ∞) : ℝ≥0∞ :=
  if n = ⊤ then ⊤ else n.toNat

@[simp] theorem sampleCountENNReal_zero : sampleCountENNReal 0 = 0 := by
  simp [sampleCountENNReal]

@[simp] theorem sampleCountENNReal_top : sampleCountENNReal ⊤ = ⊤ := by
  simp [sampleCountENNReal]

theorem observationCharge_eq (E : BinaryExperiment) (n : ℕ∞) :
    E.observationCharge n = ENNReal.ofReal (E.observationFee : ℝ) * sampleCountENNReal n := by
  by_cases hn : n = ⊤
  · subst n
    have hfee : ENNReal.ofReal (E.observationFee : ℝ) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr E.observationFee_real_pos)
    simp [observationCharge, sampleCountENNReal, hfee]
  · simp [observationCharge, sampleCountENNReal, hn]

noncomputable def expectedSamples (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (x : Bool) : ℝ≥0∞ :=
  ∫⁻ ω, sampleCountENNReal (test.rule.stop ω.1 ω.2) ∂(E.conditionalLaw ν x)

noncomputable def expectedObservationCharge (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (x : Bool) : ℝ≥0∞ :=
  ∫⁻ ω, E.observationCharge (test.rule.stop ω.1 ω.2) ∂(E.conditionalLaw ν x)

theorem expectedObservationCharge_eq (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (x : Bool) :
    E.expectedObservationCharge ν test x =
      ENNReal.ofReal (E.observationFee : ℝ) * E.expectedSamples ν test x := by
  unfold expectedObservationCharge expectedSamples
  simp_rw [E.observationCharge_eq]
  exact lintegral_const_mul _
    ((measurable_of_countable sampleCountENNReal).comp test.measurable_stop)

noncomputable def conditionalError (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (x : Bool) : ℝ≥0∞ :=
  E.conditionalLaw ν x {ω | test.rule.decision ω.1 ω.2 ≠ x}

noncomputable def decisionLaw (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (x : Bool) : Measure Bool :=
  (E.conditionalLaw ν x).map (fun ω => test.rule.decision ω.1 ω.2)

/-- The finite stopped word, retaining the private seed. It is used for the information
identity only after both conditional expected sample counts have been shown finite. -/
abbrev StoppedWord (E : BinaryExperiment) := Σ n : ℕ, Fin n → Fin E.alphabetSize

def stoppedTranscript (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (ω : Seed × E.Tape) : Seed × E.StoppedWord :=
  (ω.1, ⟨(test.rule.stop ω.1 ω.2).toNat, fun k => ω.2 k.val⟩)

noncomputable def transcriptLaw (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (x : Bool) : Measure (Seed × E.StoppedWord) :=
  (E.conditionalLaw ν x).map (E.stoppedTranscript test)

instance decisionLaw_probability (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) (x : Bool) :
    IsProbabilityMeasure (E.decisionLaw ν test x) := by
  unfold decisionLaw
  infer_instance

noncomputable def bayesError (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) : ℝ≥0∞ :=
  ∑ x : Bool, E.priorMass x * E.conditionalError ν test x

theorem bayesError_le_one (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) : E.bayesError ν test ≤ 1 := by
  calc
    _ ≤ ∑ x : Bool, E.priorMass x * 1 := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_right (prob_le_one (μ := E.conditionalLaw ν x)) _
    _ = 1 := by simpa using E.priorMass_sum

noncomputable def bayesObservationCharge (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) : ℝ≥0∞ :=
  ∑ x : Bool, E.priorMass x * E.expectedObservationCharge ν test x

noncomputable def bayesObjective (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (penalty : ℝ≥0∞) : ℝ≥0∞ :=
  E.bayesObservationCharge ν test + penalty * E.bayesError ν test

@[simp] theorem constantGuess_observationCharge (E : BinaryExperiment) (ν : Measure Seed)
    (bit : Bool) : E.bayesObservationCharge ν (E.constantGuess Seed bit) = 0 := by
  simp [bayesObservationCharge, expectedObservationCharge, constantGuess]

end PrivateSeed

/-- The true local penalty comparator. The seed space and its probability law are unrestricted.
The infimum includes non-MAP rules and tests with infinite expected observation charge. -/
noncomputable def localValue (E : BinaryExperiment) (penalty : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (Seed : Type), ⨅ (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ⨅ (ν : Measure Seed) (_h : IsProbabilityMeasure ν) (test : E.AdmissibleRule Seed),
      E.bayesObjective ν test penalty

theorem localValue_le_test (E : BinaryExperiment) {Seed : Type} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed)
    (penalty : ℝ≥0∞) : E.localValue penalty ≤ E.bayesObjective ν test penalty := by
  exact iInf_le_of_le Seed (iInf_le_of_le ‹MeasurableSpace Seed›
    (iInf_le_of_le ν (iInf_le_of_le ‹IsProbabilityMeasure ν›
      (iInf_le_of_le test le_rfl))))

theorem localValue_le_penalty (E : BinaryExperiment) (penalty : ℝ≥0∞) :
    E.localValue penalty ≤ penalty := by
  let ν : Measure Unit := Measure.dirac ()
  have : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  calc
    _ ≤ E.bayesObjective ν (E.constantGuess Unit false) penalty :=
      E.localValue_le_test ν (E.constantGuess Unit false) penalty
    _ = penalty * E.bayesError ν (E.constantGuess Unit false) := by
      simp [bayesObjective]
    _ ≤ penalty := by
      simpa using mul_le_mul_right (E.bayesError_le_one ν (E.constantGuess Unit false)) penalty

theorem localValue_ne_top (E : BinaryExperiment) (penalty : ℝ≥0∞) (h : penalty ≠ ⊤) :
    E.localValue penalty ≠ ⊤ := by
  intro htop
  exact h (top_le_iff.mp (htop ▸ E.localValue_le_penalty penalty))

theorem localValue_ofReal_ne_top (E : BinaryExperiment) (t : ℝ) :
    E.localValue (ENNReal.ofReal t) ≠ ⊤ :=
  E.localValue_ne_top _ ENNReal.ofReal_ne_top

/-- Real conversion is used only after the preceding finiteness theorem. -/
noncomputable def localValueReal (E : BinaryExperiment) (t : ℝ) : ℝ :=
  (E.localValue (ENNReal.ofReal t)).toReal

theorem localValueReal_nonneg (E : BinaryExperiment) (t : ℝ) : 0 ≤ E.localValueReal t :=
  ENNReal.toReal_nonneg

theorem localValueReal_le (E : BinaryExperiment) (t : ℝ) (ht : 0 ≤ t) :
    E.localValueReal t ≤ t := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (E.localValue_le_penalty (ENNReal.ofReal t))
  simpa [localValueReal, ENNReal.toReal_ofReal ht] using h

@[simp] theorem localValue_zero (E : BinaryExperiment) : E.localValue 0 = 0 :=
  le_antisymm (E.localValue_le_penalty 0) zero_le

noncomputable def logOddsScore (E : BinaryExperiment) (tape : E.Tape) (n : ℕ) : ℝ :=
  Real.log (E.priorReal true / E.priorReal false) +
    ∑ k ∈ Finset.range n,
      Real.log (E.channelReal true (tape k) / E.channelReal false (tape k))

noncomputable def posteriorThresholdStop (E : BinaryExperiment) (p : ℚ)
    (tape : E.Tape) : ℕ∞ :=
  sInf {t : ℕ∞ | ∃ n : ℕ, t = n ∧
    Real.log ((1 - (p : ℝ)) / (p : ℝ)) ≤ |E.logOddsScore tape n|}

def IsPosteriorThresholdRule (E : BinaryExperiment) (p : ℚ)
    (test : E.AdmissibleRule Unit) : Prop := by
  classical
  exact (∀ tape, test.rule.stop () tape = E.posteriorThresholdStop p tape) ∧
    ∀ tape (n : ℕ), test.rule.stop () tape = n →
      test.rule.decision () tape = decide (0 ≤ E.logOddsScore tape n)

/-- `price-proofs.tex:23-31`, proved in PosteriorSPRT: the actual posterior-threshold SPRT has finite
conditional expectations and the sharp drift coefficient, with a constant fixed by E. -/
def PosteriorSPRTGuarantee (E : BinaryExperiment) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ p : ℚ, 0 < p → p ≤ 1 / 4 →
    ∃ test : E.AdmissibleRule Unit,
      E.IsPosteriorThresholdRule p test ∧
      E.bayesError (Measure.dirac ()) test ≤ ENNReal.ofReal (p : ℝ) ∧
      ∀ x,
        E.expectedSamples (Measure.dirac ()) test x ≠ ⊤ ∧
        E.expectedObservationCharge (Measure.dirac ()) test x ≠ ⊤ ∧
        (E.expectedObservationCharge (Measure.dirac ()) test x).toReal ≤
          (E.observationFee : ℝ) / E.divergence x * (Real.log (1 / (p : ℝ)) + K)

/-- Finite full-support KL agrees with Mathlib's extended measure KL, proved in
ChannelKL. This statement is not a new paper hypothesis. -/
def ChannelDivergenceAgreement (E : BinaryExperiment) : Prop :=
  ∀ x, InformationTheory.klDiv (E.channelLaw x) (E.channelLaw (!x)) =
    ENNReal.ofReal (E.divergence x)

/-- Stopped information identity, proved in StoppedInformation/StoppedWald,
before data processing, `price-proofs.tex:40-47`.
Finiteness is explicit; no integration on the eventual-success event is used. -/
def StoppedInformationIdentity (E : BinaryExperiment) : Prop :=
  ∀ (Seed : Type) (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ∀ (ν : Measure Seed) (_h : IsProbabilityMeasure ν) (test : E.AdmissibleRule Seed),
      (∀ x, E.expectedSamples ν test x ≠ ⊤) →
      Measurable (E.stoppedTranscript test) ∧
      ∀ x, InformationTheory.klDiv (E.transcriptLaw ν test x) (E.transcriptLaw ν test (!x)) =
        ENNReal.ofReal (E.divergence x) * E.expectedSamples ν test x

/-- `price-proofs.tex:40-47`, proved in StoppedWald. Both conditional expectations are required finite
before using the stopped-information argument; infinite Bayes cost needs no such reduction.
The decision-law KL is extended-valued and handles zero/one error probabilities. -/
def StoppedDecisionInformationBound (E : BinaryExperiment) : Prop :=
  ∀ (Seed : Type) (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ∀ (ν : Measure Seed) (_h : IsProbabilityMeasure ν) (test : E.AdmissibleRule Seed),
      (∀ x, E.expectedSamples ν test x ≠ ⊤) →
      ∀ x, InformationTheory.klDiv (E.decisionLaw ν test x) (E.decisionLaw ν test (!x)) ≤
        ENNReal.ofReal (E.divergence x) * E.expectedSamples ν test x

/-- `lem:price-local`, proved in LocalPrice, with the actual infimum above. -/
def LocalLogarithmicPrice (E : BinaryExperiment) : Prop :=
  Tendsto (fun t : ℝ => E.localValueReal t / (E.coefficient * Real.log t))
    atTop (nhds 1)

/-- The global logarithmic envelope, proved in LocalPrice (`price-proofs.tex:20,31-33`). -/
def GlobalLogarithmicEnvelope (E : BinaryExperiment) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t → E.localValueReal t ≤ K * Real.log (1 + t)

end PaperProofs.Statistics.BinaryExperiment
