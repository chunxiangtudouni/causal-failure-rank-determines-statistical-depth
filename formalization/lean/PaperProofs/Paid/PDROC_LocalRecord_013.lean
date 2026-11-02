module
public import PaperProofs.Paid.PDROC_LocalRecord_012
public import PaperProofs.Paid.PDROC_Simulator_001

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native
open PaperProofs.Paid
open PaperProofs.Statistics

namespace PDROC
universe u
section
variable {Seed : Type u} [MeasurableSpace Seed]

/-- The simulator's direct entry++review source rule is an actual existing
native head test, with its original source seed and entire entry history. -/
noncomputable def simulatorLocalTest (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    P.binarySymmetric.experiment.AdmissibleRule (Seed × List (VisibleEvent P.sharedInstance)) :=
  nativeHeadTest (P.input fee hfee) stage (simulatorPrewriteRule P source)
    (measurable_simulatorPrewriteRule P source hm)

noncomputable def simulatorDrawDecoder (P : Parameters) (_fee : ℚ) (_hfee : 0 ≤ _fee)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (record : (Seed × List (VisibleEvent P.sharedInstance)) × P.binarySymmetric.experiment.StoppedWord) :
    SimulatorDraw P.sharedInstance :=
  let action := source record.1.1 (record.1.2 ++
    List.ofFn (fun k : Fin record.2.1 => VisibleEvent.observation stage (record.2.2 k).val))
  { record := {observations := List.ofFn record.2.2, decision := optionWriteBit action}
    action := action }

theorem measurable_simulatorDrawDecoder (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (simulatorDrawDecoder P fee hfee source stage) := by
  apply measurable_from_prod_countable_left
  intro word
  have ha := (measurable_simulatorPrewriteRule P source hm).comp
    (measurable_id.prodMk (measurable_const (a := List.ofFn (fun k : Fin word.1 =>
      VisibleEvent.observation stage (word.2 k).val))))
  exact (measurable_of_countable (fun action : Action P.sharedInstance =>
    ({record := {observations := List.ofFn word.2, decision := optionWriteBit action}, action := action} :
      SimulatorDraw P.sharedInstance))).comp ha

omit [MeasurableSpace Seed] in
/-- The draw keeps the whole real stopped word, hence its original integer
posterior level; the terminal action does not change this word identity. -/
theorem simulatorDrawDecoder_word (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (record : (Seed × List (VisibleEvent P.sharedInstance)) × P.binarySymmetric.experiment.StoppedWord) :
    auxiliaryRecordWord P (simulatorDrawDecoder P fee hfee source stage record).record = record.2 := by
  rcases record with ⟨entry, ⟨n, word⟩⟩
  change (⟨(List.ofFn word).length, (List.ofFn word).get⟩ :
    Σ n, Fin n → Fin P.binarySymmetric.experiment.alphabetSize) = ⟨n, word⟩
  exact List.equivSigmaTuple.right_inv ⟨n, word⟩

/-- On every finite sample the actual simulator draw is precisely the
measurable decoder of the genuine stopped transcript. No truth is read. -/
theorem simulatorDrawAt_eq_decoder_of_finite (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage)
    (sample : (Seed × List (VisibleEvent P.sharedInstance)) × P.binarySymmetric.experiment.Tape)
    (hs : (simulatorLocalTest P fee hfee source hm stage).rule.stop sample.1 sample.2 ≠ ⊤) :
    simulatorDrawAt P fee hfee source stage sample.1.1 sample.1.2 sample.2 =
      some (simulatorDrawDecoder P fee hfee source stage
        (P.binarySymmetric.experiment.stoppedTranscript (simulatorLocalTest P fee hfee source hm stage) sample)) := by
  unfold simulatorDrawAt
  change (if (simulatorLocalTest P fee hfee source hm stage).rule.stop sample.1 sample.2 = ⊤ then none else _) = _
  rw [ite_eq_right hs]
  rfl

/-- The record level selected by an actual finite simulator draw is the
absolute integer score of the actual direct native-head stopped word. -/
theorem simulatorDrawAt_word (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage)
    (sample : (Seed × List (VisibleEvent P.sharedInstance)) × P.binarySymmetric.experiment.Tape)
    (draw : SimulatorDraw P.sharedInstance)
    (hd : simulatorDrawAt P fee hfee source stage sample.1.1 sample.1.2 sample.2 = some draw) :
    auxiliaryRecordWord P draw.record =
      (P.binarySymmetric.experiment.stoppedTranscript (simulatorLocalTest P fee hfee source hm stage) sample).2 := by
  have hs : (simulatorLocalTest P fee hfee source hm stage).rule.stop sample.1 sample.2 ≠ ⊤ := by
    intro htop
    have : simulatorDrawAt P fee hfee source stage sample.1.1 sample.1.2 sample.2 = none := by
      unfold simulatorDrawAt
      change (if (simulatorLocalTest P fee hfee source hm stage).rule.stop sample.1 sample.2 = ⊤ then none else _) = none
      rw [ite_eq_left htop]
    rw [this] at hd
    cases hd
  have heq := simulatorDrawAt_eq_decoder_of_finite P fee hfee source hm stage sample hs
  rw [hd] at heq
  rw [Option.some.inj heq]
  exact simulatorDrawDecoder_word P fee hfee source stage _

end
end PDROC
