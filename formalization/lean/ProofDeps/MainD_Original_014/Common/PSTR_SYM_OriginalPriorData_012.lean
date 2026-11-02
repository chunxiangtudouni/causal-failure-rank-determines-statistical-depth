module

public import Common.PSTR_SYM_FirstRat_011
public import PaperProofs.Common.CompactPriceClaims

/-! Original heterogeneous symbolic input has a genuine first prior Rat
when N>0. This derives the input shape; it does not add a field, parser
answer or caller precondition beyond this explicit positive branch. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicLocator

open PaperProofs.Common

def setNumbers {q : Nat} (tools : Finset (Fin q)) : List Nat :=
  (List.finRange q).map (fun tool => if decide (tool ∈ tools) then 1 else 0)

theorem rawSet_numbers {q : Nat} (tools : Finset (Fin q)) :
    rawSet tools = (setNumbers tools).map Datum.natural := by
  simp only [rawSet, setNumbers, List.map_map, Function.comp_def, boolDatum]

theorem incidence_numbers {q : Nat} (full : List (Finset (Fin q))) :
    full.flatMap rawSet = (full.flatMap setNumbers).map Datum.natural := by
  induction full with
  | nil => rfl
  | cons head later ih =>
    simp only [List.flatMap_cons, rawSet_numbers, List.map_append, ih]

theorem finRange_head_zero (N : Nat) (positive : 0 < N) :
    ∃ later : List (Fin N), List.finRange N = ⟨0,positive⟩ :: later := by
  cases N with
  | zero => omega
  | succ N =>
    exact ⟨(List.finRange N).map Fin.succ, by simpa using (List.finRange_succ (n := N))⟩

def firstStage {I : Instance} (positive : 0 < I.stageCount) : I.Stage := ⟨0,positive⟩

/-- Both witnesses are determined by ORIGINAL raw data. The machine is
not selected using the witnesses; the real parser reads their actual bits. -/
theorem original_prior_data {I : Instance} (input : StatisticalInput I)
    (available : Finset I.Tool) (positive : 0 < I.stageCount) :
    ∃ (numbers : List Nat) (remaining : List Datum),
      rawInstance input ++ rawSet available = numbers.map Datum.natural ++
        .rational (input.experiment (firstStage positive)).priorOne :: remaining := by
  obtain ⟨later, stages⟩ := finRange_head_zero I.compatibility.length
    (by simpa only [Instance.stageCount] using positive)
  let stage := firstStage (I := I) positive
  let experiment := input.experiment stage
  let channels := [false,true].flatMap (fun truth => (List.finRange experiment.alphabetSize).map
    (fun symbol => Datum.rational (experiment.channel truth symbol)))
  let fees := (List.finRange I.stageCount).flatMap (fun step => (List.finRange I.toolCount).map
    (fun tool => Datum.rational (input.correctionFee step tool)))
  have experiments : (List.finRange I.compatibility.length).flatMap
      (fun step : I.Stage => rawExperiment (input.experiment step)) =
      rawExperiment experiment ++ later.flatMap (fun step => rawExperiment (input.experiment step)) := by
    rw [stages, List.flatMap_cons]
    all_goals rfl
  refine ⟨[I.stageCount,I.toolCount] ++ I.compatibility.flatMap setNumbers ++ [experiment.alphabetSize],
    [.rational experiment.observationFee] ++ channels ++
      later.flatMap (fun step => rawExperiment (input.experiment step)) ++ fees ++ rawSet available, ?_⟩
  unfold rawInstance
  simp only [Instance.stageCount]
  rw [experiments, incidence_numbers]
  simp only [List.flatMap_cons, List.flatMap_nil, rawExperiment,
    List.map_append, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_assoc, stage, experiment, channels, fees, Instance.stageCount, firstStage]

theorem original_prior_bits {I : Instance} (input : StatisticalInput I)
    (available : Finset I.Tool) (positive : 0 < I.stageCount) :
    ∃ (numbers : List Nat) (remaining : List Datum),
      rawInstance input ++ rawSet available = numbers.map Datum.natural ++
        .rational (input.experiment (firstStage positive)).priorOne :: remaining ∧
      CompactPrice.symbolicInput input available =
        encodeNat (rawInstance input ++ rawSet available).length ++
          (naturalPrefix numbers ++ encodeDatum (.rational
            (input.experiment (firstStage positive)).priorOne) ++ (remaining.flatMap encodeDatum ++ [true])) := by
  obtain ⟨numbers, remaining, data⟩ := original_prior_data input available positive
  refine ⟨numbers,remaining,data,?_⟩
  unfold CompactPrice.symbolicInput encode
  rw [data]
  simp only [List.flatMap_append, List.flatMap_map, List.flatMap_cons,
    naturalPrefix, List.append_assoc]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicLocator
