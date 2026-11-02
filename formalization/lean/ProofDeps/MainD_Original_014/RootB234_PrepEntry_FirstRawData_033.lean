module

public import RootB234_PrepEntry_NatPrefixRun_032

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.FirstRaw

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep PSTRTMWordPreparationFront214

variable {I : Instance}

def setNumbers {q : Nat} (tools : Finset (Fin q)) : List Nat :=
  (List.finRange q).map (fun tool => if tool∈tools then 1 else 0)

def incidenceNumbers (I : Instance) : List Nat := I.compatibility.flatMap setNumbers

def contractNumbers (contract : Contract I) : List Nat :=
  [if contract.reporting=.early then 1 else 0,
   if contract.allocation=.currentWindow then 1 else 0,
   if contract.execution=.currentWindow then 1 else 0,
   contract.totalCallCap,contract.normalCallBound]

/-- Specification only: the source reads these original fields and does
not receive this list or a stage-count case as a runtime parameter. -/
def firstNumbers (input : StatisticalInput I) (contract : Contract I) : List Nat :=
  if positive : 0<I.stageCount then
    incidenceNumbers I++[(input.experiment ⟨0,positive⟩).alphabetSize]
  else contractNumbers contract

def firstValue (input : StatisticalInput I) (budget : Rat) : Rat :=
  if positive : 0<I.stageCount then (input.experiment ⟨0,positive⟩).priorOne else budget

theorem rawSet_numbers {q : Nat} (tools : Finset (Fin q)) :
    rawSet tools=(setNumbers tools).map Datum.natural := by
  simp only [rawSet,setNumbers,boolDatum,List.map_map,Function.comp_def]
  congr 1
  funext tool
  by_cases member : tool∈tools <;> simp [member]

theorem incidence_numbers : I.compatibility.flatMap rawSet=(incidenceNumbers I).map Datum.natural := by
  simp only [incidenceNumbers,List.map_flatMap]
  congr 1
  funext tools
  exact rawSet_numbers tools

private theorem bool_number (proposition : Prop) [Decidable proposition] :
    boolDatum (decide proposition)=Datum.natural (if proposition then 1 else 0) := by
  by_cases truth : proposition <;> simp [boolDatum,truth]

theorem contract_numbers (contract : Contract I) :
    rawContract contract=(contractNumbers contract).map Datum.natural++
      (List.finRange I.stageCount).map (fun stage => Datum.natural (contract.reviewQuota stage)) := by
  simp only [rawContract,contractNumbers,List.map_cons,List.map_nil,bool_number]

theorem finRange_head {n : Nat} (positive : 0<n) :
    List.finRange n=⟨0,positive⟩::(List.finRange n).tail := by
  cases n with
  | zero => omega
  | succ n => rw [List.finRange_succ]; rfl

theorem remaining_data (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    Raw.remaining input contract budget=
      I.compatibility.flatMap rawSet++
      (List.finRange I.stageCount).flatMap (fun stage => rawExperiment (input.experiment stage))++
      (List.finRange I.stageCount).flatMap (fun stage => (List.finRange I.toolCount).map
        (fun tool => Datum.rational (input.correctionFee stage tool)))++
      rawContract contract++[.rational budget] := rfl

theorem afterTools_remaining (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    NJ.afterTools input contract budget=(Raw.remaining input contract budget).flatMap encodeDatum++[true] := rfl

/-- The actual preparation stream after J always has a first Rat. For
N>0 it is the first experiment's prior after the real incidence and
alphabet; for N=0 it is budget after the five actual contract Naturals. -/
theorem afterTools_split (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    ∃ suffix : List Bool,NJ.afterTools input contract budget=
      NatPrefix.naturals (firstNumbers input contract)++
        encodeDatum (.rational (firstValue input budget))++suffix++[true] := by
  by_cases positive : 0<I.stageCount
  · let stage : I.Stage:=⟨0,positive⟩
    let E:=input.experiment stage
    let rest : List Datum:=
      [.rational E.observationFee]++
      [false,true].flatMap (fun truth => (List.finRange E.alphabetSize).map
        (fun symbol => Datum.rational (E.channel truth symbol)))++
      (List.finRange I.stageCount).tail.flatMap (fun point => rawExperiment (input.experiment point))++
      (List.finRange I.stageCount).flatMap (fun point => (List.finRange I.toolCount).map
        (fun tool => Datum.rational (input.correctionFee point tool)))++
      rawContract contract++[.rational budget]
    refine ⟨rest.flatMap encodeDatum,?_⟩
    rw [show firstNumbers input contract=incidenceNumbers I++[E.alphabetSize] from dite_eq_left positive,
      show firstValue input budget=E.priorOne from dite_eq_left positive]
    rw [afterTools_remaining,remaining_data]
    have experiments : (List.finRange I.stageCount).flatMap (fun point => rawExperiment (input.experiment point))=
        rawExperiment E++(List.finRange I.stageCount).tail.flatMap (fun point => rawExperiment (input.experiment point)) := by
      change (List.finRange I.compatibility.length).flatMap (fun point => rawExperiment (input.experiment point))=_
      rw [finRange_head (show 0<I.compatibility.length from positive),List.flatMap_cons]
      rfl
    rw [experiments,incidence_numbers]
    simp only [NatPrefix.naturals,List.flatMap_append,
      List.flatMap_map,List.flatMap_cons,List.flatMap_nil,List.nil_append,List.cons_append,
      rawExperiment,rest,E,stage,List.append_assoc]
  · have zero : I.stageCount=0 := by omega
    have noCompatibility : I.compatibility=[] := by
      have length : I.compatibility.length=0 := zero
      exact List.length_eq_zero_iff.mp length
    refine ⟨[],?_⟩
    rw [show firstNumbers input contract=contractNumbers contract from dite_eq_right positive,
      show firstValue input budget=budget from dite_eq_right positive]
    rw [afterTools_remaining,remaining_data,noCompatibility]
    have noStages : List.finRange I.compatibility.length=[] := by
      apply List.length_eq_zero_iff.mp
      rw [List.length_finRange]
      change I.stageCount=0
      exact zero
    simp only [contract_numbers,Instance.stageCount,noStages,List.flatMap_nil,List.nil_append,
      List.map_nil,List.append_nil,NatPrefix.naturals,List.flatMap_append,List.flatMap_map,
      List.flatMap_cons,List.append_assoc]

theorem firstNumbers_nonempty (input : StatisticalInput I) (contract : Contract I) :
    firstNumbers input contract≠[] := by
  unfold firstNumbers
  split
  · exact List.append_ne_nil_of_right_ne_nil _ (by simp)
  · simp [contractNumbers]

theorem firstNumbers_length_le (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    (NatPrefix.naturals (firstNumbers input contract)).length≤(preparationInput input contract budget).length := by
  obtain ⟨suffix,shape⟩:=afterTools_split input contract budget
  have sub : (NJ.afterTools input contract budget).length≤(preparationInput input contract budget).length := by
    change (((preparationData input contract budget).drop 2).flatMap encodeDatum++[true]).length≤
      (encode (preparationData input contract budget)).length
    have pieces:=List.take_append_drop 2 (preparationData input contract budget)
    have encoded:=congrArg (fun data : List Datum => data.flatMap encodeDatum) pieces
    simp only [List.flatMap_append,List.length_append,encode] at encoded ⊢
    have lengths:=congrArg List.length encoded
    simp only [List.length_append] at lengths
    omega
  rw [shape] at sub
  simp only [List.length_append] at sub
  omega

end RootB234.PrepEntry.FirstRaw
