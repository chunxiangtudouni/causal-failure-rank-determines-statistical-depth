module

public import Paid.RootD27Core_CopySavedResult_068

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 950000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open PDLower.CoreSearch

def selectedMetadataCommands (upper isExact : Bool) : List HeaderCommand :=
  [.copy 24 (multiplierSlot upper),.copy 25 (statisticsSlot upper),
   .copy 26 (statisticsSlot upper+1),.copy 27 (statisticsSlot upper+2),
   .constant 13 (.natural (if isExact then 0 else 1))]

def selectedMetadataValues (values : ℕ→Cell) (upper isExact : Bool) : ℕ→Cell :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update values (multiplierSlot upper) (values 24)) (statisticsSlot upper) (values 25))
      (statisticsSlot upper+1) (values 26)) (statisticsSlot upper+2) (values 27))
        13 (.natural (if isExact then 0 else 1))

def selectedMetadataRegion (upper : Bool) : Finset ℕ :=
  {13,multiplierSlot upper,statisticsSlot upper,statisticsSlot upper+1,statisticsSlot upper+2}

theorem selectedMetadata_valid (upper isExact : Bool) :
    ∀ command∈selectedMetadataCommands upper isExact,command.Valid := by
  cases upper <;> simp [selectedMetadataCommands,HeaderCommand.Valid,multiplierSlot,statisticsSlot,headerWords]

theorem selectedMetadata_targets (upper isExact : Bool) :
    ∀ command∈selectedMetadataCommands upper isExact,commandTarget command∈scalarRegion := by
  cases upper <;> simp [selectedMetadataCommands,commandTarget,scalarRegion,multiplierSlot,statisticsSlot]

theorem selectedMetadata_length (upper isExact : Bool) :
    (headerCode (selectedMetadataCommands upper isExact)).length=28 := by
  cases upper <;> rfl

theorem selectedMetadata_eval (values : ℕ→Cell) (upper isExact : Bool) :
    headerEval (selectedMetadataCommands upper isExact) values=some (selectedMetadataValues values upper isExact) := by
  cases upper <;> simp [selectedMetadataCommands,selectedMetadataValues,multiplierSlot,statisticsSlot,
    headerEval,HeaderCommand.eval]

theorem selectedMetadata_outside (values : ℕ→Cell) (upper isExact : Bool) (query : ℕ)
    (outside : query∉selectedMetadataRegion upper) :
    selectedMetadataValues values upper isExact query=values query := by
  simp only [selectedMetadataRegion,Finset.mem_insert,Finset.mem_singleton,not_or] at outside
  obtain ⟨q13,qPrice,qObs,qRep,qRisk⟩:=outside
  simp only [selectedMetadataValues,Function.update_of_ne q13,Function.update_of_ne qRisk,
    Function.update_of_ne qRep,Function.update_of_ne qObs,Function.update_of_ne qPrice]

/-- Refine an actual Header48 scalar run by its computed final values.
This proves preservation of the opposite metadata even though the
general intermediate scalar frame permits writes anywhere in13..42. -/
theorem header_final_values_region {before after : State} {values next : ℕ→Cell} (region : Finset ℕ)
    (header : Header before 0 values) (afterHeader : Header after 0 next)
    (memory : MemoryFrame scalarRegion before after ∧ HeaderMemory before after 0)
    (unchanged : ∀ slot<headerWords,slot∉region→next slot=values slot) :
    RegionMemory before after region := by
  refine ⟨?_,?_,?_,memory.2.2.2⟩
  · intro query outside
    by_cases inside : query<headerWords
    · have old:=header.value query inside
      have new:=afterHeader.value query inside
      simp only [Nat.zero_add] at old new
      exact new.trans ((unchanged query inside outside).trans old.symm)
    · apply memory.1.1
      apply scalarRegion_outside
      right
      unfold headerWords at inside
      omega
  · rw [memory.2.2.1]
    exact Finset.subset_union_left
  · rw [memory.2.2.1]

/-- Copy the real midpoint lambda/statistics24..27 to the chosen source
buffer metadata and actually store the branch tag. Length22/23 and the
opposite buffer metadata are outside the proved final write region. -/
theorem selected_metadata_actual (program : Program) (input : List Cell) (before : State)
    (values : ℕ→Cell) (upper isExact : Bool) (header : Header before 0 values)
    (fresh : before.register .fresh=.natural 0)
    (fetched : FetchesCode program before.pc (headerCode (selectedMetadataCommands upper isExact))) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤435 ∧
      Header after 0 (selectedMetadataValues values upper isExact) ∧ after.register .fresh=.natural 0 ∧
      after.pc=before.pc+28 ∧ RegionMemory before after (selectedMetadataRegion upper) ∧
      (∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+28) ∧
      peakCells trace≤workingCells before := by
  obtain ⟨trace,after,head,last,chain,cost,afterHeader,afterFresh,pc,memory,scope⟩:=
    scalar_commands_located_actual (selectedMetadataCommands upper isExact) program input before values
      (selectedMetadataValues values upper isExact) (selectedMetadata_valid upper isExact)
      (selectedMetadata_targets upper isExact) header fresh (selectedMetadata_eval values upper isExact) fetched
  have finalMemory:=memory after (List.mem_of_getLast? last)
  have precise:=header_final_values_region (selectedMetadataRegion upper) header afterHeader finalMemory
    (fun slot _inside outside=>selectedMetadata_outside values upper isExact slot outside)
  have allSpace : ∀ state∈trace,workingCells state≤workingCells before := by
    intro state member
    have fields:=memory state member
    unfold workingCells
    rw [fields.2.2.1,fields.2.2.2]
  refine ⟨trace,after,head,last,chain,?_,afterHeader,afterFresh,?_,precise,memory,?_,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace⟩
  · simpa only [selectedMetadata_length] using cost
  · simpa only [selectedMetadata_length] using pc
  · simpa only [selectedMetadata_length] using scope

end RootD27.Core
