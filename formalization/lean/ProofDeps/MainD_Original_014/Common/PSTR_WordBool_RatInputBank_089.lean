module

public import Common.PSTR_WordBool_RatInputPorts_088

/-! The encoder's physical work bank and the exact collector/finish
boundaries. Unowned stacks retain the supplied finite background. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatInput.Encoder

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

def bank (background : RatInput.Stack→List Bool)
    (source scratch numRev denRev numerator denominator raw left counter : List Bool) : RatInput.Stack→List Bool :=
  fun slot=>if slot=15 then source else if slot=7 then scratch else if slot=3 then numRev else if slot=4 then denRev
    else if slot=5 then numerator else if slot=6 then denominator else if slot=13 then raw else if slot=14 then left
    else if slot=12 then counter else background slot

theorem collect_configuration (background : RatInput.Stack→List Bool) (point : RatInput.Label)
    (context : C) (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (source scratch numRev denRev numerator denominator raw left counter : List Bool) :
    collectConfiguration (RatInput.state (bank background [] [] [] [] numerator denominator [] left counter)
      point (context,formatter) memory source scratch numRev denRev raw)=
    (⟨some (collectLabel point),((context,memory),formatter),
      bank background source scratch numRev denRev numerator denominator raw left counter⟩:State C) := by
  unfold collectConfiguration LabelMap.configuration StoreIso.configuration RatInput.state
  simp only [Option.map_some]
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem actual_collect_bank (caller : Statement C) (background : RatInput.Stack→List Bool)
    (context : C) (memory : RatInput.Store) (formatter : WordNatIO.Store) (negative : Bool)
    (num den source scratch numerator denominator raw left counter : List Bool) :
    ∃ trace : List (State C),
      trace.head?=some ⟨some (.collect 0),((context,memory),formatter),
        bank background (PSTRSymbolicRatExport.packet negative num den source) scratch [] [] numerator denominator raw left counter⟩ ∧
      trace.IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
      trace.getLast?=some ⟨some .reverseNum,
        ((context,(PSTRSymbolicNaturalExport.finalBit (RatOutput.outputLeft negative num den) false,true,negative)),formatter),
        bank background (PSTRSymbolicRatExport.packet negative num den source) scratch num.reverse den.reverse numerator denominator
          (true::raw) left counter⟩ ∧
      trace.length≤3*(num.length+den.length)+11 := by
  let background':=bank background [] [] [] [] numerator denominator [] left counter
  obtain ⟨trace,first,chain,last,count,_stable⟩:=RatInput.actual_collect .halt background'
    (context,formatter) memory negative num den source scratch [] [] raw
  have path:=collect_path caller trace _ _ first chain last rfl
  refine ⟨trace.map collectConfiguration,?_,path.2.1,?_,?_⟩
  · rw [path.1,collect_configuration]
    rfl
  · simp only [List.append_nil] at path
    rw [path.2.2,collect_configuration]
    rfl
  · simpa only [List.length_map] using count

theorem reverse_num_bank (background : RatInput.Stack→List Bool)
    (source scratch numRev denRev numerator denominator raw left counter word target : List Bool) :
    reverseCells (bank background source scratch numRev denRev numerator denominator raw left counter) false word target=
      bank background source scratch word denRev target denominator raw left counter := by
  funext slot;fin_cases slot <;> rfl

theorem reverse_den_bank (background : RatInput.Stack→List Bool)
    (source scratch numRev denRev numerator denominator raw left counter word target : List Bool) :
    reverseCells (bank background source scratch numRev denRev numerator denominator raw left counter) true word target=
      bank background source scratch numRev word numerator target raw left counter := by
  funext slot;fin_cases slot <;> rfl

theorem format_num_bank (background : RatInput.Stack→List Bool)
    (source scratch numRev denRev numerator denominator raw left counter word newLeft output newCounter : List Bool) :
    formatCells (bank background source scratch numRev denRev numerator denominator raw left counter) false word newLeft output newCounter=
      bank background source scratch numRev denRev word denominator output newLeft newCounter := by
  funext slot;fin_cases slot <;> rfl

theorem format_den_bank (background : RatInput.Stack→List Bool)
    (source scratch numRev denRev numerator denominator raw left counter word newLeft output newCounter : List Bool) :
    formatCells (bank background source scratch numRev denRev numerator denominator raw left counter) true word newLeft output newCounter=
      bank background source scratch numRev denRev numerator word output newLeft newCounter := by
  funext slot;fin_cases slot <;> rfl

theorem finish_step (caller : Statement C) (memory : Store C) (contents : RatInput.Stack→List Bool) :
    TM2.step (program caller) ⟨some .finish,memory,contents⟩=
      some ⟨some .done,memory,Function.update contents 13
        (prefixBits++true::PSTRSymbolicNaturalExport.positive memory.1::contents 13)⟩ := by
  change some (TM2.stepAux finishBody memory contents)=_
  simp only [finishBody,TM2.stepAux,putPrefix_stepAux,Function.update_self,Function.update_idem]

theorem bank_update_raw (background : RatInput.Stack→List Bool)
    (source scratch numRev denRev numerator denominator raw left counter output : List Bool) :
    Function.update (bank background source scratch numRev denRev numerator denominator raw left counter) 13 output=
      bank background source scratch numRev denRev numerator denominator output left counter := by
  funext slot;fin_cases slot <;> rfl

end PaperProofs.Common.Native.PSTRWordBool.RatInput.Encoder
