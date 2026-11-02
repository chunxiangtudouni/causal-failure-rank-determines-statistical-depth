module

public import PSTR_WordBool_WordOutput_Code_001

/-! Static transports of the actual original packet collector and the
arbitrary-base formatter suffix. No getter/reverse/formatter is rebuilt. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.WordOutput

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

def smallLabel (point : RatInput.Label) : Label := collectLabel (RatInput.Encoder.collectLabel point)

theorem labels_comp (body : TM2.Stmt RatInput.Alphabet RatInput.Label (Store C)) :
    LabelMap.statement collectLabel (LabelMap.statement RatInput.Encoder.collectLabel body)=
      LabelMap.statement smallLabel body := by
  induction body with
  | push slot value tail ih => exact congrArg (TM2.Stmt.push slot value) ih
  | peek slot value tail ih => exact congrArg (TM2.Stmt.peek slot value) ih
  | pop slot value tail ih => exact congrArg (TM2.Stmt.pop slot value) ih
  | load value tail ih => exact congrArg (TM2.Stmt.load value) ih
  | branch test yes no ihYes ihNo => exact congrArg₂ (TM2.Stmt.branch test) ihYes ihNo
  | goto target => rfl
  | halt => rfl

theorem program_collect (caller : Statement C) (point : RatInput.Label) (proper : point≠4) :
    program caller (smallLabel point)=LabelMap.statement smallLabel
      (StoreIso.statement (RatInput.Encoder.exchange (C × Bool × Bool))
        (RatInput.program (C:=(C × Bool × Bool) × WordNatIO.Store) .halt point)) := by
  unfold smallLabel
  rw [RatInput.Encoder.collectLabel]
  simp only [proper,ite_false]
  change LabelMap.statement collectLabel (LabelMap.statement RatInput.Encoder.collectLabel _)=_
  exact labels_comp _

theorem collect_path (caller : Statement C)
    (trace : List (RatInput.State ((C × Bool × Bool) × WordNatIO.Store)))
    (before final : RatInput.State ((C × Bool × Bool) × WordNatIO.Store))
    (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b=>TM2.step (RatInput.program .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some 4) :
    let transform:=fun old=>LabelMap.configuration smallLabel
      (StoreIso.configuration (RatInput.Encoder.exchange (C × Bool × Bool)) old)
    (trace.map transform).head?=some (transform before) ∧
    (trace.map transform).IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
    (trace.map transform).getLast?=some (transform final) := by
  let exchange:=RatInput.Encoder.exchange (C × Bool × Bool)
  let isoProgram:=StoreIso.machine exchange (RatInput.program .halt)
  have iso:=StoreIso.actual_path_on exchange (RatInput.program .halt) isoProgram trace before final first chain last
    (by intro current member point selected;rfl)
  have proper:=NativeMulLink.no_early_halt_port isoProgram 4 rfl _ _ iso.2.1 iso.2.2.1 active
  have mapped:=LabelMap.actual_path_on smallLabel isoProgram (program caller) _ _ _ iso.1 iso.2.1 iso.2.2.1 (by
    intro current member point selected
    exact program_collect caller point (by intro same;subst point;exact proper current member selected))
  have maps : (trace.map (StoreIso.configuration exchange)).map (LabelMap.configuration smallLabel)=
      trace.map (fun old=>LabelMap.configuration smallLabel (StoreIso.configuration exchange old)) := by
    rw [List.map_map]
    rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem collect_configuration (background : Stack → List Bool) (point : RatInput.Label)
    (context : C) (hit map : Bool) (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (source scratch numRev denRev numerator denominator raw left counter : List Bool) :
    LabelMap.configuration smallLabel (StoreIso.configuration (RatInput.Encoder.exchange (C × Bool × Bool))
      (RatInput.state (RatInput.Encoder.bank background [] [] [] [] numerator denominator [] left counter)
        point ((context,hit,map),formatter) memory source scratch numRev denRev raw))=
      (⟨some (smallLabel point),(((context,hit,map),memory),formatter),
        RatInput.Encoder.bank background source scratch numRev denRev numerator denominator raw left counter⟩:State C) := by
  change (⟨some (smallLabel point),(((context,hit,map),memory),formatter),_⟩:State C)=_
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem actual_collect (caller : Statement C) (background : Stack → List Bool)
    (context : C) (hit map : Bool) (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (negative : Bool) (num den source scratch : List Bool) :
    ∃ trace : List (State C),
      trace.head?=some ⟨some (.collect (.collect 0)),(((context,hit,map),memory),formatter),
        RatInput.Encoder.bank background (PSTRSymbolicRatExport.packet negative num den source) scratch [] [] [] [] [] [] []⟩ ∧
      trace.IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
      trace.getLast?=some ⟨some .prepare,
        (((context,hit,map),(PSTRSymbolicNaturalExport.finalBit (RatOutput.outputLeft negative num den) false,true,negative)),formatter),
        RatInput.Encoder.bank background (PSTRSymbolicRatExport.packet negative num den source) scratch
          num.reverse den.reverse [] [] [true] [] []⟩ ∧
      trace.length≤3*(num.length+den.length)+11 := by
  let background':=RatInput.Encoder.bank background [] [] [] [] [] [] [] [] []
  obtain ⟨trace,first,chain,last,count,_stable⟩:=RatInput.actual_collect .halt background'
    ((context,hit,map),formatter) memory negative num den source scratch [] [] []
  have path:=collect_path caller trace _ _ first chain last rfl
  refine ⟨_,?_,path.2.1,?_,?_⟩
  · rw [path.1]
    dsimp only [background']
    rw [collect_configuration]
    rfl
  · simp only [List.append_nil] at path
    rw [path.2.2]
    dsimp only [background']
    rw [collect_configuration]
    rfl
  · simpa only [List.length_map] using count

theorem program_suffix (caller : Statement C) (point : RatInput.Encoder.Label) (proper : point≠.done) :
    program caller (suffixLabel point)=LabelMap.statement suffixLabel
      (RatInput.Encoder.program (C:=C × Bool × Bool) .halt point) := by
  simp only [suffixLabel,proper,ite_false,program]

theorem suffix_path (caller : Statement C) (trace : List (RatInput.Encoder.State (C × Bool × Bool)))
    (before final : RatInput.Encoder.State (C × Bool × Bool)) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b=>TM2.step (RatInput.Encoder.program .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some .done) :
    (trace.map suffixConfiguration).head?=some (suffixConfiguration before) ∧
    (trace.map suffixConfiguration).IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
    (trace.map suffixConfiguration).getLast?=some (suffixConfiguration final) := by
  have proper:=NativeMulLink.no_early_halt_port (RatInput.Encoder.program .halt) .done rfl trace final chain last active
  have mapped:=LabelMap.actual_path_on suffixLabel (RatInput.Encoder.program .halt) (program caller)
    trace before final first chain last (by
      intro current member point selected
      exact program_suffix caller point (by intro same;subst point;exact proper current member selected))
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem actual_suffix (caller : Statement C) (background : Stack → List Bool) (context : C) (hit map : Bool)
    (bit flag negative : Bool) (formatter : WordNatIO.Store) (num den source scratch raw : List Bool) :
    ∃ trace : List (State C),
      trace.head?=some ⟨some (.suffix .reverseNum),(((context,hit,map),(bit,flag,negative)),formatter),
        RatInput.Encoder.bank background source scratch num.reverse den.reverse [] [] raw [] []⟩ ∧
      trace.IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
      trace.getLast?=some ⟨some .trim,(((context,hit,map),(bit,flag,negative)),(false,false)),
        RatInput.Encoder.bank background source scratch [] [] [] []
          (RatInput.Encoder.prefixBits++true::negative::(encodeNat (PSTRTMIncrement009.valueDigits num)++
            encodeNat (PSTRTMIncrement009.valueDigits den)++raw)) [] []⟩ ∧
      trace.length≤5*(num.length+den.length)+24 := by
  obtain ⟨trace,first,chain,last,count⟩:=RatPair.Serializer.old_suffix background (context,hit,map)
    bit flag negative formatter num den source scratch raw
  have path:=suffix_path caller trace _ _ first chain last rfl
  refine ⟨trace.map suffixConfiguration,path.1,path.2.1,path.2.2,?_⟩
  simpa only [List.length_map] using count

end PaperProofs.Common.Native.PSTRWordBool.WordOutput
