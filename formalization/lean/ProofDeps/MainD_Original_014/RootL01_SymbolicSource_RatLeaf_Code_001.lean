module

public import Common.PSTR_WordBool_RatInputAPI_093
public import PaperProofs.Common.CompactPriceClaims

/-! Actual prefix-expression rational leaf appender.  The source reads a
canonical signed packet on15, restores15 and7, and prepends the ORIGINAL
natural0/rational datum bytes to arbitrary old13.  It does not receive an
Expr or a host-produced output list as executable input.

The existing collector temporarily pushes TRUE on13.  A real pop at the
otherwise unused collect4 label removes that owned cell before either
formatter runs.  No outer list count or footer is inserted into a leaf. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootL01.SymbolicSource.RatLeaf

open Turing
open PaperProofs.Common.Native
open PSTRWordVM PSTRWordBool RationalControllerComputation


abbrev Label := RatInput.Encoder.Label
abbrev Store (C : Type*) := RatInput.Encoder.Store C
abbrev Statement (C : Type*) := RatInput.Encoder.Statement C
abbrev State (C : Type*) := RatInput.Encoder.State C
abbrev Bank := RatInput.Stack → List Bool

variable {C : Type*}

def collectLabel (point : RatInput.Label) : Label := .collect point
abbrev reverseNumLabel := RatInput.Encoder.reverseNumLabel
abbrev reverseDenLabel := RatInput.Encoder.reverseDenLabel
abbrev denLabel := RatInput.Encoder.denLabel
abbrev numLabel := RatInput.Encoder.numLabel
abbrev exchange := RatInput.Encoder.exchange
abbrev reverseRoles := RatInput.Encoder.reverseRoles
abbrev formatRoles := RatInput.Encoder.formatRoles

def leafPrefix : List Bool := encodeDatum (.natural 0)

def finishBody : Statement C :=
  .push 13 (fun memory => PSTRSymbolicNaturalExport.positive memory.1)
    (.push 13 (fun _ => true) (RatInput.Encoder.putPrefix leafPrefix (.goto (fun _ => .done))))

def program (caller : Statement C) : Label → Statement C
  | .collect point => if point=4 then .pop 13 (fun memory _ => memory)
      (.goto (fun _ => .reverseNum)) else
      LabelMap.statement collectLabel (StoreIso.statement (exchange C)
        (RatInput.program (C:=C × WordNatIO.Store) .halt point))
  | .reverseNum => LabelMap.statement reverseNumLabel (StackIso.statement (reverseRoles false)
      (RatOutput.program (C:=C × RatInput.Store) .halt 7))
  | .reverseDen => LabelMap.statement reverseDenLabel (StackIso.statement (reverseRoles true)
      (RatOutput.program (C:=C × RatInput.Store) .halt 7))
  | .den point => LabelMap.statement denLabel (StackIso.statement (formatRoles true)
      (WordNatIO.callerProgram (C:=C × RatInput.Store) .halt point))
  | .num point => LabelMap.statement numLabel (StackIso.statement (formatRoles false)
      (WordNatIO.callerProgram (C:=C × RatInput.Store) .halt point))
  | .finish => finishBody
  | .done => caller

def collectConfiguration (before : RatInput.State (C × WordNatIO.Store)) : State C :=
  LabelMap.configuration collectLabel (StoreIso.configuration (exchange C) before)

abbrev reverseConfiguration := @RatInput.Encoder.reverseConfiguration
abbrev formatConfiguration := @RatInput.Encoder.formatConfiguration

theorem collect_path (caller : Statement C) (trace : List (RatInput.State (C × WordNatIO.Store)))
    (before final : RatInput.State (C × WordNatIO.Store))
    (first : trace.head? = some before)
    (chain : trace.IsChain (fun a b => TM2.step (RatInput.program .halt) a = some b))
    (last : trace.getLast? = some final) (active : final.l = some 4) :
    (trace.map collectConfiguration).head? = some (collectConfiguration before) ∧
    (trace.map collectConfiguration).IsChain (fun a b => TM2.step (program caller) a = some b) ∧
    (trace.map collectConfiguration).getLast? = some (collectConfiguration final) := by
  let isoProgram := StoreIso.machine (exchange C) (RatInput.program .halt)
  have iso := StoreIso.actual_path_on (exchange C) (RatInput.program .halt) isoProgram
    trace before final first chain last (by intro current member point selected; rfl)
  have proper := NativeMulLink.no_early_halt_port isoProgram 4 rfl _ _ iso.2.1 iso.2.2.1 active
  have mapped := LabelMap.actual_path_on collectLabel isoProgram (program caller)
    _ _ _ iso.1 iso.2.1 iso.2.2.1 (by
      intro current member point selected
      have notFour : point ≠ 4 := by intro same; subst point; exact proper current member selected
      simp only [collectLabel, program, notFour, ite_false]
      rfl)
  have maps : (trace.map (StoreIso.configuration (exchange C))).map
      (LabelMap.configuration collectLabel) = trace.map collectConfiguration := by
    rw [List.map_map]; rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem reverse_path (caller : Statement C) (second : Bool)
    (background : Bank) (context : C × RatInput.Store) (word : List Bool)
    (memory : WordNatIO.Store) (right counter target : List Bool) :
    let trace := RatOutput.reverseTrace background context word memory right counter target
    (trace.map (reverseConfiguration second)).head? = some (reverseConfiguration second
      (RatOutput.state background 7 context memory right word counter target)) ∧
    (trace.map (reverseConfiguration second)).IsChain (fun a b => TM2.step (program caller) a = some b) ∧
    (trace.map (reverseConfiguration second)).getLast? = some (reverseConfiguration second
      (RatOutput.state background 8 context (false,false) right [] counter (word.reverse ++ target))) := by
  let trace := RatOutput.reverseTrace background context word memory right counter target
  let roles := reverseRoles second
  let mapping := if second then reverseDenLabel else reverseNumLabel
  let isoProgram := fun point => StackIso.statement roles (RatOutput.program (C:=C × RatInput.Store) .halt point)
  have first : (trace.map (StackIso.configuration roles)).head? = some (StackIso.configuration roles
      (RatOutput.state background 7 context memory right word counter target)) := by
    rw [List.head?_map,RatOutput.reverse_head,Option.map_some]
  have last : (trace.map (StackIso.configuration roles)).getLast? = some (StackIso.configuration roles
      (RatOutput.state background 8 context (false,false) right [] counter (word.reverse ++ target))) := by
    rw [List.getLast?_map,RatOutput.reverse_last,Option.map_some]
  have chain := StackIso.chain_configuration_on roles (RatOutput.program .halt) isoProgram trace
    (RatOutput.reverse_chain .halt background context word memory right counter target)
    (by intro current member point selected; rfl)
  have proper := NativeMulLink.no_early_halt_port isoProgram 8 rfl _ _ chain last rfl
  have mapped := LabelMap.actual_path_on mapping isoProgram (program caller) _ _ _ first chain last (by
    intro current member point selected
    obtain ⟨old,oldMember,same⟩ := List.mem_map.mp (List.mem_of_mem_dropLast member)
    have labels := RatInput.Encoder.reverse_labels background context word memory right counter target old oldMember
    have oldSelected : old.l = some point := by rw [←selected,←same]; rfl
    have seven : point = 7 := by
      rcases labels with seven | eight
      · exact Option.some.inj (oldSelected.symm.trans seven)
      · have equal : point = 8 := Option.some.inj (oldSelected.symm.trans eight)
        subst point
        exact False.elim (proper current member selected)
    subst point
    cases second <;> rfl)
  have maps : (trace.map (StackIso.configuration roles)).map (LabelMap.configuration mapping) =
      trace.map (reverseConfiguration second) := by rw [List.map_map]; rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem program_format (caller : Statement C) (second : Bool) (point : WordNatIO.Label) (proper : point ≠ 6) :
    program caller ((if second then denLabel else numLabel) point) =
      LabelMap.statement (if second then denLabel else numLabel)
        (StackIso.statement (formatRoles second) (WordNatIO.callerProgram (C:=C × RatInput.Store) .halt point)) := by
  cases second
  · simp only [Bool.false_eq_true,ite_false,numLabel,RatInput.Encoder.numLabel,proper,program]
  · simp only [ite_true,denLabel,RatInput.Encoder.denLabel,proper,ite_false,program]

theorem format_path (caller : Statement C) (second : Bool)
    (trace : List (WordNatIO.CallerState (C × RatInput.Store)))
    (before final : WordNatIO.CallerState (C × RatInput.Store))
    (first : trace.head? = some before)
    (chain : trace.IsChain (fun a b => TM2.step (WordNatIO.callerProgram .halt) a = some b))
    (last : trace.getLast? = some final) (active : final.l = some 6) :
    (trace.map (formatConfiguration second)).head? = some (formatConfiguration second before) ∧
    (trace.map (formatConfiguration second)).IsChain (fun a b => TM2.step (program caller) a = some b) ∧
    (trace.map (formatConfiguration second)).getLast? = some (formatConfiguration second final) := by
  let roles := formatRoles second
  let mapping := if second then denLabel else numLabel
  let isoProgram := fun point => StackIso.statement roles (WordNatIO.callerProgram (C:=C × RatInput.Store) .halt point)
  have isoFirst : (trace.map (StackIso.configuration roles)).head? = some (StackIso.configuration roles before) := by
    rw [List.head?_map,first,Option.map_some]
  have isoLast : (trace.map (StackIso.configuration roles)).getLast? = some (StackIso.configuration roles final) := by
    rw [List.getLast?_map,last,Option.map_some]
  have isoChain := StackIso.chain_configuration_on roles (WordNatIO.callerProgram .halt) isoProgram trace chain
    (by intro current member point selected; rfl)
  have proper := NativeMulLink.no_early_halt_port isoProgram 6 rfl _ _ isoChain isoLast active
  have mapped := LabelMap.actual_path_on mapping isoProgram (program caller) _ _ _ isoFirst isoChain isoLast (by
    intro current member point selected
    exact program_format caller second point (by intro same; subst point; exact proper current member selected))
  have maps : (trace.map (StackIso.configuration roles)).map (LabelMap.configuration mapping) =
      trace.map (formatConfiguration second) := by rw [List.map_map]; rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem finish_step (caller : Statement C) (memory : Store C) (contents : Bank) :
    TM2.step (program caller) ⟨some .finish,memory,contents⟩ =
      some ⟨some .done,memory,Function.update contents 13
        (leafPrefix ++ true :: PSTRSymbolicNaturalExport.positive memory.1 :: contents 13)⟩ := by
  change some (TM2.stepAux finishBody memory contents) = _
  simp only [finishBody,TM2.stepAux,RatInput.Encoder.putPrefix_stepAux,Function.update_self,Function.update_idem]

theorem strip_step (caller : Statement C) (memory : Store C) (contents : Bank) (output : List Bool)
    (owned : contents 13 = true :: output) :
    TM2.step (program caller) ⟨some (.collect 4),memory,contents⟩ =
      some ⟨some .reverseNum,memory,Function.update contents 13 output⟩ := by
  simp only [program,ite_true,TM2.step,TM2.stepAux,owned,List.tail_cons]

end RootL01.SymbolicSource.RatLeaf
