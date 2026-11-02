module

public import Common.PSTR_WordBool_RatInputEncoderCode_086

/-! Static transport of the actual collection, reversal and formatter
paths into the one encoder. All return ports remain unexecuted. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatInput.Encoder

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

theorem program_collect (caller : Statement C) (point : RatInput.Label) (proper : point≠4) :
    program caller (collectLabel point) = LabelMap.statement collectLabel
      (StoreIso.statement (exchange C) (RatInput.program (C:=C×WordNatIO.Store) .halt point)) := by
  simp only [collectLabel,proper,ite_false,program]

theorem collect_path (caller : Statement C) (trace : List (RatInput.State (C×WordNatIO.Store)))
    (before final : RatInput.State (C×WordNatIO.Store))
    (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b=>TM2.step (RatInput.program .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some 4) :
    (trace.map collectConfiguration).head?=some (collectConfiguration before) ∧
    (trace.map collectConfiguration).IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
    (trace.map collectConfiguration).getLast?=some (collectConfiguration final) := by
  let isoProgram:=StoreIso.machine (exchange C) (RatInput.program .halt)
  have iso:=StoreIso.actual_path_on (exchange C) (RatInput.program .halt) isoProgram trace before final
    first chain last (by intro current member point selected;rfl)
  have proper:=NativeMulLink.no_early_halt_port isoProgram 4 rfl
    (trace.map (StoreIso.configuration (exchange C))) (StoreIso.configuration (exchange C) final)
    iso.2.1 iso.2.2.1 active
  have mapped:=LabelMap.actual_path_on collectLabel isoProgram (program caller)
    (trace.map (StoreIso.configuration (exchange C))) _ _ iso.1 iso.2.1 iso.2.2.1 (by
      intro current member point selected
      exact program_collect caller point (by intro same;subst point;exact proper current member selected))
  have maps : (trace.map (StoreIso.configuration (exchange C))).map (LabelMap.configuration collectLabel)=
      trace.map collectConfiguration := by rw [List.map_map];rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem reverse_labels (background : RatInput.Stack→List Bool) (context : C×RatInput.Store)
    (word : List Bool) (memory : WordNatIO.Store) (right counter target : List Bool) :
    ∀ current∈RatOutput.reverseTrace background context word memory right counter target,
      current.l=some 7 ∨ current.l=some 8 := by
  induction word generalizing memory target with
  | nil =>
    intro current member
    simp only [RatOutput.reverseTrace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  | cons bit later ih =>
    intro current member
    rcases List.mem_cons.mp member with rfl|remaining
    · exact Or.inl rfl
    · exact ih (true,bit) (bit::target) current remaining

theorem reverse_path (caller : Statement C) (second : Bool)
    (background : RatInput.Stack→List Bool) (context : C×RatInput.Store)
    (word : List Bool) (memory : WordNatIO.Store) (right counter target : List Bool) :
    let trace:=RatOutput.reverseTrace background context word memory right counter target
    (trace.map (reverseConfiguration second)).head?=some (reverseConfiguration second
      (RatOutput.state background 7 context memory right word counter target)) ∧
    (trace.map (reverseConfiguration second)).IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
    (trace.map (reverseConfiguration second)).getLast?=some (reverseConfiguration second
      (RatOutput.state background 8 context (false,false) right [] counter (word.reverse++target))) := by
  let trace:=RatOutput.reverseTrace background context word memory right counter target
  let roles:=reverseRoles second
  let mapping:=if second then reverseDenLabel else reverseNumLabel
  let isoProgram:=fun point=>StackIso.statement roles (RatOutput.program (C:=C×RatInput.Store) .halt point)
  have first : (trace.map (StackIso.configuration roles)).head?=some (StackIso.configuration roles
      (RatOutput.state background 7 context memory right word counter target)) := by
    rw [List.head?_map,RatOutput.reverse_head,Option.map_some]
  have last : (trace.map (StackIso.configuration roles)).getLast?=some (StackIso.configuration roles
      (RatOutput.state background 8 context (false,false) right [] counter (word.reverse++target))) := by
    rw [List.getLast?_map,RatOutput.reverse_last,Option.map_some]
  have chain:=StackIso.chain_configuration_on roles (RatOutput.program .halt) isoProgram trace
    (RatOutput.reverse_chain .halt background context word memory right counter target)
    (by intro current member point selected;rfl)
  have proper:=NativeMulLink.no_early_halt_port isoProgram 8 rfl _ _ chain last rfl
  have mapped:=LabelMap.actual_path_on mapping isoProgram (program caller) _ _ _ first chain last (by
    intro current member point selected
    obtain ⟨old,oldMember,same⟩:=List.mem_map.mp (List.mem_of_mem_dropLast member)
    have labels:=reverse_labels background context word memory right counter target old oldMember
    have oldSelected : old.l=some point := by rw [←selected,←same];rfl
    have seven : point=7 := by
      rcases labels with seven|eight
      · exact Option.some.inj (oldSelected.symm.trans seven)
      · have equal : point=8:=Option.some.inj (oldSelected.symm.trans eight)
        subst point
        exact False.elim (proper current member selected)
    subst point
    cases second <;> rfl)
  have maps : (trace.map (StackIso.configuration roles)).map (LabelMap.configuration mapping)=
      trace.map (reverseConfiguration second) := by rw [List.map_map];rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem program_format (caller : Statement C) (second : Bool) (point : WordNatIO.Label) (proper : point≠6) :
    program caller ((if second then denLabel else numLabel) point)=
      LabelMap.statement (if second then denLabel else numLabel)
        (StackIso.statement (formatRoles second) (WordNatIO.callerProgram (C:=C×RatInput.Store) .halt point)) := by
  cases second
  · simp only [Bool.false_eq_true,ite_false,numLabel,proper,program]
  · simp only [ite_true,denLabel,proper,ite_false,program]

theorem format_path (caller : Statement C) (second : Bool)
    (trace : List (WordNatIO.CallerState (C×RatInput.Store)))
    (before final : WordNatIO.CallerState (C×RatInput.Store))
    (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b=>TM2.step (WordNatIO.callerProgram .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some 6) :
    (trace.map (formatConfiguration second)).head?=some (formatConfiguration second before) ∧
    (trace.map (formatConfiguration second)).IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
    (trace.map (formatConfiguration second)).getLast?=some (formatConfiguration second final) := by
  let roles:=formatRoles second
  let mapping:=if second then denLabel else numLabel
  let isoProgram:=fun point=>StackIso.statement roles (WordNatIO.callerProgram (C:=C×RatInput.Store) .halt point)
  have isoFirst : (trace.map (StackIso.configuration roles)).head?=some (StackIso.configuration roles before) := by
    rw [List.head?_map,first,Option.map_some]
  have isoLast : (trace.map (StackIso.configuration roles)).getLast?=some (StackIso.configuration roles final) := by
    rw [List.getLast?_map,last,Option.map_some]
  have isoChain:=StackIso.chain_configuration_on roles (WordNatIO.callerProgram .halt) isoProgram trace chain
    (by intro current member point selected;rfl)
  have proper:=NativeMulLink.no_early_halt_port isoProgram 6 rfl _ _ isoChain isoLast active
  have mapped:=LabelMap.actual_path_on mapping isoProgram (program caller) _ _ _ isoFirst isoChain isoLast (by
    intro current member point selected
    exact program_format caller second point (by intro same;subst point;exact proper current member selected))
  have maps : (trace.map (StackIso.configuration roles)).map (LabelMap.configuration mapping)=
      trace.map (formatConfiguration second) := by rw [List.map_map];rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

end PaperProofs.Common.Native.PSTRWordBool.RatInput.Encoder
