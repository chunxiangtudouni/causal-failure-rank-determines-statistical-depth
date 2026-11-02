module

public import PSTR_WordBool_RatDrop_Fields_002

/-! The parked result returns through the frozen076 actual reverse loop.
Only its fixed stack roles and labels are transported. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatDrop

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

def reverseConfiguration (before : RatOutput.State C) : State C:=
  LabelMap.configuration reverseLabel (StackIso.configuration reverseRoles before)

def reverseTrace (background : Stack→List Bool) (context : C) (word : List Bool)
    (memory : RatOutput.Store) (target : List Bool) : List (State C):=
  (RatOutput.reverseTrace (StackIso.slots reverseRoles.symm background) context word memory
    (background 13) (background 7) target).map reverseConfiguration

theorem reverse_configuration (background : Stack→List Bool) (point : RatOutput.Label)
    (context : C) (memory : RatOutput.Store) (word target : List Bool) :
    reverseConfiguration (RatOutput.state (StackIso.slots reverseRoles.symm background) point context memory
      (background 13) word (background 7) target)=state background (reverseLabel point) context memory target word := by
  unfold reverseConfiguration LabelMap.configuration StackIso.configuration RatOutput.state state
  simp only [Option.map_some]
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem reverse_head (background : Stack→List Bool) (context : C) (word : List Bool)
    (memory : RatOutput.Store) (target : List Bool) :
    (reverseTrace background context word memory target).head?=some (state background 9 context memory target word) := by
  rw [reverseTrace,List.head?_map,RatOutput.reverse_head,Option.map_some,reverse_configuration]
  rfl

theorem reverse_last (background : Stack→List Bool) (context : C) (word : List Bool)
    (memory : RatOutput.Store) (target : List Bool) :
    (reverseTrace background context word memory target).getLast?=
      some (state background 10 context (false,false) (word.reverse++target) []) := by
  rw [reverseTrace,List.getLast?_map,RatOutput.reverse_last,Option.map_some,reverse_configuration]
  rfl

theorem reverse_length (background : Stack→List Bool) (context : C) (word : List Bool)
    (memory : RatOutput.Store) (target : List Bool) :
    (reverseTrace background context word memory target).length=word.length+2 := by
  rw [reverseTrace,List.length_map,RatOutput.reverse_length]

private theorem old_reverse_labels (background : Stack→List Bool) (context : C)
    (word : List Bool) (memory : RatOutput.Store) (right counter target : List Bool) :
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

theorem reverse_chain (caller : Statement C) (background : Stack→List Bool) (context : C)
    (word : List Bool) (memory : RatOutput.Store) (target : List Bool) :
    (reverseTrace background context word memory target).IsChain (fun a b=>TM2.step (program caller) a=some b) := by
  let oldBackground:=StackIso.slots reverseRoles.symm background
  let trace:=RatOutput.reverseTrace oldBackground context word memory (background 13) (background 7) target
  let isoProgram:=fun point=>StackIso.statement reverseRoles (RatOutput.program (C:=C) .halt point)
  have chain:=StackIso.chain_configuration_on reverseRoles (RatOutput.program .halt) isoProgram trace
    (RatOutput.reverse_chain .halt oldBackground context word memory (background 13) (background 7) target)
    (by intro current member point selected;rfl)
  have last : (trace.map (StackIso.configuration reverseRoles)).getLast?=some (StackIso.configuration reverseRoles
      (RatOutput.state oldBackground 8 context (false,false) (background 13) [] (background 7) (word.reverse++target))) := by
    rw [List.getLast?_map,RatOutput.reverse_last,Option.map_some]
  have proper:=NativeMulLink.no_early_halt_port isoProgram 8 rfl _ _ chain last rfl
  have mapped:=LabelMap.chain_configuration_on reverseLabel isoProgram (program caller) _ chain (by
    intro current member point selected
    obtain ⟨old,oldMember,same⟩:=List.mem_map.mp (List.mem_of_mem_dropLast member)
    have labels:=old_reverse_labels oldBackground context word memory (background 13) (background 7) target old oldMember
    have oldSelected : old.l=some point:=by rw [←selected,←same];rfl
    have seven : point=7:=by
      rcases labels with seven|eight
      · exact Option.some.inj (oldSelected.symm.trans seven)
      · have equal : point=8:=Option.some.inj (oldSelected.symm.trans eight)
        subst point
        exact False.elim (proper current member selected)
    subst point
    rfl)
  change (trace.map (fun before=>LabelMap.configuration reverseLabel (StackIso.configuration reverseRoles before))).IsChain _
  simpa only [List.map_map,Function.comp_def] using mapped

theorem reverse_safe (background : Stack→List Bool) (context : C) (word : List Bool)
    (memory : RatOutput.Store) (target : List Bool) :
    ∀ current∈reverseTrace background context word memory target,
      Safe background context (outside background+word.length+target.length) current := by
  induction word generalizing memory target with
  | nil =>
    intro current member
    simp only [reverseTrace,RatOutput.reverseTrace,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    all_goals rw [reverse_configuration]
    all_goals apply safe_state
    all_goals simp only [List.length_nil,Nat.add_zero]
    all_goals exact Nat.le_refl _
  | cons bit later ih =>
    intro current member
    simp only [reverseTrace,RatOutput.reverseTrace,List.map_cons,List.mem_cons] at member
    rcases member with same|remaining
    · subst current
      rw [reverse_configuration]
      apply safe_state
      omega
    · apply safe_mono (ih (true,bit) (bit::target) current remaining)
      simp only [List.length_cons]
      omega

end PaperProofs.Common.Native.PSTRWordBool.RatDrop
