module

public import B23_4_RatWordPrep_SeqCmp_NatFieldCurrent_052

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.HeaderNat

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM

abbrev Store (C : Type*) := Header.Store (NatField.Store C)

inductive Label where
  | header : Fin 2 → Label
  | field : NatField.Label → Label
  | done
  deriving DecidableEq, Fintype
instance : Inhabited Label := ⟨.header 0⟩

abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def roles : RatInput.Stack ≃ RatInput.Stack := Equiv.swap 8 15

def fieldIso (C : Type*) : NatField.Store (Header.Store C) ≃ Store C :=
  StoreIso.exchange C Header.NativeMemory PSTRSymbolicNaturalExport.Store

def headerLabel (point : Fin 2) : Label := if point=1 then .field 0 else .header point

def fieldLabel (point : NatField.Label) : Label := if point=4 then .done else .field point

def program (caller : Statement C) : Label → Statement C
  | .header point => LabelMap.statement headerLabel (Header.program .halt point)
  | .field point => LabelMap.statement fieldLabel
    (StoreIso.statement (fieldIso C) (StackIso.statement roles (NatField.program .halt point)))
  | .done => caller

def headerCfg (before : Header.State (NatField.Store C)) : State C := LabelMap.configuration headerLabel before

def fieldCfg (before : NatField.State (Header.Store C)) : State C :=
  LabelMap.configuration fieldLabel (StoreIso.configuration (fieldIso C) (StackIso.configuration roles before))

def fieldStart (before : Header.State (NatField.Store C)) : NatField.State (Header.Store C) :=
  ⟨some 0,(fieldIso C).symm before.var,StackIso.slots roles.symm before.stk⟩

def entry (context : C) (flags : PSTRSymbolicNaturalExport.Store) (background : RatInput.Stack → List Bool)
    (bits : List Bool) : State C := headerCfg (Header.entry (context,flags) background bits)

theorem shared (before : Header.State (NatField.Store C)) (active : before.l=some 1) :
    fieldCfg (fieldStart before)=headerCfg before := by
  cases before with
  | mk position memory contents =>
    change position=some 1 at active
    subst position
    change (⟨some (.field 0),fieldIso C ((fieldIso C).symm memory),
      StackIso.slots roles (StackIso.slots roles.symm contents)⟩ : State C)=⟨some (.field 0),memory,contents⟩
    rw [Equiv.apply_symm_apply]
    congr 1
    funext slot
    fin_cases slot <;> rfl

theorem header_path (caller : Statement C) (run : List (Header.State (NatField.Store C)))
    (before final : Header.State (NatField.Store C)) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (Header.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some 1) :
    (run.map headerCfg).head?=some (headerCfg before) ∧
    (run.map headerCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map headerCfg).getLast?=some (headerCfg final) := by
  have proper:=NativeMulLink.no_early_halt_port (Header.program .halt) 1 rfl run final chain last active
  have mapped:=LabelMap.actual_path_on headerLabel (Header.program .halt) (program caller)
    run before final first chain last (by
      intro current member point selected
      have notDone : point≠1 := by intro same; subst point; exact proper current member selected
      simp only [headerLabel,notDone,ite_false,program])
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem field_path (caller : Statement C) (run : List (NatField.State (Header.Store C)))
    (before final : NatField.State (Header.Store C)) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (NatField.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some 4) :
    (run.map fieldCfg).head?=some (fieldCfg before) ∧
    (run.map fieldCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map fieldCfg).getLast?=some (fieldCfg final) := by
  let old:=NatField.program (C := Header.Store C) .halt
  let stackProgram:=fun point => StackIso.statement roles (old point)
  let stackRun:=run.map (StackIso.configuration roles)
  have stackFirst : stackRun.head?=some (StackIso.configuration roles before) := by
    rw [List.head?_map,first,Option.map_some]
  have stackChain:=StackIso.chain_configuration_on roles old stackProgram run chain
    (by intro current member point selected; rfl)
  have stackLast : stackRun.getLast?=some (StackIso.configuration roles final) := by
    rw [List.getLast?_map,last,Option.map_some]
  let isoProgram:=StoreIso.machine (fieldIso C) stackProgram
  have iso:=StoreIso.actual_path_on (fieldIso C) stackProgram isoProgram stackRun _ _ stackFirst stackChain stackLast
    (by intro current member point selected; rfl)
  have proper:=NativeMulLink.no_early_halt_port isoProgram 4 rfl _ _ iso.2.1 iso.2.2.1 active
  have mapped:=LabelMap.actual_path_on fieldLabel isoProgram (program caller)
    _ _ _ iso.1 iso.2.1 iso.2.2.1 (by
      intro current member point selected
      have notDone : point≠4 := by intro same; subst point; exact proper current member selected
      simp only [fieldLabel,notDone,ite_false,program]
      rfl)
  have maps : ((run.map (StackIso.configuration roles)).map (StoreIso.configuration (fieldIso C))).map
      (LabelMap.configuration fieldLabel)=run.map fieldCfg := by
    simp only [List.map_map]
    rfl
  dsimp only [stackRun] at mapped
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

end B23_4_RatWordPrep.HeaderNat
