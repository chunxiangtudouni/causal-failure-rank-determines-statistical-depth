module

public import RootB234_PrepEntry_NatPublic_004
public import RootB234_PrepEntry_Alpha_006

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.NJ

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

abbrev Store (C : Type*) := HeaderNat.Store (C × Alpha.NativeMemory)

inductive Label where
  | stages : HeaderNat.Label → Label
  | tools : Fin 2 → Label
  | field : NatField.Label → Label
  | done
  deriving DecidableEq, Fintype
instance : Inhabited Label := ⟨.stages default⟩

abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def alphaIso (C : Type*) : Alpha.Store (HeaderNat.Store C) ≃ Store C where
  toFun := fun m => (((m.1.1.1,m.2),m.1.1.2),m.1.2)
  invFun := fun m => (((m.1.1.1,m.1.2),m.2),m.1.1.2)
  left_inv := by rintro ⟨⟨⟨context,flags⟩,header⟩,tools⟩; rfl
  right_inv := by rintro ⟨⟨⟨context,tools⟩,flags⟩,header⟩; rfl

def roles : RatInput.Stack ≃ RatInput.Stack := Equiv.swap 9 15

def stagesLabel (point : HeaderNat.Label) : Label := if point=.done then .tools 0 else .stages point

def toolsLabel (point : Fin 2) : Label := if point=1 then .field 0 else .tools point

def fieldLabel (point : NatField.Label) : Label := if point=4 then .done else .field point

def program (caller : Statement C) : Label → Statement C
  | .stages point => LabelMap.statement stagesLabel (HeaderNat.program .halt point)
  | .tools point => LabelMap.statement toolsLabel
    (StoreIso.statement (alphaIso C) (Alpha.program .halt point))
  | .field point => LabelMap.statement fieldLabel
    (StoreIso.statement (HeaderNat.fieldIso (C × Alpha.NativeMemory))
      (StackIso.statement roles (NatField.program .halt point)))
  | .done => caller

def stagesCfg (before : HeaderNat.State (C × Alpha.NativeMemory)) : State C :=
  LabelMap.configuration stagesLabel before

def alphaCfg (before : Alpha.State (HeaderNat.Store C)) : State C :=
  LabelMap.configuration toolsLabel (StoreIso.configuration (alphaIso C) before)

def alphaStart (before : HeaderNat.State (C × Alpha.NativeMemory)) : Alpha.State (HeaderNat.Store C) :=
  ⟨some 0,(alphaIso C).symm before.var,before.stk⟩

def fieldCfg (before : NatField.State (Header.Store (C × Alpha.NativeMemory))) : State C :=
  LabelMap.configuration fieldLabel (StoreIso.configuration (HeaderNat.fieldIso (C × Alpha.NativeMemory))
    (StackIso.configuration roles before))

def fieldStart (before : Alpha.State (HeaderNat.Store C)) : NatField.State (Header.Store (C × Alpha.NativeMemory)) :=
  ⟨some 0,(HeaderNat.fieldIso (C × Alpha.NativeMemory)).symm ((alphaCfg before).var),
    StackIso.slots roles.symm before.stk⟩

def entry (context : C) (bits : List Bool) : State C :=
  stagesCfg (Nat.entry (context,default) bits)

def callerContext (memory : Store C) : C := memory.1.1.1

theorem alpha_shared (before : HeaderNat.State (C × Alpha.NativeMemory)) (active : before.l=some .done) :
    alphaCfg (alphaStart before)=stagesCfg before := by
  cases before with
  | mk position memory contents =>
    change position=some .done at active
    subst position
    change (⟨some (.tools 0),alphaIso C ((alphaIso C).symm memory),contents⟩ : State C)=
      ⟨some (.tools 0),memory,contents⟩
    rw [Equiv.apply_symm_apply]

theorem field_shared (before : Alpha.State (HeaderNat.Store C)) (active : before.l=some 1) :
    fieldCfg (fieldStart before)=alphaCfg before := by
  cases before with
  | mk position memory contents =>
    change position=some 1 at active
    subst position
    change (⟨some (.field 0),HeaderNat.fieldIso (C × Alpha.NativeMemory)
      ((HeaderNat.fieldIso (C × Alpha.NativeMemory)).symm (alphaIso C memory)),
      StackIso.slots roles (StackIso.slots roles.symm contents)⟩ : State C)=
      ⟨some (.field 0),alphaIso C memory,contents⟩
    rw [Equiv.apply_symm_apply]
    congr 1
    funext slot
    fin_cases slot <;> rfl

theorem stages_path (caller : Statement C) (trace : List (HeaderNat.State (C × Alpha.NativeMemory)))
    (before final : HeaderNat.State (C × Alpha.NativeMemory)) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (HeaderNat.program .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some .done) :
    (trace.map stagesCfg).head?=some (stagesCfg before) ∧
    (trace.map stagesCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (trace.map stagesCfg).getLast?=some (stagesCfg final) := by
  have proper:=NativeMulLink.no_early_halt_port (HeaderNat.program .halt) .done rfl trace final chain last active
  have mapped:=LabelMap.actual_path_on stagesLabel (HeaderNat.program .halt) (program caller)
    trace before final first chain last (by
      intro current member point selected
      have notDone : point≠.done := by intro same; subst point; exact proper current member selected
      simp only [stagesLabel,notDone,ite_false,program])
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem alpha_path (caller : Statement C) (trace : List (Alpha.State (HeaderNat.Store C)))
    (before final : Alpha.State (HeaderNat.Store C)) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (Alpha.program .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some 1) :
    (trace.map alphaCfg).head?=some (alphaCfg before) ∧
    (trace.map alphaCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (trace.map alphaCfg).getLast?=some (alphaCfg final) := by
  let old:=Alpha.program (C := HeaderNat.Store C) .halt
  let isoProgram:=StoreIso.machine (alphaIso C) old
  have iso:=StoreIso.actual_path_on (alphaIso C) old isoProgram trace before final first chain last
    (by intro current member point selected; rfl)
  have proper:=NativeMulLink.no_early_halt_port isoProgram 1 rfl _ _ iso.2.1 iso.2.2.1 active
  have mapped:=LabelMap.actual_path_on toolsLabel isoProgram (program caller)
    _ _ _ iso.1 iso.2.1 iso.2.2.1 (by
      intro current member point selected
      have notDone : point≠1 := by intro same; subst point; exact proper current member selected
      simp only [toolsLabel,notDone,ite_false,program]
      rfl)
  have maps : (trace.map (StoreIso.configuration (alphaIso C))).map (LabelMap.configuration toolsLabel)=trace.map alphaCfg := by
    rw [List.map_map]
    rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem field_path (caller : Statement C) (run : List (NatField.State (Header.Store (C × Alpha.NativeMemory))))
    (before final : NatField.State (Header.Store (C × Alpha.NativeMemory))) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (NatField.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some 4) :
    (run.map fieldCfg).head?=some (fieldCfg before) ∧
    (run.map fieldCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map fieldCfg).getLast?=some (fieldCfg final) := by
  let old:=NatField.program (C := Header.Store (C × Alpha.NativeMemory)) .halt
  let stackProgram:=fun point => StackIso.statement roles (old point)
  let stackRun:=run.map (StackIso.configuration roles)
  have stackFirst : stackRun.head?=some (StackIso.configuration roles before) := by
    rw [List.head?_map,first,Option.map_some]
  have stackChain:=StackIso.chain_configuration_on roles old stackProgram run chain
    (by intro current member point selected; rfl)
  have stackLast : stackRun.getLast?=some (StackIso.configuration roles final) := by
    rw [List.getLast?_map,last,Option.map_some]
  let isoProgram:=StoreIso.machine (HeaderNat.fieldIso (C × Alpha.NativeMemory)) stackProgram
  have iso:=StoreIso.actual_path_on (HeaderNat.fieldIso (C × Alpha.NativeMemory)) stackProgram isoProgram stackRun _ _ stackFirst stackChain stackLast
    (by intro current member point selected; rfl)
  have proper:=NativeMulLink.no_early_halt_port isoProgram 4 rfl _ _ iso.2.1 iso.2.2.1 active
  have mapped:=LabelMap.actual_path_on fieldLabel isoProgram (program caller)
    _ _ _ iso.1 iso.2.1 iso.2.2.1 (by
      intro current member point selected
      have notDone : point≠4 := by intro same; subst point; exact proper current member selected
      simp only [fieldLabel,notDone,ite_false,program]
      rfl)
  have maps : ((run.map (StackIso.configuration roles)).map (StoreIso.configuration (HeaderNat.fieldIso (C × Alpha.NativeMemory)))).map
      (LabelMap.configuration fieldLabel)=run.map fieldCfg := by
    simp only [List.map_map]
    rfl
  dsimp only [stackRun] at mapped
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩


end RootB234.PrepEntry.NJ
