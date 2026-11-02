module

public import RootB234_PrepEntry_StageGuard_046

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.StageFront

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

abbrev Store (C : Type*) := FirstRaw.Store C
abbrev GuardContext (C : Type*) := FirstRaw.HeaderContext C × Fin 38

inductive Label where
  | header : Fin 2 → Label
  | guard : StageGuard.Label → Label
  | body : FirstRaw.Label → Label
  | select
  | fee : RawGetter.Label → Label
  | done
  deriving DecidableEq, Fintype
instance : Inhabited Label := ⟨.header 0⟩

abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

/-- The header native Bool is now owned by the stage guard. Its actual
control Fin38 and every other allocated register are kept verbatim. No
finite block is inserted or reset at this splice. -/
def guardIso (C : Type*) : StageGuard.Store (GuardContext C) ≃ Store C where
  toFun := fun value => (value.1.1,(value.1.2,value.2))
  invFun := fun value => ((value.1,value.2.1),value.2.2)
  left_inv := by rintro ⟨⟨context,control⟩,bit⟩; rfl
  right_inv := by rintro ⟨context,control,bit⟩; rfl

def feeRoles : RatInput.Stack ≃ RatInput.Stack := Equiv.swap 12 15

def headerLabel (point : Fin 2) : Label := if point=1 then .guard 0 else .header point
def guardLabel (point : StageGuard.Label) : Label := if point=1 ∨ point=2 then .body (.tools 0) else .guard point
def bodyLabel (point : FirstRaw.Label) : Label := if point=.done then .select else .body point
def feeLabel (point : RawGetter.Label) : Label := if point=.done then .done else .fee point

def program (caller : Statement C) : Label → Statement C
  | .header point => LabelMap.statement headerLabel (Header.program .halt point)
  | .guard point => LabelMap.statement guardLabel (StoreIso.statement (guardIso C) (StageGuard.program .halt .halt point))
  | .body point => LabelMap.statement bodyLabel (FirstRaw.program .halt point)
  | .select => .branch (fun memory => memory.2.2) (.goto (fun _ => .fee .boot)) (.goto (fun _ => .done))
  | .fee point => LabelMap.statement feeLabel (StoreIso.statement (FirstRaw.rawIso C)
      (StackIso.statement feeRoles (RawGetter.program .halt point)))
  | .done => caller

def headerCfg (before : Header.State (FirstRaw.HeaderContext C)) : State C := LabelMap.configuration headerLabel before
def guardCfg (before : StageGuard.State (GuardContext C)) : State C :=
  LabelMap.configuration guardLabel (StoreIso.configuration (guardIso C) before)
def bodyCfg (before : FirstRaw.State C) : State C := LabelMap.configuration bodyLabel before
def feeCfg (before : RawGetter.State (FirstRaw.RawContext C)) : State C :=
  LabelMap.configuration feeLabel (StoreIso.configuration (FirstRaw.rawIso C) (StackIso.configuration feeRoles before))

def entry (context : C) (background : RatInput.Stack → List Bool) (bits : List Bool) : State C :=
  headerCfg (Header.entry (((context,default),default),default) background bits)

def callerContext (memory : Store C) : C := FirstRaw.callerContext memory

theorem header_path (caller : Statement C) (run : List (Header.State (FirstRaw.HeaderContext C)))
    (before final : Header.State (FirstRaw.HeaderContext C)) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (Header.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some 1) :
    (run.map headerCfg).head?=some (headerCfg before) ∧
    (run.map headerCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map headerCfg).getLast?=some (headerCfg final) := by
  have proper:=NativeMulLink.no_early_halt_port (Header.program .halt) 1 rfl run final chain last active
  have mapped:=LabelMap.actual_path_on headerLabel (Header.program .halt) (program caller)
    run before final first chain last (by
      intro current member point selected
      have different : point≠1 := by intro equal; subst point; exact proper current member selected
      simp only [headerLabel,different,ite_false,program])
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem guard_path (caller : Statement C) (context : GuardContext C) (flag : Bool)
    (bank : RatInput.Stack → List Bool) (number : Nat)
    (physical : ∃ tail,bank 1=false::true::decide (number≠0)::tail) :
    let run:=StageGuard.actualTrace context flag bank number
    (run.map guardCfg).head?=some (guardCfg (StageGuard.before context flag bank)) ∧
    (run.map guardCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map guardCfg).getLast?=some (guardCfg (StageGuard.final context bank number)) := by
  have facts:=StageGuard.actual .halt .halt context flag bank number physical
  let old:=StageGuard.program (C := GuardContext C) .halt .halt
  let isoProgram:=StoreIso.machine (guardIso C) old
  have iso:=StoreIso.actual_path_on (guardIso C) old isoProgram _ _ _ facts.1 facts.2.1 facts.2.2.1
    (by intro current member point selected; rfl)
  have mapped:=LabelMap.actual_path_on guardLabel isoProgram (program caller) _ _ _ iso.1 iso.2.1 iso.2.2.1 (by
    intro current member point selected
    change current∈((StageGuard.actualTrace context flag bank number).map (StoreIso.configuration (guardIso C))).dropLast at member
    rw [←List.map_dropLast] at member
    obtain ⟨original,present,rfl⟩:=List.mem_map.mp member
    have same : original=StageGuard.before context flag bank := by
      change original∈[StageGuard.before context flag bank] at present
      exact List.mem_singleton.mp present
    subst original
    have samePoint : point=0 := Option.some.inj selected.symm
    subst point
    rfl)
  simp only [List.map_map,Function.comp_def] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem body_path (caller : Statement C) (run : List (FirstRaw.State C)) (before final : FirstRaw.State C)
    (first : run.head?=some before) (chain : run.IsChain (fun a b => TM2.step (FirstRaw.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    (run.map bodyCfg).head?=some (bodyCfg before) ∧
    (run.map bodyCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map bodyCfg).getLast?=some (bodyCfg final) := by
  have proper:=NativeMulLink.no_early_halt_port (FirstRaw.program .halt) .done rfl run final chain last active
  have mapped:=LabelMap.actual_path_on bodyLabel (FirstRaw.program .halt) (program caller)
    run before final first chain last (by
      intro current member point selected
      have different : point≠.done := by intro equal; subst point; exact proper current member selected
      simp only [bodyLabel,different,ite_false,program])
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem select_step (caller : Statement C) (memory : Store C) (bank : RatInput.Stack → List Bool) :
    TM2.step (program caller) (⟨some .select,memory,bank⟩ : State C)=
      some (⟨some (if memory.2.2 then .fee .boot else .done),memory,bank⟩ : State C) := by
  cases selected : memory.2.2 <;> simp [TM2.step,program,TM2.stepAux,selected]

theorem fee_path (caller : Statement C) (run : List (RawGetter.State (FirstRaw.RawContext C)))
    (before final : RawGetter.State (FirstRaw.RawContext C)) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (RawGetter.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    (run.map feeCfg).head?=some (feeCfg before) ∧
    (run.map feeCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map feeCfg).getLast?=some (feeCfg final) := by
  let old:=RawGetter.program (C := FirstRaw.RawContext C) .halt
  let stackProgram:=fun point => StackIso.statement feeRoles (old point)
  let stackRun:=run.map (StackIso.configuration feeRoles)
  have stackFirst : stackRun.head?=some (StackIso.configuration feeRoles before) := by
    rw [List.head?_map,first,Option.map_some]
  have stackChain:=StackIso.chain_configuration_on feeRoles old stackProgram run chain
    (by intro current member point selected; rfl)
  have stackLast : stackRun.getLast?=some (StackIso.configuration feeRoles final) := by
    rw [List.getLast?_map,last,Option.map_some]
  let isoProgram:=StoreIso.machine (FirstRaw.rawIso C) stackProgram
  have iso:=StoreIso.actual_path_on (FirstRaw.rawIso C) stackProgram isoProgram stackRun _ _ stackFirst stackChain stackLast
    (by intro current member point selected; rfl)
  have proper:=NativeMulLink.no_early_halt_port isoProgram .done rfl _ _ iso.2.1 iso.2.2.1 active
  have mapped:=LabelMap.actual_path_on feeLabel isoProgram (program caller)
    _ _ _ iso.1 iso.2.1 iso.2.2.1 (by
      intro current member point selected
      have different : point≠.done := by intro equal; subst point; exact proper current member selected
      simp only [feeLabel,different,ite_false,program]
      rfl)
  simp only [stackRun,List.map_map,Function.comp_def] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

end RootB234.PrepEntry.StageFront
