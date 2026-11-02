module

public import RootB234_PrepEntry_FirstRawData_033

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.FirstRaw

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

abbrev Store (C : Type*) := NJ.Store (C × RawGetter.ParserMemory)
abbrev HeaderContext (C : Type*) := ((C × RawGetter.ParserMemory) × Alpha.NativeMemory) × PSTRSymbolicNaturalExport.Store
abbrev FieldContext (C : Type*) := Header.Store ((C × RawGetter.ParserMemory) × Alpha.NativeMemory)
abbrev RawContext (C : Type*) := Header.Store (C × Alpha.NativeMemory)

inductive Label where
  | header : Fin 2 → Label
  | tools : Fin 2 → Label
  | prefix : NatPrefix.Label → Label
  | natural : NatField.Label → Label
  | rational : RawGetter.Label → Label
  | done
  deriving DecidableEq, Fintype
instance : Inhabited Label := ⟨.header 0⟩

abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def alphaIso (C : Type*) : Alpha.Store (HeaderNat.Store (C × RawGetter.ParserMemory)) ≃ Store C :=
  NJ.alphaIso (C × RawGetter.ParserMemory)

def fieldIso (C : Type*) : NatField.Store (FieldContext C) ≃ Store C :=
  HeaderNat.fieldIso ((C × RawGetter.ParserMemory) × Alpha.NativeMemory)

def rawIso (C : Type*) : RawGetter.Store (RawContext C) ≃ Store C where
  toFun := fun v => ((((v.1.1.1.1,v.1.2),v.1.1.1.2),v.2),v.1.1.2)
  invFun := fun v => ((((v.1.1.1.1,v.1.1.2),v.2),v.1.1.1.2),v.1.2)
  left_inv := by rintro ⟨⟨⟨⟨context,alpha⟩,header⟩,parser⟩,flags⟩; rfl
  right_inv := by rintro ⟨⟨⟨⟨context,parser⟩,alpha⟩,flags⟩,header⟩; rfl

def naturalRoles : RatInput.Stack ≃ RatInput.Stack := Equiv.swap 14 15
def rationalRoles : RatInput.Stack ≃ RatInput.Stack := Equiv.swap 13 15

def headerLabel (point : Fin 2) : Label := if point=1 then .tools 0 else .header point
def toolsLabel (point : Fin 2) : Label := if point=1 then .prefix .check else .tools point
def prefixLabel (point : NatPrefix.Label) : Label := if point=.done then .natural 0 else .prefix point
def naturalLabel (point : NatField.Label) : Label := if point=4 then .rational .boot else .natural point
def rationalLabel (point : RawGetter.Label) : Label := if point=.done then .done else .rational point

/-- All extra registers are finite Bool/Fin products allocated at literal
entry. The source consumes original M/N/J, the original natural prefix,
then its first original rational. Existing N8/J9/budget15 are framed. -/
def program (caller : Statement C) : Label → Statement C
  | .header point => LabelMap.statement headerLabel (Header.program .halt point)
  | .tools point => LabelMap.statement toolsLabel (StoreIso.statement (alphaIso C) (Alpha.program .halt point))
  | .prefix point => LabelMap.statement prefixLabel (StoreIso.statement (alphaIso C) (NatPrefix.program .halt point))
  | .natural point => LabelMap.statement naturalLabel (StoreIso.statement (fieldIso C)
      (StackIso.statement naturalRoles (NatField.program .halt point)))
  | .rational point => LabelMap.statement rationalLabel (StoreIso.statement (rawIso C)
      (StackIso.statement rationalRoles (RawGetter.program .halt point)))
  | .done => caller

def headerCfg (before : Header.State (HeaderContext C)) : State C := LabelMap.configuration headerLabel before
def toolsCfg (before : Alpha.State (HeaderNat.Store (C × RawGetter.ParserMemory))) : State C :=
  LabelMap.configuration toolsLabel (StoreIso.configuration (alphaIso C) before)
def prefixCfg (before : NatPrefix.State (HeaderNat.Store (C × RawGetter.ParserMemory))) : State C :=
  LabelMap.configuration prefixLabel (StoreIso.configuration (alphaIso C) before)
def naturalCfg (before : NatField.State (FieldContext C)) : State C :=
  LabelMap.configuration naturalLabel (StoreIso.configuration (fieldIso C) (StackIso.configuration naturalRoles before))
def rationalCfg (before : RawGetter.State (RawContext C)) : State C :=
  LabelMap.configuration rationalLabel (StoreIso.configuration (rawIso C) (StackIso.configuration rationalRoles before))

def entry (context : C) (background : RatInput.Stack → List Bool) (bits : List Bool) : State C :=
  headerCfg (Header.entry (((context,default),default),default) background bits)

def callerContext (memory : Store C) : C := memory.1.1.1.1

private theorem iso_path {Λ σ : Type*} [Inhabited Λ] (caller : Statement C)
    (old : Λ → TM2.Stmt RatInput.Alphabet Λ σ) (port : Λ) (halt : old port=.halt)
    (iso : σ ≃ Store C) (tag : Λ → Label)
    (run : List (TM2.Cfg RatInput.Alphabet Λ σ)) (before final : TM2.Cfg RatInput.Alphabet Λ σ)
    (first : run.head?=some before) (chain : run.IsChain (fun a b => TM2.step old a=some b))
    (last : run.getLast?=some final) (active : final.l=some port)
    (same : ∀ point,point≠port→program caller (tag point)=LabelMap.statement tag (StoreIso.statement iso (old point))) :
    (run.map (fun current => LabelMap.configuration tag (StoreIso.configuration iso current))).head?=
      some (LabelMap.configuration tag (StoreIso.configuration iso before)) ∧
    (run.map (fun current => LabelMap.configuration tag (StoreIso.configuration iso current))).IsChain
      (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map (fun current => LabelMap.configuration tag (StoreIso.configuration iso current))).getLast?=
      some (LabelMap.configuration tag (StoreIso.configuration iso final)) := by
  let isoProgram:=StoreIso.machine iso old
  have mappedStore:=StoreIso.actual_path_on iso old isoProgram run before final first chain last
    (by intro current member point selected; rfl)
  have stopped : isoProgram port=.halt := by change StoreIso.statement iso (old port)=.halt; rw [halt]; rfl
  have proper:=NativeMulLink.no_early_halt_port isoProgram port stopped _ _ mappedStore.2.1 mappedStore.2.2.1 active
  have mapped:=LabelMap.actual_path_on tag isoProgram (program caller)
    _ _ _ mappedStore.1 mappedStore.2.1 mappedStore.2.2.1 (by
      intro current member point selected
      exact same point (by intro equal; subst point; exact proper current member selected))
  have maps : (run.map (StoreIso.configuration iso)).map (LabelMap.configuration tag)=
      run.map (fun current => LabelMap.configuration tag (StoreIso.configuration iso current)) := by rw [List.map_map]; rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem header_path (caller : Statement C) (run : List (Header.State (HeaderContext C)))
    (before final : Header.State (HeaderContext C)) (first : run.head?=some before)
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

theorem tools_path (caller : Statement C) (run : List (Alpha.State (HeaderNat.Store (C × RawGetter.ParserMemory))))
    (before final : Alpha.State (HeaderNat.Store (C × RawGetter.ParserMemory))) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (Alpha.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some 1) :
    (run.map toolsCfg).head?=some (toolsCfg before) ∧
    (run.map toolsCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map toolsCfg).getLast?=some (toolsCfg final) := by
  exact iso_path caller (Alpha.program .halt) 1 rfl (alphaIso C) toolsLabel run before final first chain last active
    (by intro point different; simp only [toolsLabel,different,ite_false,program])

theorem prefix_path (caller : Statement C) (run : List (NatPrefix.State (HeaderNat.Store (C × RawGetter.ParserMemory))))
    (before final : NatPrefix.State (HeaderNat.Store (C × RawGetter.ParserMemory))) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (NatPrefix.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    (run.map prefixCfg).head?=some (prefixCfg before) ∧
    (run.map prefixCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map prefixCfg).getLast?=some (prefixCfg final) := by
  exact iso_path caller (NatPrefix.program .halt) .done rfl (alphaIso C) prefixLabel run before final first chain last active
    (by intro point different; simp only [prefixLabel,different,ite_false,program])

private theorem stack_path {Λ σ : Type*} [Inhabited Λ] (caller : Statement C)
    (old : Λ → TM2.Stmt RatInput.Alphabet Λ σ) (port : Λ) (halt : old port=.halt)
    (iso : σ ≃ Store C) (roles : RatInput.Stack ≃ RatInput.Stack) (tag : Λ → Label)
    (run : List (TM2.Cfg RatInput.Alphabet Λ σ)) (before final : TM2.Cfg RatInput.Alphabet Λ σ)
    (first : run.head?=some before) (chain : run.IsChain (fun a b => TM2.step old a=some b))
    (last : run.getLast?=some final) (active : final.l=some port)
    (same : ∀ point,point≠port→program caller (tag point)=
      LabelMap.statement tag (StoreIso.statement iso (StackIso.statement roles (old point)))) :
    (run.map (fun current => LabelMap.configuration tag (StoreIso.configuration iso (StackIso.configuration roles current)))).head?=
      some (LabelMap.configuration tag (StoreIso.configuration iso (StackIso.configuration roles before))) ∧
    (run.map (fun current => LabelMap.configuration tag (StoreIso.configuration iso (StackIso.configuration roles current)))).IsChain
      (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map (fun current => LabelMap.configuration tag (StoreIso.configuration iso (StackIso.configuration roles current)))).getLast?=
      some (LabelMap.configuration tag (StoreIso.configuration iso (StackIso.configuration roles final))) := by
  let stackProgram:=fun point => StackIso.statement roles (old point)
  have first' : (run.map (StackIso.configuration roles)).head?=some (StackIso.configuration roles before) := by
    rw [List.head?_map,first,Option.map_some]
  have chain':=StackIso.chain_configuration_on roles old stackProgram run chain (by intro current member point selected; rfl)
  have last' : (run.map (StackIso.configuration roles)).getLast?=some (StackIso.configuration roles final) := by
    rw [List.getLast?_map,last,Option.map_some]
  have halted : stackProgram port=.halt := by change StackIso.statement roles (old port)=.halt; rw [halt]; rfl
  have mapped:=iso_path caller stackProgram port halted iso tag _ _ _ first' chain' last' active same
  simpa only [List.map_map,Function.comp_def] using mapped

theorem natural_path (caller : Statement C) (run : List (NatField.State (FieldContext C)))
    (before final : NatField.State (FieldContext C)) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (NatField.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some 4) :
    (run.map naturalCfg).head?=some (naturalCfg before) ∧
    (run.map naturalCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map naturalCfg).getLast?=some (naturalCfg final) := by
  exact stack_path caller (NatField.program .halt) 4 rfl (fieldIso C) naturalRoles naturalLabel run before final first chain last active
    (by intro point different; simp only [naturalLabel,different,ite_false,program])

theorem rational_path (caller : Statement C) (run : List (RawGetter.State (RawContext C)))
    (before final : RawGetter.State (RawContext C)) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (RawGetter.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    (run.map rationalCfg).head?=some (rationalCfg before) ∧
    (run.map rationalCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map rationalCfg).getLast?=some (rationalCfg final) := by
  exact stack_path caller (RawGetter.program .halt) .done rfl (rawIso C) rationalRoles rationalLabel run before final first chain last active
    (by intro point different; simp only [rationalLabel,different,ite_false,program])

end RootB234.PrepEntry.FirstRaw
