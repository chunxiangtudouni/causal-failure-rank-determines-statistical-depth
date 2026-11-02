module

public import RootB234_PrepEntry_StageChannelsPublic_069

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.WholeChannels

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

variable {C D : Type*}

/-- Preserve every actual finite budget register, replacing only its
opaque caller context. No register is initialized at a phase splice. -/
def mapBudgetContext (change : C → D) (memory : Budget.Store C) : Budget.Store D :=
  (((((change memory.1.1.1.1.1,memory.1.1.1.1.2),memory.1.1.1.2),memory.1.1.2),memory.1.2),memory.2)

abbrev Store (C : Type*) := Budget.Store Unit × StageChannels.Store C

def budgetIso (C : Type*) : Budget.Store (StageChannels.Store C) ≃ Store C where
  toFun := fun memory => (mapBudgetContext (fun _ => ()) memory,Budget.callerContext memory)
  invFun := fun memory => mapBudgetContext (fun _ => memory.2) memory.1
  left_inv := by intro memory; rfl
  right_inv := by
    rintro ⟨⟨⟨⟨⟨⟨trivial,raw⟩,copy⟩,alpha⟩,natural⟩,header⟩,stage⟩
    cases trivial
    rfl

inductive Label where
  | budget : Budget.Label → Label
  | channels : StageChannels.Label → Label
  | done
  deriving DecidableEq, Fintype
instance : Inhabited Label := ⟨.budget default⟩

abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

def budgetLabel (point : Budget.Label) : Label := if point=.done then .channels default else .budget point
def channelsLabel (point : StageChannels.Label) : Label := if point=.done then .done else .channels point

noncomputable def program (caller : Statement C) : Label → Statement C
  | .budget point => LabelMap.statement budgetLabel (StoreIso.statement (budgetIso C) (Budget.program .halt point))
  | .channels point => LabelMap.statement channelsLabel (ContextLift.statement (StageChannels.program .halt point))
  | .done => caller

def stageMemory (context : C) : StageChannels.Store C := (StageChannels.entry context (fun _ => []) []).var

def budgetCfg (before : Budget.State (StageChannels.Store C)) : State C :=
  LabelMap.configuration budgetLabel (StoreIso.configuration (budgetIso C) before)

def channelsCfg (memory : Budget.Store Unit) (before : StageChannels.State C) : State C :=
  LabelMap.configuration channelsLabel (ContextLift.configuration memory before)

def entry (context : C) (bits : List Bool) : State C := budgetCfg (Budget.entry (stageMemory context) bits)

def callerContext (memory : Store C) : C := StageChannels.callerContext memory.2

/-- This is a fixed finite initial value, chosen before all original
inputs. The budget entry already contains the stage block as opaque
context, so it cannot be allocated or reset at the later splice. -/
instance [Inhabited C] : Inhabited (Store C) :=
  ⟨budgetIso C (Budget.entry (stageMemory (default : C)) []).var⟩

theorem initial_default [Inhabited C] (bits : List Bool) :
    entry (default : C) bits=TM2.init (Γ := RatInput.Alphabet) (Λ := Label) (σ := Store C) 0 bits := by
  change (⟨some (default : Label),(default : Store C),_⟩ : State C)=⟨some default,default,_⟩
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem stage_entry_memory (context : C) (background : RatInput.Stack → List Bool) (bits : List Bool) :
    (StageChannels.entry context background bits).var=stageMemory context := rfl

theorem stage_entry_point (context : C) (background : RatInput.Stack → List Bool) (bits : List Bool) :
    (StageChannels.entry context background bits).l=some default := rfl

theorem budget_path (caller : Statement C) (run : List (Budget.State (StageChannels.Store C)))
    (before final : Budget.State (StageChannels.Store C)) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (Budget.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    (run.map budgetCfg).head?=some (budgetCfg before) ∧
    (run.map budgetCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map budgetCfg).getLast?=some (budgetCfg final) := by
  let old := StoreIso.machine (budgetIso C) (Budget.program .halt)
  have transported := StoreIso.actual_path_on (budgetIso C) (Budget.program .halt) old run before final
    first chain last (by intro current member point selected; rfl)
  have proper := NativeMulLink.no_early_halt_port old .done rfl _ _ transported.2.1 transported.2.2.1 active
  have mapped := LabelMap.actual_path_on budgetLabel old (program caller)
    _ _ _ transported.1 transported.2.1 transported.2.2.1 (by
      intro current member point selected
      have different : point≠.done := by intro equal; subst point; exact proper current member selected
      simp only [budgetLabel,different,ite_false,program]
      rfl)
  simp only [List.map_map,Function.comp_def] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem channels_path (caller : Statement C) (memory : Budget.Store Unit)
    (run : List (StageChannels.State C)) (before final : StageChannels.State C)
    (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (StageChannels.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    (run.map (channelsCfg memory)).head?=some (channelsCfg memory before) ∧
    (run.map (channelsCfg memory)).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map (channelsCfg memory)).getLast?=some (channelsCfg memory final) := by
  let old : StageChannels.Label → TM2.Stmt RatInput.Alphabet StageChannels.Label (Store C) :=
    ContextLift.machine (StageChannels.program (C := C) .halt)
  have contextual := ContextLift.actual_path (StageChannels.program .halt) memory run before final first chain last
  have proper := NativeMulLink.no_early_halt_port old .done rfl _ _ contextual.2.1 contextual.2.2.1 active
  have mapped := LabelMap.actual_path_on channelsLabel old (program caller)
    _ _ _ contextual.1 contextual.2.1 contextual.2.2.1 (by
      intro current member point selected
      have different : point≠.done := by intro equal; subst point; exact proper current member selected
      simp only [channelsLabel,different,ite_false,program]
      rfl)
  simp only [List.map_map,Function.comp_def] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

end RootB234.PrepEntry.WholeChannels
