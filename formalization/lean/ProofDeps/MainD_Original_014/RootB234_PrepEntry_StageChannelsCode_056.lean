module

public import RootB234_PrepEntry_StageFrontPublic_054
public import B23_4_RatWordPrep_SeqCmp_ChannelsLoop_079

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.StageChannels

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

variable {C D : Type*}

/-- Only reassociate the already allocated finite old loop registers.
The unused word prelude remains opaque context; it is never executed. -/
def mapFeeContext (change : C → D) (memory : OriginalFee.Store C) : OriginalFee.Store D :=
  (((((((change (OriginalFee.context memory),memory.1.1.1.1.1.1.2),memory.1.1.1.1.1.2),
    memory.1.1.1.1.2),memory.1.1.1.2),memory.1.1.2),memory.1.2),memory.2)

abbrev Registers := Channels.Aux × (OriginalPrelude.Extra × OriginalFee.Store Unit)
abbrev Store (C : Type*) := Registers × StageFront.Store C

def channelIso (C : Type*) : Channels.Store (StageFront.Store C) ≃ Store C where
  toFun := fun memory => ((memory.1,(OriginalPrelude.extra memory.2,
    mapFeeContext (fun _ => ()) (OriginalPrelude.feeMemory memory.2))),OriginalPrelude.callerContext memory.2)
  invFun := fun memory => (memory.1.1,OriginalPrelude.feeIso (StageFront.Store C)
    (memory.1.2.1,mapFeeContext (fun _ => memory.2) memory.1.2.2))
  left_inv := by intro memory; rfl
  right_inv := by
    rintro ⟨⟨aux,extra,fee⟩,context⟩
    rcases fee with ⟨⟨⟨⟨⟨⟨⟨trivialContext,parser⟩,natural⟩,prior⟩,rat⟩,formatter⟩,native⟩,reader⟩
    cases trivialContext
    rfl

inductive Label where
  | front : StageFront.Label → Label
  | select
  | buildLeft : RootB234.RuntimeCounter.Builder.Label → Label
  | left : Channels.Label → Label
  | buildRight : RootB234.RuntimeCounter.Builder.Label → Label
  | right : Channels.Label → Label
  | done
  deriving DecidableEq, Fintype
instance : Inhabited Label := ⟨.front default⟩

abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

def leftRoles : RatInput.Stack ≃ RatInput.Stack := Equiv.swap 8 14
def rightRoles : RatInput.Stack ≃ RatInput.Stack := (Equiv.swap 8 14).trans (Equiv.swap 2 6)

def buildIso (C : Type*) : RootB234.RuntimeCounter.Builder.Store (Channels.PacketContext (StageFront.Store C)) ≃ Store C :=
  (Channels.packetIso (StageFront.Store C)).trans (channelIso C)

def frontLabel (point : StageFront.Label) : Label := if point=.done then .select else .front point
def buildLeftLabel (point : RootB234.RuntimeCounter.Builder.Label) : Label := if point=5 then .left (.round 0) else .buildLeft point
def leftLabel (point : Channels.Label) : Label := if point=.done then .buildRight 0 else .left point
def buildRightLabel (point : RootB234.RuntimeCounter.Builder.Label) : Label := if point=5 then .right (.round 0) else .buildRight point
def rightLabel (point : Channels.Label) : Label := if point=.done then .done else .right point

/-- Reuse the frozen round/read/move source literally. Old word-prelude
and old 2A-builder labels are unavailable in this A-per-truth source. -/
noncomputable def loopSource (caller : Channels.Statement (StageFront.Store C)) :
    Channels.Label → Channels.Statement (StageFront.Store C)
  | .prelude _ | .build _ => .halt
  | .round point => Channels.program caller (.round point)
  | .read point => Channels.program caller (.read point)
  | .move point => Channels.program caller (.move point)
  | .done => caller

noncomputable def program (caller : Statement C) : Label → Statement C
  | .front point => LabelMap.statement frontLabel (ContextLift.statement (StageFront.program .halt point))
  | .select => .branch (fun memory => memory.2.2.2) (.goto (fun _ => .buildLeft 0)) (.goto (fun _ => .done))
  | .buildLeft point => LabelMap.statement buildLeftLabel (StoreIso.statement (buildIso C)
      (StackIso.statement leftRoles (RootB234.RuntimeCounter.Builder.Public.from8N point)))
  | .left point => LabelMap.statement leftLabel (StoreIso.statement (channelIso C)
      (StackIso.statement leftRoles (loopSource .halt point)))
  | .buildRight point => LabelMap.statement buildRightLabel (StoreIso.statement (buildIso C)
      (StackIso.statement leftRoles (RootB234.RuntimeCounter.Builder.Public.from8N point)))
  | .right point => LabelMap.statement rightLabel (StoreIso.statement (channelIso C)
      (StackIso.statement rightRoles (loopSource .halt point)))
  | .done => caller

def frontCfg (registers : Registers) (before : StageFront.State C) : State C :=
  LabelMap.configuration frontLabel (ContextLift.configuration registers before)
def buildLeftCfg (before : RootB234.RuntimeCounter.Builder.State (Channels.PacketContext (StageFront.Store C))) : State C :=
  LabelMap.configuration buildLeftLabel (StoreIso.configuration (buildIso C) (StackIso.configuration leftRoles before))
def leftCfg (before : Channels.State (StageFront.Store C)) : State C :=
  LabelMap.configuration leftLabel (StoreIso.configuration (channelIso C) (StackIso.configuration leftRoles before))
def buildRightCfg (before : RootB234.RuntimeCounter.Builder.State (Channels.PacketContext (StageFront.Store C))) : State C :=
  LabelMap.configuration buildRightLabel (StoreIso.configuration (buildIso C) (StackIso.configuration leftRoles before))
def rightCfg (before : Channels.State (StageFront.Store C)) : State C :=
  LabelMap.configuration rightLabel (StoreIso.configuration (channelIso C) (StackIso.configuration rightRoles before))

def entry (context : C) (background : RatInput.Stack → List Bool) (bits : List Bool) : State C :=
  frontCfg default (StageFront.entry context background bits)

def callerContext (memory : Store C) : C := StageFront.callerContext memory.2

theorem initial_default [Inhabited C] (bits : List Bool) :
    entry (default : C) (fun _ => []) bits=TM2.init (Γ := RatInput.Alphabet) (Λ := Label) (σ := Store C) 0 bits := by
  rw [entry,StageFront.initial_default]
  rfl

theorem front_path (caller : Statement C) (registers : Registers) (run : List (StageFront.State C))
    (before final : StageFront.State C) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (StageFront.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    (run.map (frontCfg registers)).head?=some (frontCfg registers before) ∧
    (run.map (frontCfg registers)).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map (frontCfg registers)).getLast?=some (frontCfg registers final) := by
  let old:=StageFront.program (C := C) .halt
  let lifted : StageFront.Label → TM2.Stmt RatInput.Alphabet StageFront.Label (Store C):=
    ContextLift.machine old
  have contextual:=ContextLift.actual_path old registers run before final first chain last
  have proper:=NativeMulLink.no_early_halt_port lifted .done rfl _ _ contextual.2.1 contextual.2.2.1 active
  have mapped:=LabelMap.actual_path_on frontLabel lifted (program caller)
    _ _ _ contextual.1 contextual.2.1 contextual.2.2.1 (by
      intro current member point selected
      have different : point≠.done := by intro equal; subst point; exact proper current member selected
      simp only [frontLabel,different,ite_false,program]
      rfl)
  simp only [List.map_map,Function.comp_def] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem select_step (caller : Statement C) (memory : Store C) (bank : RatInput.Stack → List Bool) :
    TM2.step (program caller) (⟨some .select,memory,bank⟩ : State C)=
      some (⟨some (if memory.2.2.2 then .buildLeft 0 else .done),memory,bank⟩ : State C) := by
  cases selected : memory.2.2.2 <;> simp [TM2.step,program,TM2.stepAux,selected]

end RootB234.PrepEntry.StageChannels
