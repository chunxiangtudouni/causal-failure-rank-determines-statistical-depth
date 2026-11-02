module

public import RootB234_PrepEntry_StageChannelsClosed_057

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

variable {C : Type*}

private theorem path {Λ σ : Type*} (caller : Statement C)
    (old : Λ → TM2.Stmt RatInput.Alphabet Λ σ) (roles : RatInput.Stack ≃ RatInput.Stack)
    (iso : σ ≃ Store C) (rename : Λ → Label) (allowed : Λ → Prop)
    (run : List (TM2.Cfg RatInput.Alphabet Λ σ)) (before final : TM2.Cfg RatInput.Alphabet Λ σ)
    (first : run.head?=some before) (chain : run.IsChain (fun a b => TM2.step old a=some b))
    (last : run.getLast?=some final)
    (proper : ∀ current∈run.dropLast,∀ point,current.l=some point→allowed point)
    (same : ∀ point,allowed point→program caller (rename point)=
      LabelMap.statement rename (StoreIso.statement iso (StackIso.statement roles (old point)))) :
    let mapped:=fun current => LabelMap.configuration rename (StoreIso.configuration iso (StackIso.configuration roles current))
    (run.map mapped).head?=some (mapped before) ∧
    (run.map mapped).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map mapped).getLast?=some (mapped final) := by
  let stackProgram:=fun point => StackIso.statement roles (old point)
  let stackRun:=run.map (StackIso.configuration roles)
  have stackFirst : stackRun.head?=some (StackIso.configuration roles before) := by rw [List.head?_map,first,Option.map_some]
  have stackChain:=StackIso.chain_configuration_on roles old stackProgram run chain (by intro current member point selected; rfl)
  have stackLast : stackRun.getLast?=some (StackIso.configuration roles final) := by rw [List.getLast?_map,last,Option.map_some]
  let isoProgram:=StoreIso.machine iso stackProgram
  have isoRun:=StoreIso.actual_path_on iso stackProgram isoProgram stackRun _ _ stackFirst stackChain stackLast
    (by intro current member point selected; rfl)
  have mapped:=LabelMap.actual_path_on rename isoProgram (program caller)
    _ _ _ isoRun.1 isoRun.2.1 isoRun.2.2.1 (by
      intro current member point selected
      change current∈(stackRun.map (StoreIso.configuration iso)).dropLast at member
      rw [←List.map_dropLast] at member
      obtain ⟨stackCurrent,stackMember,rfl⟩:=List.mem_map.mp member
      change stackCurrent∈(run.map (StackIso.configuration roles)).dropLast at stackMember
      rw [←List.map_dropLast] at stackMember
      obtain ⟨original,present,rfl⟩:=List.mem_map.mp stackMember
      exact same point (proper original present point selected))
  simp only [stackRun,List.map_map,Function.comp_def] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem buildLeft_path (caller : Statement C)
    (run : List (RootB234.RuntimeCounter.Builder.State (Channels.PacketContext (StageFront.Store C))))
    (before final : RootB234.RuntimeCounter.Builder.State (Channels.PacketContext (StageFront.Store C)))
    (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step RootB234.RuntimeCounter.Builder.Public.from8N a=some b))
    (last : run.getLast?=some final) (active : final.l=some 5) :
    (run.map buildLeftCfg).head?=some (buildLeftCfg before) ∧
    (run.map buildLeftCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map buildLeftCfg).getLast?=some (buildLeftCfg final) := by
  have proper:=NativeMulLink.no_early_halt_port RootB234.RuntimeCounter.Builder.Public.from8N 5 rfl run final chain last active
  exact path caller RootB234.RuntimeCounter.Builder.Public.from8N leftRoles (buildIso C) buildLeftLabel
    (fun point => point≠5) run before final first chain last (by
      intro current member point selected equal
      subst point; exact proper current member selected)
    (by intro point different; simp only [buildLeftLabel,different,ite_false,program])

theorem buildRight_path (caller : Statement C)
    (run : List (RootB234.RuntimeCounter.Builder.State (Channels.PacketContext (StageFront.Store C))))
    (before final : RootB234.RuntimeCounter.Builder.State (Channels.PacketContext (StageFront.Store C)))
    (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step RootB234.RuntimeCounter.Builder.Public.from8N a=some b))
    (last : run.getLast?=some final) (active : final.l=some 5) :
    (run.map buildRightCfg).head?=some (buildRightCfg before) ∧
    (run.map buildRightCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map buildRightCfg).getLast?=some (buildRightCfg final) := by
  have proper:=NativeMulLink.no_early_halt_port RootB234.RuntimeCounter.Builder.Public.from8N 5 rfl run final chain last active
  exact path caller RootB234.RuntimeCounter.Builder.Public.from8N leftRoles (buildIso C) buildRightLabel
    (fun point => point≠5) run before final first chain last (by
      intro current member point selected equal
      subst point; exact proper current member selected)
    (by intro point different; simp only [buildRightLabel,different,ite_false,program])

theorem left_path (caller : Statement C) (run : List (Channels.State (StageFront.Store C)))
    (before final : Channels.State (StageFront.Store C)) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (Channels.program .halt) a=some b))
    (last : run.getLast?=some final) (start : before.l=some (.round 0)) (active : final.l=some .done) :
    (run.map leftCfg).head?=some (leftCfg before) ∧
    (run.map leftCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map leftCfg).getLast?=some (leftCfg final) := by
  have closed:=loop_closed run before first chain start
  have proper:=NativeMulLink.no_early_halt_port (Channels.program .halt) .done rfl run final chain last active
  apply path caller (Channels.program .halt) leftRoles (channelIso C) leftLabel
    (fun point => LoopPoint point ∧ point≠.done) run before final first chain last
  · intro current member point selected
    exact ⟨closed current (List.mem_of_mem_dropLast member) point selected,
      fun equal => proper current member (equal ▸ selected)⟩
  · intro point allowed
    simp only [leftLabel,allowed.2,ite_false,program]
    rw [loopSource_eq .halt point allowed.1]

theorem right_path (caller : Statement C) (run : List (Channels.State (StageFront.Store C)))
    (before final : Channels.State (StageFront.Store C)) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (Channels.program .halt) a=some b))
    (last : run.getLast?=some final) (start : before.l=some (.round 0)) (active : final.l=some .done) :
    (run.map rightCfg).head?=some (rightCfg before) ∧
    (run.map rightCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map rightCfg).getLast?=some (rightCfg final) := by
  have closed:=loop_closed run before first chain start
  have proper:=NativeMulLink.no_early_halt_port (Channels.program .halt) .done rfl run final chain last active
  apply path caller (Channels.program .halt) rightRoles (channelIso C) rightLabel
    (fun point => LoopPoint point ∧ point≠.done) run before final first chain last
  · intro current member point selected
    exact ⟨closed current (List.mem_of_mem_dropLast member) point selected,
      fun equal => proper current member (equal ▸ selected)⟩
  · intro point allowed
    simp only [rightLabel,allowed.2,ite_false,program]
    rw [loopSource_eq .halt point allowed.1]

end RootB234.PrepEntry.StageChannels
