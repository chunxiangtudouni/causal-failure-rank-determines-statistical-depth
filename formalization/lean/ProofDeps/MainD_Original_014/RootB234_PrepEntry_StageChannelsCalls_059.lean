module

public import RootB234_PrepEntry_StageChannelsPaths_058

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

structure Segment (caller : Statement C) (before final : State C) where
  trace : List (State C)
  first : trace.head?=some before
  chain : trace.IsChain (fun a b => TM2.step (program caller) a=some b)
  last : trace.getLast?=some final

def Segment.append {caller : Statement C} {before middle final : State C}
    (front : Segment caller before middle) (back : Segment caller middle final) : Segment caller before final := by
  have shape : middle::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp back.first
    rw [same]; rfl
  refine ⟨front.trace++back.trace.tail,?_,?_,?_⟩
  · rw [List.head?_append,front.first]; rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)

def buildCfg (right : Bool) : RootB234.RuntimeCounter.Builder.State (Channels.PacketContext (StageFront.Store C)) → State C :=
  if right then buildRightCfg else buildLeftCfg

def buildPoint (right : Bool) : Label := if right then .buildRight 0 else .buildLeft 0
def roundPoint (right : Bool) : Label := if right then .right (.round 0) else .left (.round 0)

theorem build_path (right : Bool) (caller : Statement C)
    (run : List (RootB234.RuntimeCounter.Builder.State (Channels.PacketContext (StageFront.Store C))))
    (before final : RootB234.RuntimeCounter.Builder.State (Channels.PacketContext (StageFront.Store C)))
    (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step RootB234.RuntimeCounter.Builder.Public.from8N a=some b))
    (last : run.getLast?=some final) (active : final.l=some 5) :
    (run.map (buildCfg right)).head?=some (buildCfg right before) ∧
    (run.map (buildCfg right)).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map (buildCfg right)).getLast?=some (buildCfg right final) := by
  cases right
  · exact buildLeft_path caller run before final first chain last active
  · exact buildRight_path caller run before final first chain last active

theorem build_shared (right : Bool) (before : State C) (number : Nat) (tail : List Bool)
    (active : before.l=some (buildPoint right)) (source : before.stk 14=NatField.packet number tail)
    (scratch : before.stk 4=[]) :
    buildCfg right (RootB234.RuntimeCounter.Builder.atState RootB234.RuntimeCounter.Builder.Public.source8Roles
      (StackIso.slots leftRoles.symm before.stk) 0 ((buildIso C).symm before.var).1 ((buildIso C).symm before.var).2
      (NatField.packet number tail) [] (before.stk 10) (before.stk 11))=before := by
  cases before with
  | mk point memory slots =>
    change point=some (buildPoint right) at active
    subst point
    cases right <;> change
      (⟨some _,buildIso C ((buildIso C).symm memory),
        StackIso.slots leftRoles (RootB234.RuntimeCounter.Builder.bank (StackIso.slots leftRoles.symm slots) _ _ _ _)⟩ : State C)=_
    all_goals
      rw [Equiv.apply_symm_apply]
      congr 1
      funext slot
      fin_cases slot <;> simp_all [RootB234.RuntimeCounter.Builder.bank,leftRoles,StackIso.slots,Equiv.swap_apply_def]

/-- Each truth channel receives an actual A counter copied from the
original alphabet packet14. This is the N builder, never the old 2N
word-input builder. Its two finite flags are carried from real memory. -/
theorem actual_build (right : Bool) (caller : Statement C) (before : State C) (number : Nat) (tail : List Bool)
    (active : before.l=some (buildPoint right)) (source : before.stk 14=NatField.packet number tail)
    (scratch : before.stk 4=[]) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (roundPoint right) ∧ final.var.2=before.var.2 ∧
      final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet (PSTRTMNatValue017.rawPayload number) ∧
      final.stk 11=[false] ∧ final.stk 4=[] ∧
      (∀ slot,slot≠4→slot≠10→slot≠11→final.stk slot=before.stk slot) ∧
      run.trace.length≤(before.stk 10).length+(before.stk 11).length+
        2*(PSTRTMNatValue017.rawPayload number).length+14 := by
  let registers:=(buildIso C).symm before.var
  let background:=StackIso.slots leftRoles.symm before.stk
  obtain ⟨trace,facts⟩:=RootB234.RuntimeCounter.Builder.Public.from8N_actual
    background registers.1 registers.2 number tail (before.stk 10) (before.stk 11)
  let final:=RootB234.RuntimeCounter.Builder.Public.finalState
    RootB234.RuntimeCounter.Builder.Public.source8Roles false background registers.1 number tail
  have path:=build_path right caller trace _ final facts.first facts.chain facts.last rfl
  let run : Segment caller before (buildCfg right final):=
    ⟨trace.map (buildCfg right),path.1.trans (congrArg some (build_shared right before number tail active source scratch)),
      path.2.1,path.2.2⟩
  refine ⟨buildCfg right final,run,?_,?_,?_,?_,?_,?_,?_⟩
  · cases right <;> rfl
  · cases right <;> rfl
  · cases right <;> rfl
  · cases right <;> rfl
  · cases right <;> rfl
  · intro slot n4 n10 n11
    cases right <;> change
      RootB234.RuntimeCounter.Builder.bank background (NatField.packet number tail) [] _ _ (leftRoles.symm slot)=before.stk slot
    all_goals
      fin_cases slot <;> simp_all [RootB234.RuntimeCounter.Builder.bank,background,leftRoles,StackIso.slots,Equiv.swap_apply_def]
  · simpa only [run,List.length_map] using facts.count

end RootB234.PrepEntry.StageChannels
