module

public import B23_4_RatWordPrep_SeqCmp_ChannelsCode_076

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.Channels

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

theorem transport_path {σ Λ : Type*} (iso : σ ≃ Store C) (rename : Λ → Label)
    (old : Λ → TM2.Stmt RatInput.Alphabet Λ σ) (caller : Statement C)
    (allowed : Λ → Prop) (trace : List (TM2.Cfg RatInput.Alphabet Λ σ))
    (before final : TM2.Cfg RatInput.Alphabet Λ σ)
    (first : trace.head?=some before) (chain : trace.IsChain (fun a b => TM2.step old a=some b))
    (last : trace.getLast?=some final)
    (proper : ∀ current∈trace.dropLast,∀ point,current.l=some point→allowed point)
    (same : ∀ point,allowed point→program caller (rename point)=
      LabelMap.statement rename (StoreIso.statement iso (old point))) :
    let mapCfg := fun current => LabelMap.configuration rename (StoreIso.configuration iso current)
    (trace.map mapCfg).head?=some (mapCfg before) ∧
    (trace.map mapCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (trace.map mapCfg).getLast?=some (mapCfg final) := by
  let changed := StoreIso.machine iso old
  have storePath := StoreIso.actual_path_on iso old changed trace before final first chain last
    (by intro current member point selected; rfl)
  have mapped := LabelMap.actual_path_on rename changed (program caller)
    _ _ _ storePath.1 storePath.2.1 storePath.2.2.1 (by
      intro current member point selected
      rw [←List.map_dropLast] at member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact same point (proper original present point selected))
  simp only [List.map_map,Function.comp_def] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem prelude_path (caller : Statement C) (registers : Aux) (run : List (OriginalPrelude.State C))
    (before final : OriginalPrelude.State C) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (OriginalPrelude.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    (run.map (preludeCfg registers)).head?=some (preludeCfg registers before) ∧
    (run.map (preludeCfg registers)).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map (preludeCfg registers)).getLast?=some (preludeCfg registers final) := by
  let old := OriginalPrelude.program (C := C) .halt
  let lifted : OriginalPrelude.Label → TM2.Stmt RatInput.Alphabet OriginalPrelude.Label (Store C) :=
    ContextLift.machine old
  have contextual := ContextLift.actual_path old registers run before final first chain last
  have proper := NativeMulLink.no_early_halt_port lifted .done rfl _ _ contextual.2.1 contextual.2.2.1 active
  have mapped := LabelMap.actual_path_on preludeLabel lifted (program caller)
    _ _ _ contextual.1 contextual.2.1 contextual.2.2.1 (by
      intro current member point selected
      have notDone : point≠.done := by intro equal; subst point; exact proper current member selected
      simp only [preludeLabel,notDone,ite_false,program]
      rfl)
  simp only [List.map_map,Function.comp_def] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem build_path (caller : Statement C)
    (run : List (RootB234.RuntimeCounter.Builder.State (PacketContext C)))
    (before final : RootB234.RuntimeCounter.Builder.State (PacketContext C))
    (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step RootB234.RuntimeCounter.Builder.Public.from8Twice a=some b))
    (last : run.getLast?=some final) (active : final.l=some 5) :
    (run.map buildCfg).head?=some (buildCfg before) ∧
    (run.map buildCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map buildCfg).getLast?=some (buildCfg final) := by
  have proper := NativeMulLink.no_early_halt_port RootB234.RuntimeCounter.Builder.Public.from8Twice 5 rfl
    run final chain last active
  exact transport_path (packetIso C) buildLabel _ caller (fun point => point≠5) run before final first chain last
    (by intro current member point selected equal; subst point; exact proper current member selected)
    (by intro point different; simp only [buildLabel,different,ite_false,program])

theorem read_path (caller : Statement C) (run : List (RawGetter.State (RawContext C)))
    (before final : RawGetter.State (RawContext C)) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (RawGetter.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    (run.map readCfg).head?=some (readCfg before) ∧
    (run.map readCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map readCfg).getLast?=some (readCfg final) := by
  have proper := NativeMulLink.no_early_halt_port (RawGetter.program .halt) .done rfl run final chain last active
  exact transport_path (rawIso C) readLabel _ caller (fun point => point≠.done) run before final first chain last
    (by intro current member point selected equal; subst point; exact proper current member selected)
    (by intro point different; simp only [readLabel,different,ite_false,program])

theorem move_path (caller : Statement C)
    (run : List (RootB234.RatPacketTransport.State (PacketContext C)))
    (before final : RootB234.RatPacketTransport.State (PacketContext C))
    (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step RootB234.RatPacketTransport.Public.move15To2 a=some b))
    (last : run.getLast?=some final) (active : final.l=some 4) :
    (run.map moveCfg).head?=some (moveCfg before) ∧
    (run.map moveCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map moveCfg).getLast?=some (moveCfg final) := by
  have proper := NativeMulLink.no_early_halt_port RootB234.RatPacketTransport.Public.move15To2 4 rfl
    run final chain last active
  exact transport_path (packetIso C) moveLabel _ caller (fun point => point≠4) run before final first chain last
    (by intro current member point selected equal; subst point; exact proper current member selected)
    (by intro point different; simp only [moveLabel,different,ite_false,program])

theorem round_path (caller : Statement C)
    {frame : RatInput.Stack → List Bool} {memory : RootB234.RuntimeCounter.Round.Store (RoundContext C)}
    {digits : List Bool} {run : List (RootB234.RuntimeCounter.Round.State (RoundContext C))}
    {final : RootB234.RuntimeCounter.Round.State (RoundContext C)}
    (facts : RootB234.RuntimeCounter.Round.Facts RootB234.RuntimeCounter.Round.program frame memory digits run final) :
    (run.map roundCfg).head?=some (roundCfg (RootB234.RuntimeCounter.Round.entry frame memory digits)) ∧
    (run.map roundCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map roundCfg).getLast?=some (roundCfg final) := by
  exact transport_path (roundIso C) roundLabel _ caller (fun point => point≠7 ∧ point≠8)
    run _ final facts.first facts.chain facts.last
    (by
      intro current member point selected
      exact ⟨fun equal => (facts.proper current member).1 (equal ▸ selected),
        fun equal => (facts.proper current member).2 (equal ▸ selected)⟩)
    (by intro point different; simp only [roundLabel,different.1,different.2,ite_false,program])

structure Segment (caller : Statement C) (before final : State C) where
  trace : List (State C)
  first : trace.head?=some before
  chain : trace.IsChain (fun a b => TM2.step (program caller) a=some b)
  last : trace.getLast?=some final

def Segment.append {caller : Statement C} {before middle final : State C}
    (front : Segment caller before middle) (back : Segment caller middle final) : Segment caller before final := by
  have shape : middle::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩ := List.head?_eq_some_iff.mp back.first
    rw [same]; rfl
  refine ⟨front.trace++back.trace.tail,?_,?_,?_⟩
  · rw [List.head?_append,front.first]; rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)

end B23_4_RatWordPrep.Channels
