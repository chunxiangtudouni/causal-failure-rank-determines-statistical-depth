module
public import RootB236_Controller_DFSDriver_Machine010

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver.Machine
open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.PSTRWordVM
variable {C : Type*}

def frameConfiguration (before : B23_6.DFSFrame.State (C×Ordering)) : State C :=
  LabelMap.configuration frameMap (StoreIso.configuration BestUpdate.storeIso before)
def state (point : Label) (memory : Store C) (before : Stack → List Bool) : State C := ⟨some point,memory,before⟩

theorem frame_map_not_done (point : B23_6.DFSFrame.Label) : frameMap point≠done := by
  cases point
  all_goals simp [frameMap,done,entry,rootDone,returnedGood,returnedBad]
  all_goals rename_i kind;cases kind <;> simp

theorem frame_path (finish : Statement C) {entry exit : B23_6.DFSFrame.Label}
    {memory : B23_6.DFSFrame.Store (C×Ordering)} {before output : B23_6.DFSFrame.Bank}
    {trace : List (B23_6.DFSFrame.State (C×Ordering))}
    (facts : B23_6.DFSFrame.Facts entry exit memory before output trace) :
    Run finish (frameConfiguration (B23_6.DFSFrame.state entry memory before))
      (frameConfiguration (B23_6.DFSFrame.state exit (B23_6.DFSFrame.clean memory) output)) (trace.length-1) := by
  apply Run.of_mapped finish frameConfiguration (fun x y => TM2.step B23_6.DFSFrame.source x=some y)
    trace _ _ facts.first facts.chain facts.last
  · intro current member next edge
    obtain ⟨point,active,proper⟩:=(facts.proper current member).1
    have code : ∀ other,(StoreIso.configuration BestUpdate.storeIso current).l=some other →
        program finish (frameMap other)=LabelMap.statement frameMap
          (StoreIso.statement BestUpdate.storeIso (B23_6.DFSFrame.source other)) := by
      intro other activeOther
      have same : other=point := Option.some.inj (activeOther.symm.trans active)
      subst other;exact frame_code finish point proper
    unfold frameConfiguration
    rw [LabelMap.step_configuration_on frameMap (StoreIso.machine BestUpdate.storeIso B23_6.DFSFrame.source)
      (program finish) _ code,StoreIso.step_configuration BestUpdate.storeIso B23_6.DFSFrame.source,edge]
    rfl
  · intro current member
    cases active : current.l with
    | none => change current.l.map frameMap≠some done;rw [active];intro impossible;cases impossible
    | some point =>
      change current.l.map frameMap≠some done
      rw [active,Option.map_some]
      exact fun same => frame_map_not_done point (Option.some.inj same)

theorem frame_state (point : B23_6.DFSFrame.Label) (memory : Store C) (before : Stack → List Bool) :
    frameConfiguration (B23_6.DFSFrame.state point (BestUpdate.storeIso.symm memory) before)=state (frameMap point) memory before := by
  simp only [frameConfiguration,B23_6.DFSFrame.state,LabelMap.configuration,StoreIso.configuration,
    Equiv.apply_symm_apply,Option.map_some,state]
theorem frame_state_clean (point : B23_6.DFSFrame.Label) (memory : Store C) (before : Stack → List Bool) :
    frameConfiguration (B23_6.DFSFrame.state point (B23_6.DFSFrame.clean (BestUpdate.storeIso.symm memory)) before)=
      state (frameMap point) (memory.1,false,false,memory.2.2.2) before := rfl

/-- Real kind-labelled push and seed copyback, in the single global source. -/
theorem push (finish : Statement C) (memory : Store C) (parent : B23_6.DFSFrame.Bank) (kind : Bool) :
    ∃ steps,Run finish (state (.inr (.pushBoot kind)) memory parent)
      (state start (memory.1,false,false,memory.2.2.2) (B23_6.DFSFrame.pushBank kind parent)) steps ∧
      steps≤51*(B23_6.DFSFrame.scale parent) := by
  obtain ⟨trace,facts,_clock,_charge⟩:=B23_6.DFSFrame.Public.push_actual (BestUpdate.storeIso.symm memory) parent kind
  have actual:=frame_path finish facts
  rw [frame_state,frame_state_clean] at actual
  refine ⟨trace.length-1,actual,?_⟩
  exact (Nat.sub_le trace.length 1).trans facts.time

/-- One pop entry reads the physical kind; no runtime kind oracle selects a program. -/
theorem pop (finish : Statement C) (memory : Store C) (parent child : B23_6.DFSFrame.Bank) (kind flag : Bool)
    (spool : child 13=flag::B23_6.DFSFrame.framePrefix parent kind 14) :
    ∃ steps,Run finish (state (.inr .popBoot) memory child)
      (state (.inl (if kind then returnedGood else returnedBad)) (memory.1,false,false,memory.2.2.2)
        (B23_6.DFSFrame.restoreBank parent (child 15))) steps ∧ steps≤51*(B23_6.DFSFrame.scale child) := by
  obtain ⟨trace,facts,_clock,_charge⟩:=B23_6.DFSFrame.Public.pop_actual (BestUpdate.storeIso.symm memory) parent child kind flag spool
  have actual:=frame_path finish facts
  rw [frame_state,frame_state_clean] at actual
  refine ⟨trace.length-1,?_,(Nat.sub_le trace.length 1).trans facts.time⟩
  cases kind <;> exact actual

/-- The new spool is nonempty independently of parent fields, including all empty/FALSE payloads. -/
theorem frame_nonempty (parent : B23_6.DFSFrame.Bank) (kind : Bool) :
    B23_6.DFSFrame.framePrefix parent kind 14≠[] := by
  have size:=(B23_6.DFSFrame.Public.spool_exact parent kind).2
  intro empty
  change (false::B23_6.DFSFrame.framePrefix parent kind 14).length=_ at size
  rw [empty] at size
  simp only [List.length_cons,List.length_nil] at size
  omega
end RootB236.Controller.DFSDriver.Machine
