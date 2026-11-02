module

public import B23_4_RatWordPrep_SeqCmp_WordFinishPaths_127

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

theorem step_of_halted (source : Label → Statement C) (current : State C) (stopped : current.l=none) :
    TM2.step source current=none := by
  cases current with
  | mk point memory slots =>
    change point=none at stopped
    subst point
    rfl

def finalCfg (before : RootB234.WordFinalizer.State (PacketContext C)) : State C :=
  LabelMap.configuration finalLabel (StoreIso.configuration (OddsInit.packetIso C) before)

theorem final_shared (before : State C) (bits : List Bool)
    (active : before.l=some (.finalize .clear)) (empty : before.stk 3=[]) (output : before.stk 13=bits) :
    finalCfg (RootB234.WordFinalizer.entry before.stk ((OddsInit.packetIso C).symm before.var)
      (before.stk 0) bits)=before := by
  cases before with
  | mk point memory slots =>
    change point=some (.finalize .clear) at active
    subst point
    change (⟨some (.finalize .clear),OddsInit.packetIso C ((OddsInit.packetIso C).symm memory),
      RootB234.WordFinalizer.cells slots (slots 0) [] bits⟩ : State C)=_
    rw [Equiv.apply_symm_apply]
    congr 1
    funext slot
    fin_cases slot <;> first | rfl | exact empty.symm | exact output.symm

/-- Paid physical output movement ends at literal l=none and step=none.
FALSE cells are retained by the existing finite EOF finalizer. -/
theorem actual_halt (caller : Statement C) (before : State C) (bits : List Bool)
    (active : before.l=some (.finalize .clear)) (empty : before.stk 3=[]) (output : before.stk 13=bits) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=none ∧ TM2.step (program caller) final=none ∧
      final.var.2.2.2=before.var.2.2.2 ∧ final.stk 0=bits ∧ final.stk 3=[] ∧ final.stk 13=[] ∧
      (∀ slot,¬RootB234.WordFinalizer.Work slot→final.stk slot=before.stk slot) ∧
      run.trace.length≤4*RootB234.WordFinalizer.scale before.stk (before.stk 0) bits := by
  let memory := (OddsInit.packetIso C).symm before.var
  obtain ⟨trace,final,facts⟩ := RootB234.WordFinalizer.actual_polynomial before.stk memory (before.stk 0) bits
  have path := transport_path (OddsInit.packetIso C) finalLabel RootB234.WordFinalizer.program
    caller (fun _ => True) trace _ final facts.first facts.chain facts.last
      (by intros; trivial) (by intros; rfl)
  let run : Segment caller before (finalCfg final) :=
    ⟨trace.map finalCfg,path.1.trans (congrArg some (final_shared before bits active empty output)),path.2.1,path.2.2⟩
  have halted : (finalCfg final).l=none := by
    change final.l.map finalLabel=none
    rw [facts.halted]
    rfl
  refine ⟨finalCfg final,run,halted,?_,?_,?_,?_,?_,?_,?_⟩
  · exact step_of_halted _ _ halted
  · exact congrArg (fun context : PacketContext C => context.2.2.2) facts.context
  · change final.stk 0=bits
    rw [facts.contents]
    rfl
  · change final.stk 3=[]
    rw [facts.contents]
    rfl
  · change final.stk 13=[]
    rw [facts.contents]
    rfl
  · intro slot untouched
    change final.stk slot=before.stk slot
    exact (facts.boundary final (List.mem_of_getLast? facts.last)).2.2.2 slot untouched
  · simpa only [run,List.length_map] using facts.time

end B23_4_RatWordPrep.WordFinish
