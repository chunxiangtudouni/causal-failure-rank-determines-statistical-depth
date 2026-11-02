module

public import Paid.PDROC_BitVM_Kernel_NatMarshal_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.BitVM.Kernel.CellRead

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal

abbrev Label := PDROC.BitVM.Log.TwoStack.Label
abbrev Store := Option Bool
abbrev State := TM2.Cfg Alphabet Label Store

/-- The checked whole-word copier, reading an actual original register
and preserving its Cell tag and every payload byte. -/
def program (source : Register) := Lift.machine (NatMarshalGlobal.embedding source) Copy.program

def before (contents : Stack → List Bool) : State := ⟨some 0,none,contents⟩

theorem runs (logical : PaperProofs.Paid.Computation.State) (source : Register)
    (target : List Bool) (contents : Stack → List Bool)
    (represented : ∀ reg,contents (registerSlot reg)=encodeCellBits (logical.register reg))
    (targetWord : contents 0=target) (emptyScratch : contents 24=[]) :
    ∃ (run : List State) (final : State),
      run.head?=some (before contents) ∧
      run.IsChain (fun x y=>TM2.step (program source) x=some y) ∧
      run.getLast?=some final ∧ TM2.step (program source) final=none ∧
      final.l=none ∧ final.var=none ∧ RegistersRepresent logical final ∧
      final.stk 0=encodeCellBits (logical.register source)++target ∧ final.stk 24=[] ∧
      run.length=2*(encodeCellBits (logical.register source)).length+3 ∧
      ∀ other,(∀ index,other ≠ NatMarshalGlobal.embedding source index) → final.stk other=contents other := by
  let word := encodeCellBits (logical.register source)
  have projection : Lift.cfg (NatMarshalGlobal.embedding source) (before contents)=
      Copy.state (some 0) none word target [] := by
    have data : Lift.slots (NatMarshalGlobal.embedding source) contents=
        PDROC.BitVM.Log.TwoStack.threeStacks word target [] := by
      funext index
      fin_cases index
      · exact represented source
      · exact targetWord
      · exact emptyScratch
    change (⟨some 0,none,Lift.slots (NatMarshalGlobal.embedding source) contents⟩ :
      PDROC.BitVM.Log.TwoStack.State)=_
    rw [data]
    rfl
  obtain ⟨old,head,chain,last,halt,size,_source,_target,_scratch⟩ := Copy.copy_runs word target
  cases old with
  | nil => simp only [List.head?_nil,reduceCtorEq] at head
  | cons start rest =>
    have same : start=Copy.state (some 0) none word target [] := Option.some.inj head
    subst start
    obtain ⟨posts,final,length,actual,actualLast,view,frame⟩ :=
      Lift.path (NatMarshalGlobal.embedding source) Copy.program (before contents)
        (Copy.state (some 0) none word target []) (Copy.state none none word (word++target) []) rest
        projection chain last
    have sourceFinal : final.stk (registerSlot source)=word := by
      have part := congrArg (fun state : PDROC.BitVM.Log.TwoStack.State=>state.stk 0) view
      exact part
    refine ⟨before contents::posts,final,rfl,actual,actualLast,?_,?_,?_,?_,?_,?_,?_,frame⟩
    · apply Lift.halt_project (NatMarshalGlobal.embedding source) Copy.program final
      rw [view]
      exact halt
    · exact congrArg TM2.Cfg.l view
    · exact congrArg TM2.Cfg.var view
    · intro reg
      by_cases same : reg=source
      · subst reg
        exact sourceFinal
      · exact (frame _ (NatMarshalGlobal.outside_register source reg same)).trans (represented reg)
    · exact congrArg (fun state : PDROC.BitVM.Log.TwoStack.State=>state.stk 1) view
    · exact congrArg (fun state : PDROC.BitVM.Log.TwoStack.State=>state.stk 2) view
    · simp only [List.length_cons,length] at size ⊢
      exact size

theorem supports (source : Register) : TM2.Supports (program source) (Finset.univ : Finset Label) :=
  Lift.supports (NatMarshalGlobal.embedding source) Copy.program _ Copy.supports

end PDROC.BitVM.Kernel.CellRead
