module

public import RootB234_RuntimeCounter_Round_Normalize_003

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootB234.RuntimeCounter.Round

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PSTRWordVM RationalControllerComputation

def logicalFrame (frame : Stack → List Bool) : Stack → List Bool :=
  StackIso.slots roles.symm (cells frame [] [] [])

def smallStart (digits : List Bool) : BoolOnStacks.State Raw.support.card :=
  BoolStackStep.cfg (some ()) 0 false [false] (Raw.packet digits)

theorem smallStart_representation (digits : List Bool) :
    BoolOnStacks.representedState (smallStart digits)=Raw.finiteCfg (Raw.initial digits) := by
  change (⟨0,Raw.stableTape digits⟩ : MachineState Raw.support.card)=
    ⟨(PSTRSymbolicRelabel.finiteLabels Raw.support) (Raw.Label.test 0),Raw.stableTape digits⟩
  congr 1
  simp [PSTRSymbolicRelabel.finiteLabels,show (Raw.Label.test 0 : Raw.Label)=default from rfl]

theorem virtual_actual (frame : Stack → List Bool) (digits : List Bool) :
    ∃ (trace : List (VirtualReturn.State (Bool × Bool) OldStore))
      (final : VirtualReturn.State (Bool × Bool) OldStore),
      trace.head?=some (VirtualReturn.configuration (false,false) (logicalFrame frame) (smallStart digits)) ∧
      trace.IsChain (fun a b => TM2.step
        (VirtualReturn.program (VirtualBool.source Raw.finiteMachine) .halt) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some 1 ∧
      VirtualBool.representedState final=Raw.finiteCfg (Raw.final digits) ∧
      trace.length≤32*(digits.length+1)+1 ∧
      (∀ current∈trace,current.var.1=(false,false) ∧
        ∀ slot,slot≠0→slot≠1→current.stk slot=logicalFrame frame slot) := by
  obtain ⟨oldTrace,run,time⟩ := Raw.finite_actual digits
  have first : oldTrace.head?=some (BoolOnStacks.representedState (smallStart digits)) :=
    run.1.trans (congrArg some (smallStart_representation digits).symm)
  cases oldTrace with
  | nil => simp at first
  | cons oldStart rest =>
    have equal : oldStart=BoolOnStacks.representedState (smallStart digits) := Option.some.inj first
    subst oldStart
    obtain ⟨posts,beforeHalt,length,sourceChain,sourceLast,live,representation⟩ :=
      BoolStackTrace.lift_path Raw.finiteMachine (smallStart digits) _ _ rest rfl rfl run.2.1 run.2.2.1
    have actualHalt : TM0.step Raw.finiteMachine (BoolOnStacks.representedState beforeHalt)=none := by
      rw [representation]
      exact run.2.2.2
    obtain ⟨smallFinal,haltEdge,done,unchanged⟩ :=
      BoolStackTrace.terminate Raw.finiteMachine beforeHalt live actualHalt
    let smallTrace := (smallStart digits::posts)++[smallFinal]
    have smallFirst : smallTrace.head?=some (smallStart digits) := rfl
    have smallChain : smallTrace.IsChain (fun a b => TM2.step (BoolOnStacks.program Raw.finiteMachine) a=some b) := by
      exact NativeTrace.join_chain _ _ _ sourceLast sourceChain
        (List.isChain_cons_cons.mpr ⟨haltEdge,List.isChain_singleton _⟩)
    have smallLast : smallTrace.getLast?=some smallFinal := List.getLast?_append_cons _ _ []
    obtain ⟨liftedFirst,liftedChain,liftedLast,liftedLength,frames⟩ :=
      VirtualReturn.path_configuration (VirtualBool.source Raw.finiteMachine) .halt
        (false,false) (logicalFrame frame) smallTrace _ _ smallFirst smallChain smallLast
    refine ⟨smallTrace.map (VirtualReturn.configuration (false,false) (logicalFrame frame)),
      VirtualReturn.configuration (false,false) (logicalFrame frame) smallFinal,
      liftedFirst,liftedChain,liftedLast,VirtualReturn.returned _ _ _ done,?_,?_,frames⟩
    · exact (VirtualBool.represented_configuration _ _ _).trans (unchanged.trans representation)
    · have smallCount : smallTrace.length=(BoolOnStacks.representedState (smallStart digits)::rest).length+1 := by
        simp only [smallTrace,List.length_append,List.length_cons,List.length_nil,length]
      rw [liftedLength,smallCount]
      exact Nat.add_le_add_right time 1

def nativeConfiguration (before : VirtualReturn.State (Bool × Bool) OldStore) : BaseState :=
  LabelMap.configuration nativeLabel (StackIso.configuration roles before)

theorem native_initial (frame : Stack → List Bool) (digits : List Bool) :
    nativeConfiguration (VirtualReturn.configuration (false,false) (logicalFrame frame) (smallStart digits))=
      baseState frame 1 default (Raw.packet digits) [false] [] := by
  change (⟨some 1,default,_⟩ : BaseState)=⟨some 1,default,_⟩
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem reconstruct_base (frame : Stack → List Bool) (current : BaseState) (point : Label)
    (active : current.l=some point) (scratch : current.stk 4=[])
    (framed : ∀ slot,¬Work slot→current.stk slot=frame slot) :
    current=baseState frame point current.var (current.stk 10) (current.stk 11) [] := by
  cases current with
  | mk position memory slots =>
    change position=some point at active
    subst position
    change slots 4=[] at scratch
    congr 1
    funext slot
    by_cases n10 : slot=10
    · subst slot; rfl
    by_cases n11 : slot=11
    · subst slot; rfl
    by_cases n4 : slot=4
    · subst slot; exact scratch
    · simp only [cells,n10,n11,n4,ite_false]
      exact framed slot (by simp only [Work,not_or]; exact ⟨n4,n10,n11⟩)

theorem actual_native (frame : Stack → List Bool) (digits : List Bool) :
    ∃ (trace : List BaseState) (memory : Registers) (left tail : List Bool),
      trace.head?=some (baseState frame 1 default (Raw.packet digits) [false] []) ∧
      trace.IsChain (fun a b => TM2.step baseProgram a=some b) ∧
      trace.getLast?=some (baseState frame 2 memory (Raw.packet (Raw.outputDigits digits)++tail) left []) ∧
      trace.length≤32*(digits.length+1)+1 ∧ decoded memory=(Raw.final digits).q := by
  obtain ⟨oldTrace,oldFinal,first,chain,last,returned,representation,time,frames⟩ := virtual_actual frame digits
  let oldProgram := VirtualReturn.program (VirtualBool.source Raw.finiteMachine) (C := Bool × Bool) .halt
  let isoProgram := fun point => StackIso.statement roles (oldProgram point)
  let isoTrace := oldTrace.map (StackIso.configuration roles)
  have isoFirst : isoTrace.head?=some (StackIso.configuration roles
      (VirtualReturn.configuration (false,false) (logicalFrame frame) (smallStart digits))) := by
    rw [List.head?_map,first]; rfl
  have isoChain : isoTrace.IsChain (fun a b => TM2.step isoProgram a=some b) :=
    StackIso.chain_configuration_on roles oldProgram isoProgram oldTrace chain
      (by intro _ _ _ _; rfl)
  have isoLast : isoTrace.getLast?=some (StackIso.configuration roles oldFinal) := by
    rw [List.getLast?_map,last]; rfl
  have proper := NativeMulLink.no_early_halt_port isoProgram 1 rfl isoTrace
    (StackIso.configuration roles oldFinal) isoChain isoLast returned
  have mapped := LabelMap.actual_path_on nativeLabel isoProgram baseProgram isoTrace _ _ isoFirst isoChain isoLast (by
    intro current member point active
    have notOne : point≠1 := by intro equal; subst point; exact proper current member active
    fin_cases point
    · rfl
    · exact False.elim (notOne rfl))
  let final := nativeConfiguration oldFinal
  have mappedLast : (oldTrace.map nativeConfiguration).getLast?=some final := by
    rw [List.getLast?_map,last]; rfl
  have finalActive : final.l=some 2 := by
    change oldFinal.l.map nativeLabel=some 2
    rw [returned]; rfl
  have finalFrames := frames oldFinal (List.mem_of_getLast? last)
  have framed : ∀ slot,¬Work slot→final.stk slot=frame slot := by
    intro slot untouched
    have n0 : roles.symm slot≠0 := by
      intro equal
      have target : slot=10 := by
        calc
          slot=roles (roles.symm slot) := (Equiv.apply_symm_apply roles slot).symm
          _=10 := by rw [equal]; rfl
      exact untouched (Or.inr (Or.inl target))
    have n1 : roles.symm slot≠1 := by
      intro equal
      have target : slot=11 := by
        calc
          slot=roles (roles.symm slot) := (Equiv.apply_symm_apply roles slot).symm
          _=11 := by rw [equal]; rfl
      exact untouched (Or.inr (Or.inr target))
    change oldFinal.stk (roles.symm slot)=frame slot
    rw [finalFrames.2 _ n0 n1]
    change cells frame [] [] [] (roles (roles.symm slot))=frame slot
    rw [Equiv.apply_symm_apply]
    exact cells_frame frame [] [] [] slot untouched
  have scratch : final.stk 4=[] := by
    change oldFinal.stk 4=[]
    exact finalFrames.2 4 (by decide) (by decide)
  have control := congrArg TM0.Cfg.q representation
  change oldFinal.var.2.1=(PSTRSymbolicRelabel.finiteLabels Raw.support) (Raw.final digits).q at control
  have decodedFinal : decoded final.var=(Raw.final digits).q := by
    change PSTRSymbolicRelabel.finiteDecode Raw.support oldFinal.var.2.1=(Raw.final digits).q
    rw [control]
    exact PSTRSymbolicRelabel.finite_inverse Raw.support _ (Finset.mem_univ _)
  have rightRep := congrArg (fun current : MachineState Raw.support.card => current.Tape.right₀) representation
  have realRight : ListBlank.mk (final.stk 10)=ListBlank.mk (Raw.packet (Raw.outputDigits digits)) := by
    change ListBlank.mk (oldFinal.stk 0)=ListBlank.mk (Raw.packet (Raw.outputDigits digits))
    simpa only [VirtualBool.representedState,Raw.finiteCfg,PSTRSymbolicRelabel.relabelCfg,Raw.final,
      Raw.stableTape,Tape.mk₂,Tape.mk'_right₀] using rightRep
  obtain ⟨tail,rightEqual⟩ := true_ended_prefix _ _ (packet_last _) realRight
  have shape := reconstruct_base frame final 2 finalActive scratch framed
  have maps : isoTrace.map (LabelMap.configuration nativeLabel)=oldTrace.map nativeConfiguration := by
    rw [List.map_map]; rfl
  rw [maps] at mapped
  refine ⟨oldTrace.map nativeConfiguration,final.var,final.stk 11,tail,?_,mapped.2.1,?_,?_,decodedFinal⟩
  · exact mapped.1.trans (congrArg some (native_initial frame digits))
  · exact mappedLast.trans (congrArg some (by simpa only [rightEqual] using shape))
  · simpa only [List.length_map] using time

end RootB234.RuntimeCounter.Round
