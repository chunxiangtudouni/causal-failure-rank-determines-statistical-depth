module
public import RootB236_Controller_MaskArchive_Code001

/-! The one actual WholeCopy path transported through fixed stack roles,
including every internal node and the physical scanner's exact clock. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB236.Controller.MaskArchive
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep
variable {C : Type*}

theorem whole_internal_mass {background : Stack → List Bool} {memory : Store C}
    {input backup scratch : List Bool} {run : List (State C)}
    (facts : WholeCopy.Facts (WholeCopy.program .halt) background memory input backup scratch run)
    (current : State C) (member : current∈run) (point : Label) :
    ∀ node∈AuxWorkspace.nodes (WholeCopy.program .halt point) current.var current.stk,
      RatInput.occupied node.2≤coefficient*WholeCopy.inputScale background input backup scratch := by
  let before:=WholeCopy.state background .boot memory input backup scratch
  let M:=RatInput.occupied before.stk
  let S:=M+16*run.length
  have frames : ∀ slot,¬WholeCopy.Work slot→before.stk slot=background slot := by
    intro slot untouched
    have a : slot≠0 := by intro same;subst slot;exact untouched (by decide)
    have b : slot≠2 := by intro same;subst slot;exact untouched (by decide)
    have c : slot≠3 := by intro same;subst slot;exact untouched (by decide)
    simp only [before,WholeCopy.state,WholeCopy.bank,a,b,c,ite_false]
  have bounds:=WholeCopy.trace_resources run before background M facts.first facts.chain
    (RatInput.Encoder.point_mass before.stk) frames
  have sourceBound : input.length≤M := RatInput.Encoder.point_mass before.stk 0
  have cap : 16*(S+16)≤coefficient*WholeCopy.inputScale background input backup scratch := by
    dsimp only [S]
    rw [facts.count]
    change 16*(M+16*(2*input.length+4)+16)≤4096*(M+1)
    omega
  have internal:=WholeCopy.internal_resources current point S (bounds current member).1
  intro node inside
  exact (RatInput.Encoder.occupied_bound node.2 (S+16) ((internal.1 node inside).2.1)).trans cap

abbrev traceClockSum {C : Type*} := WholeCopy.traceClockSum (C:=C)
abbrev chargedCost {C : Type*} := WholeCopy.chargedCost (C:=C)

structure Facts (roles : Stack ≃ Stack) (caller : Statement C) (background : Stack → List Bool)
    (memory : Store C) (input backup scratch : List Bool) (run : List (State C)) : Prop where
  first : run.head?=some (state roles background .boot memory input backup scratch)
  chain : run.IsChain (fun before after => TM2.step (program roles caller) before=some after)
  last : run.getLast?=some (state roles background .done (memory.1,true,true) input (input.reverse++backup) scratch)
  count : run.length=2*input.length+4
  time : run.length≤coefficient*inputScale roles background input backup scratch
  boundaries : ∀ current∈run,current.var.1=memory.1 ∧
    (∀ slot,(current.stk slot).length≤coefficient*inputScale roles background input backup scratch) ∧
    RatInput.occupied current.stk≤coefficient*inputScale roles background input backup scratch ∧
    ∀ slot,¬Work roles slot→current.stk slot=background slot
  proper : ∀ current∈run.dropLast,current.l≠some .done ∧
    ∀ point,current.l=some point→
      (∀ node∈AuxWorkspace.nodes (program roles caller point) current.var current.stk,
        node.1.1=memory.1 ∧
        (∀ slot,(node.2 slot).length≤coefficient*inputScale roles background input backup scratch) ∧
        RatInput.occupied node.2≤coefficient*inputScale roles background input backup scratch ∧
        ∀ slot,¬Work roles slot→node.2 slot=background slot) ∧
      ScannerStatement.clock (program roles caller point) current.var current.stk≤coefficient*inputScale roles background input backup scratch
  clockSum : traceClockSum (program roles caller) run≤coefficient^2*(inputScale roles background input backup scratch)^2
  charge : chargedCost (program roles caller) run≤(coefficient^2+coefficient)*(inputScale roles background input backup scratch)^2

theorem actual (roles : Stack ≃ Stack) (caller : Statement C) (background : Stack → List Bool)
    (memory : Store C) (input backup scratch : List Bool) :
    ∃ run,Facts roles caller background memory input backup scratch run := by
  let bg:=StackIso.slots roles.symm background
  obtain ⟨run,facts⟩:=WholeCopy.actual_bounded bg memory input backup scratch
  have scale : inputScale roles background input backup scratch=WholeCopy.inputScale bg input backup scratch:=scale_eq _ _ _ _ _
  have codeOn : ∀ current∈run.dropLast,∀ point,current.l=some point→
      program roles caller point=StackIso.statement roles (WholeCopy.program .halt point) := by
    intro current member point selected
    apply program_internal
    intro same
    subst point
    exact (facts.proper current member).1 selected
  have clockOn : ∀ current∈run.dropLast,
      WholeCopy.statementClock (program roles caller) (StackIso.configuration roles current)=
        WholeCopy.statementClock (WholeCopy.program .halt) current := by
    intro current member
    cases selected : current.l with
    | none => simp only [WholeCopy.statementClock,StackIso.configuration,selected]
    | some point =>
      simp only [WholeCopy.statementClock,StackIso.configuration,selected]
      rw [codeOn current member point selected,clock_statement]
  have clocks : traceClockSum (program roles caller) (run.map (StackIso.configuration roles))=
      WholeCopy.traceClockSum (WholeCopy.program .halt) run := by
    unfold traceClockSum WholeCopy.traceClockSum
    rw [←List.map_dropLast,List.map_map]
    congr 1
    apply List.map_congr_left
    exact clockOn
  have charge : chargedCost (program roles caller) (run.map (StackIso.configuration roles))=
      WholeCopy.chargedCost (WholeCopy.program .halt) run := by
    change (run.map (StackIso.configuration roles)).length+
      traceClockSum (program roles caller) (run.map (StackIso.configuration roles))=_
    rw [List.length_map,clocks];rfl
  refine ⟨run.map (StackIso.configuration roles),⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · rw [List.head?_map,facts.first,Option.map_some,state_eq]
  · exact StackIso.chain_configuration_on roles _ _ run facts.chain codeOn
  · rw [List.getLast?_map,facts.last,Option.map_some,state_eq]
  · simpa only [List.length_map] using facts.count
  · simpa only [List.length_map,scale,coefficient] using facts.time
  · intro current member
    obtain ⟨old,present,rfl⟩:=List.mem_map.mp member
    have bound:=facts.boundaries old present
    refine ⟨bound.1,fun slot => ?_,?_,?_⟩
    · simpa only [StackIso.configuration,StackIso.slots,scale,coefficient] using bound.2.1 (roles.symm slot)
    · simpa only [StackIso.configuration,occupied_slots,scale,coefficient] using bound.2.2.1
    · intro slot untouched
      have frame:=bound.2.2.2 (roles.symm slot) ((work_iff roles slot).not.mp untouched)
      simpa only [StackIso.configuration,StackIso.slots,bg,Equiv.symm_symm,Equiv.apply_symm_apply] using frame
  · intro current member
    rw [←List.map_dropLast] at member
    obtain ⟨old,present,rfl⟩:=List.mem_map.mp member
    have bound:=facts.proper old present
    refine ⟨bound.1,?_⟩
    intro point selected
    have internal:=bound.2 point selected
    refine ⟨?_,?_⟩
    · intro node inside
      rw [codeOn old present point selected,StackIso.configuration,StackIso.nodes_statement] at inside
      obtain ⟨oldNode,oldInside,rfl⟩:=List.mem_map.mp inside
      have nodeBound:=internal.1 oldNode oldInside
      refine ⟨nodeBound.1,fun slot => ?_,?_,?_⟩
      · simpa only [StackIso.slots,scale,coefficient] using nodeBound.2.1 (roles.symm slot)
      · have mass:=whole_internal_mass facts old (List.mem_of_mem_dropLast present) point oldNode oldInside
        simpa only [occupied_slots,scale] using mass
      · intro slot untouched
        have frame:=nodeBound.2.2 (roles.symm slot) ((work_iff roles slot).not.mp untouched)
        simpa only [StackIso.slots,bg,Equiv.symm_symm,Equiv.apply_symm_apply] using frame
    · rw [codeOn old present point selected]
      simpa only [StackIso.configuration,clock_statement,scale,coefficient] using internal.2
  · rw [clocks,scale];exact WholeCopy.traceClockSum_le facts
  · rw [charge,scale];exact WholeCopy.chargedCost_le facts

end RootB236.Controller.MaskArchive
