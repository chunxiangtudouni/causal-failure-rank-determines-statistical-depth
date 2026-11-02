module

public import PSTR_WordBool_RatCmp_Syntax_001

/-! One shared positive quartic scale for the complete signed LE callee.
Time, boundary mass, internal nodes and clock use the SAME actual trace. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatCmp.Link

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

theorem step_resources (before after : State C) (bound : Nat)
    (edge : TM2.step (program .halt) before=some after)
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    (∀ slot,(after.stk slot).length≤bound+3) ∧
      ∀ slot,¬Work slot→after.stk slot=before.stk slot := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have equal : after=TM2.stepAux (program .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      refine ⟨?_,?_⟩
      · intro slot
        exact (AuxWorkspace.endpoint_bound _ _ _ bound bounded slot).trans
          (Nat.add_le_add_left (program_pushes point) bound)
      · intro slot untouched
        exact StackIso.nodes_frame Work _ (program_writes point) memory contents slot untouched
          _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_resources (trace : List (State C)) (before : State C)
    (background : Stack → List Bool) (bound : Nat)
    (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b=>TM2.step (program .halt) a=some b))
    (bounded : ∀ slot,(before.stk slot).length≤bound)
    (frames : ∀ slot,¬Work slot→before.stk slot=background slot) :
    ∀ current∈trace,
      (∀ slot,(current.stk slot).length≤bound+3*trace.length) ∧
      ∀ slot,¬Work slot→current.stk slot=background slot := by
  induction trace generalizing before bound with
  | nil => simp
  | cons firstState rest ih =>
    have equal : firstState=before:=Option.some.inj first
    subst firstState
    cases rest with
    | nil =>
      intro current member
      have same:=List.mem_singleton.mp member
      subst current
      refine ⟨?_,frames⟩
      intro slot
      exact (bounded slot).trans (by simp)
    | cons next rest =>
      obtain ⟨edge,tailChain⟩:=List.isChain_cons_cons.mp chain
      have step:=step_resources before next bound edge bounded
      have nextFrames : ∀ slot,¬Work slot→next.stk slot=background slot :=
        fun slot untouched=>(step.2 slot untouched).trans (frames slot untouched)
      intro current member
      rcases List.mem_cons.mp member with same|later
      · subst current
        exact ⟨fun slot=>(bounded slot).trans (Nat.le_add_right _ _),frames⟩
      · have tail:=ih next (bound+3) rfl tailChain step.1 nextFrames current later
        refine ⟨?_,tail.2⟩
        intro slot
        have perSlot:=tail.1 slot
        simp only [List.length_cons] at perSlot ⊢
        omega

theorem internal_resources (current : State C) (point : Label) (bound : Nat)
    (bounded : ∀ slot,(current.stk slot).length≤bound) :
    (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
      (∀ slot,(node.2 slot).length≤bound+3) ∧
        ∀ slot,¬Work slot→node.2 slot=current.stk slot) ∧
      ScannerStatement.clock (program .halt point) current.var current.stk≤16*(bound+4) := by
  refine ⟨?_,?_⟩
  · intro node member
    refine ⟨?_,?_⟩
    · intro slot
      exact (AuxWorkspace.node_bound _ _ _ bound bounded node member slot).trans
        (Nat.add_le_add_left (program_pushes point) bound)
    · intro slot untouched
      exact StackIso.nodes_frame Work _ (program_writes point) current.var current.stk slot untouched node member
  · have clock:=ScannerClock.clock_bound (program .halt point) current.var current.stk bound bounded
    exact clock.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions point))
      (Nat.add_le_add_right (Nat.add_le_add_left (program_pushes point) bound) 1))

theorem chain_caller (caller : Statement C) (trace : List (State C))
    (chain : trace.IsChain (fun a b=>TM2.step (program .halt) a=some b))
    (proper : ∀ current∈trace.dropLast,current.l≠some done) :
    trace.IsChain (fun a b=>TM2.step (program caller) a=some b) := by
  induction trace with
  | nil => exact List.isChain_nil
  | cons before rest ih =>
    cases rest with
    | nil => exact List.isChain_singleton _
    | cons next rest =>
      obtain ⟨edge,tailChain⟩:=List.isChain_cons_cons.mp chain
      refine List.isChain_cons_cons.mpr ⟨?_,ih tailChain ?_⟩
      · have beforeProper:=proper before (by rw [List.dropLast_cons_cons];exact List.mem_cons_self)
        cases before with
        | mk position memory contents =>
          cases position with
          | none => cases edge
          | some point =>
            have notDone : point≠done:=by intro same;subst point;exact beforeProper rfl
            change some (TM2.stepAux (program caller point) memory contents)=some next
            rw [program_proper caller point notDone]
            exact edge
      · intro current member
        apply proper current
        rw [List.dropLast_cons_cons]
        exact List.mem_cons_of_mem _ member

def coefficient : Nat := 1024*(RatAddSub.addSubCoefficient+1)
def degree : Nat := 4

theorem coefficient_pos : 0<coefficient := by
  change 0<1024*(RatAddSub.addSubCoefficient+1)
  exact Nat.mul_pos (by decide) (Nat.succ_pos _)
theorem degree_pos : 0<degree := by decide

def budget (background : Stack → List Bool) (x y : Rat) : Nat :=
  1024*(IsolatedRat.outside background+1)+coefficient*((encode [.rational x,.rational y]).length+1)^degree

theorem budget_ge (background : Stack → List Bool) (x y : Rat) :
    19*baseBudget background x y+200≤budget background x y := by
  have expansion : budget background x y=1024*baseBudget background x y+
      1024*((encode [.rational x,.rational y]).length+1)^4+1024 := by
    dsimp only [budget,coefficient,degree,baseBudget,rawBound]
    ring
  rw [expansion]
  omega

theorem occupied_bound (contents : Stack → List Bool) (bound : Nat)
    (bounded : ∀ slot,(contents slot).length≤bound) : RatOutput.occupied contents≤16*bound := by
  calc
    RatOutput.occupied contents≤∑ _slot : Stack,bound:=Finset.sum_le_sum (fun slot _=>bounded slot)
    _=16*bound:=by simp

theorem actual_bounded (caller : Statement C) (context : C) (flags : Reader.Store)
    (readerMemory : RatOutput.Store) (nativeMemory : BoolOnStacks.Store states)
    (background : Stack → List Bool) (x y : Rat) :
    ∃ (trace : List (State C)) (final : State C),
      trace.head?=some (entry context flags readerMemory nativeMemory background x y) ∧
      trace.IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some done ∧ final.var.1.1.1=context ∧
      final.stk 13=[] ∧ final.stk 14=[] ∧ final.stk 7=background 7 ∧ final.stk 15=background 15 ∧
      final.stk 3=decide (x≤y)::background 3 ∧
      (∀ slot,slot≠3→slot≠13→slot≠14→slot≠15→final.stk slot=background slot) ∧
      trace.length≤budget background x y ∧
      (∀ current∈trace,current.var.1.1.1=context ∧
        (∀ slot,(current.stk slot).length≤budget background x y) ∧
        RatOutput.occupied current.stk≤16*budget background x y ∧
        ∀ slot,¬Work slot→current.stk slot=background slot) ∧
      (∀ current∈trace.dropLast,current.l≠some done ∧
        ∀ point,current.l=some point→
          (∀ node∈AuxWorkspace.nodes (program caller point) current.var current.stk,
            (∀ slot,(node.2 slot).length≤budget background x y+3) ∧
            ∀ slot,¬Work slot→node.2 slot=background slot) ∧
          ScannerStatement.clock (program caller point) current.var current.stk≤16*(budget background x y+4)) := by
  obtain ⟨trace,final,first,chain,last,active,contextFinal,right,left,counter,sourceRestored,targetResult,frame,count,contexts,initialMass⟩:=
    actual_path .halt context flags readerMemory nativeMemory background x y
  have proper:=NativeMulLink.no_early_halt_port (program .halt) done rfl trace final chain last active
  let before:=entry context flags readerMemory nativeMemory background x y
  have bounds:=trace_resources trace before background (baseBudget background x y+8) first chain
    (fun slot=>(RatOutput.Link.point_mass before.stk slot).trans initialMass)
    (fun slot untouched=>entry_frame context flags readerMemory nativeMemory background x y slot untouched)
  have scale:=budget_ge background x y
  have linear : baseBudget background x y+8+3*trace.length≤budget background x y := by omega
  have time : trace.length≤budget background x y := by omega
  have bounded : ∀ current∈trace,∀ slot,(current.stk slot).length≤budget background x y :=
    fun current member slot=>((bounds current member).1 slot).trans linear
  refine ⟨trace,final,first,chain_caller caller trace chain proper,last,active,contextFinal,right,left,counter,
    sourceRestored,targetResult,frame,time,?_,?_⟩
  · intro current member
    exact ⟨contexts current member,bounded current member,occupied_bound current.stk _ (bounded current member),(bounds current member).2⟩
  · intro current member
    refine ⟨proper current member,?_⟩
    intro point selected
    have notDone : point≠done:=by intro same;subst point;exact proper current member selected
    rw [program_proper caller point notDone]
    have nodes:=internal_resources current point _ (bounded current (List.mem_of_mem_dropLast member))
    refine ⟨?_,nodes.2⟩
    intro node nodeMember
    have nodeFacts:=nodes.1 node nodeMember
    refine ⟨nodeFacts.1,?_⟩
    intro slot untouched
    exact (nodeFacts.2 slot untouched).trans ((bounds current (List.mem_of_mem_dropLast member)).2 slot untouched)

end PaperProofs.Common.Native.PSTRWordBool.RatCmp.Link
