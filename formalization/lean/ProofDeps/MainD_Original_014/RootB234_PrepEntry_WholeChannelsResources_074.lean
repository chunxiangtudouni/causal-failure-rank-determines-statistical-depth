module

public import RootB234_PrepEntry_WholeChannelsSyntax_073
public import RootB234_PrepEntry_WholeChannelsRun_072

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.WholeChannels

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

variable {C : Type*}

theorem step_context (before after : State C) (edge : TM2.step (program .halt) before=some after) :
    callerContext after.var=callerContext before.var := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (program .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      exact RawGetter.nodes_readonly callerContext _ (program_readonly point) memory contents _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_context (trace : List (State C)) (before : State C) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (program .halt) a=some b)) :
    ∀ current∈trace,callerContext current.var=callerContext before.var := by
  induction trace generalizing before with
  | nil => simp
  | cons start rest ih =>
    have same : start=before := Option.some.inj first
    subst start
    cases rest with
    | nil =>
      intro current member
      have same:=List.mem_singleton.mp member
      subst current
      rfl
    | cons next rest =>
      obtain ⟨edge,tailChain⟩:=List.isChain_cons_cons.mp chain
      intro current member
      rcases List.mem_cons.mp member with rfl|later
      · rfl
      · exact (ih next rfl tailChain current later).trans (step_context before next edge)


theorem step_resources (before after : State C) (bound : Nat)
    (edge : TM2.step (program .halt) before=some after)
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    (∀ slot,(after.stk slot).length≤bound+16) ∧
      ∀ slot,¬Work slot→after.stk slot=before.stk slot := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (program .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      exact ⟨fun slot => (AuxWorkspace.endpoint_bound _ _ _ bound bounded slot).trans
        (Nat.add_le_add_left (program_pushes point) bound),
        fun slot untouched => StackIso.nodes_frame _ _ (program_writes point) memory contents slot untouched
          _ (AuxWorkspace.endpoint_mem _ _ _)⟩

theorem trace_resources (trace : List (State C)) (before : State C) (background : RatInput.Stack → List Bool)
    (bound : Nat) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (program .halt) a=some b))
    (bounded : ∀ slot,(before.stk slot).length≤bound)
    (frame : ∀ slot,¬Work slot→before.stk slot=background slot) :
    ∀ current∈trace,(∀ slot,(current.stk slot).length≤bound+16*trace.length) ∧
      ∀ slot,¬Work slot→current.stk slot=background slot := by
  induction trace generalizing before bound with
  | nil => simp
  | cons firstState rest ih =>
    have same : firstState=before := Option.some.inj first
    subst firstState
    cases rest with
    | nil =>
      intro current member
      have same := List.mem_singleton.mp member
      subst current
      exact ⟨fun slot => (bounded slot).trans (by simp),frame⟩
    | cons next rest =>
      obtain ⟨edge,tailChain⟩ := List.isChain_cons_cons.mp chain
      have step := step_resources before next bound edge bounded
      intro current member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨fun slot => (bounded slot).trans (Nat.le_add_right _ _),frame⟩
      · have tail := ih next (bound+16) rfl tailChain step.1
          (fun slot untouched => (step.2 slot untouched).trans (frame slot untouched)) current later
        refine ⟨?_,tail.2⟩
        intro slot
        have h := tail.1 slot
        simp only [List.length_cons] at h ⊢
        omega

theorem internal_resources (current : State C) (point : Label) (bound : Nat)
    (bounded : ∀ slot,(current.stk slot).length≤bound) :
    (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
      callerContext node.1=callerContext current.var ∧ (∀ slot,(node.2 slot).length≤bound+16) ∧
        ∀ slot,¬Work slot→node.2 slot=current.stk slot) ∧
      ScannerStatement.clock (program .halt point) current.var current.stk≤32*(bound+17) := by
  refine ⟨?_,?_⟩
  · intro node member
    exact ⟨RawGetter.nodes_readonly callerContext _ (program_readonly point) current.var current.stk node member,
      fun slot => (AuxWorkspace.node_bound _ _ _ bound bounded node member slot).trans
        (Nat.add_le_add_left (program_pushes point) bound),
      fun slot untouched => StackIso.nodes_frame _ _ (program_writes point) current.var current.stk slot untouched node member⟩
  · exact (ScannerClock.clock_bound (program .halt point) current.var current.stk bound bounded).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions point))
        (Nat.add_le_add_right (Nat.add_le_add_left (program_pushes point) bound) 1))


def macroCoefficient : Nat := Budget.coefficient+StageChannels.coefficient*(Budget.coefficient+1)^4

def coefficient : Nat := 4096*(macroCoefficient+1)

def space (length : Nat) : Nat := length+16*(macroCoefficient*(length+1)^12)

variable {I : Instance}

theorem output_mass_le (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    RatInput.occupied (Budget.outputBank (preparationInput input contract budget) I.stageCount I.toolCount budget)≤
      Budget.coefficient*((preparationInput input contract budget).length+1)^3 := by
  obtain ⟨run,final,facts⟩:=Budget.actual_polynomial () input contract budget
  have mass:=(facts.boundaries final (List.mem_of_getLast? facts.last)).2.2.1
  rw [facts.contents] at mass
  exact mass

theorem time_le (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    time input contract budget≤macroCoefficient*((preparationInput input contract budget).length+1)^12 := by
  let length:=(preparationInput input contract budget).length
  let size:=length+1
  let background:=Budget.outputBank (preparationInput input contract budget) I.stageCount I.toolCount budget
  have base : 1≤size := by dsimp [size];omega
  have cubic : size≤size^3 := by simpa only [pow_one] using Nat.pow_le_pow_right base (by decide : 1≤3)
  have degree : size^3≤size^12 := Nat.pow_le_pow_right base (by decide : 3≤12)
  have mass : RatInput.occupied background≤Budget.coefficient*size^3 := output_mass_le input contract budget
  have scale : StageChannels.scale background length≤(Budget.coefficient+1)*size^3 := by
    have simple : RatInput.occupied background+size≤(Budget.coefficient+1)*size^3 := by
      nlinarith only [mass,cubic]
    simpa only [StageChannels.scale,StageFront.scale,size,Nat.add_assoc] using simple
  have powered : (StageChannels.scale background length)^4≤(Budget.coefficient+1)^4*size^12 := by
    calc
      _≤((Budget.coefficient+1)*size^3)^4 := Nat.pow_le_pow_left scale 4
      _=_ := by ring
  calc
    time input contract budget≤Budget.coefficient*size^12+StageChannels.coefficient*((Budget.coefficient+1)^4*size^12) :=
      Nat.add_le_add (Nat.mul_le_mul_left Budget.coefficient degree) (Nat.mul_le_mul_left StageChannels.coefficient powered)
    _=macroCoefficient*size^12 := by unfold macroCoefficient;ring

theorem resource_envelope (length : Nat) :
    macroCoefficient*(length+1)^12≤coefficient*(length+1)^12 ∧
    16*space length≤coefficient*(length+1)^12 ∧
    16*(space length+16)≤coefficient*(length+1)^12 ∧
    32*(space length+17)≤coefficient*(length+1)^12 := by
  have base : 1≤length+1 := by omega
  have positive : 1≤(length+1)^12 := Nat.pow_le_pow_left base 12
  have linear : length+1≤(length+1)^12 := by
    simpa only [pow_one] using Nat.pow_le_pow_right base (by decide : 1≤12)
  have product : 0≤macroCoefficient*(length+1)^12 := Nat.zero_le _
  dsimp only [space,coefficient]
  constructor
  · nlinarith only [product,positive]
  constructor
  · nlinarith only [product,linear]
  constructor <;> nlinarith only [product,linear,positive]

end RootB234.PrepEntry.WholeChannels
