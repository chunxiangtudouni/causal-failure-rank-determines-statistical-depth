module

public import RootB234_PrepEntry_ScalarPacketRun_100
public import Mathlib.Algebra.Order.BigOperators.Group.List

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.ScalarPacket
open Turing PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM B23_4_RatWordPrep
variable {C : Type*}

theorem step_context (before after : State C) (edge : TM2.step (program .halt) before=some after) :
    Prod.fst after.var=Prod.fst before.var := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (program .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      exact RawGetter.nodes_readonly Prod.fst _ (program_readonly point) memory contents _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_context (trace : List (State C)) (before : State C) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (program .halt) a=some b)) :
    ∀ current∈trace,Prod.fst current.var=Prod.fst before.var := by
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
    (∀ slot,(after.stk slot).length≤bound+1) ∧
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
    ∀ current∈trace,(∀ slot,(current.stk slot).length≤bound+1*trace.length) ∧
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
      · have tail := ih next (bound+1) rfl tailChain step.1
          (fun slot untouched => (step.2 slot untouched).trans (frame slot untouched)) current later
        refine ⟨?_,tail.2⟩
        intro slot
        have h := tail.1 slot
        simp only [List.length_cons] at h ⊢
        omega

theorem internal_resources (current : State C) (point : Label) (bound : Nat)
    (bounded : ∀ slot,(current.stk slot).length≤bound) :
    (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
      Prod.fst node.1=Prod.fst current.var ∧ (∀ slot,(node.2 slot).length≤bound+1) ∧
        ∀ slot,¬Work slot→node.2 slot=current.stk slot) ∧
      ScannerStatement.clock (program .halt point) current.var current.stk≤6*(bound+2) := by
  refine ⟨?_,?_⟩
  · intro node member
    exact ⟨RawGetter.nodes_readonly Prod.fst _ (program_readonly point) current.var current.stk node member,
      fun slot => (AuxWorkspace.node_bound _ _ _ bound bounded node member slot).trans
        (Nat.add_le_add_left (program_pushes point) bound),
      fun slot untouched => StackIso.nodes_frame _ _ (program_writes point) current.var current.stk slot untouched node member⟩
  · exact (ScannerClock.clock_bound (program .halt point) current.var current.stk bound bounded).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions point))
        (Nat.add_le_add_right (Nat.add_le_add_left (program_pushes point) bound) 1))


def coefficient : Nat := 128
def inputMass (before : State C) : Nat := RatInput.occupied before.stk
def inputScale (before : State C) : Nat := inputMass before+1

theorem resource_envelope (M : Nat) :
    2*(M+1)≤coefficient*(M+1) ∧
    16*(M+2*(M+1))≤coefficient*(M+1) ∧
    16*(M+2*(M+1)+1)≤coefficient*(M+1) ∧
    6*(M+2*(M+1)+2)≤coefficient*(M+1) := by
  dsimp only [coefficient]
  omega

structure Bounds (before : State C) (trace : List (State C)) : Prop where
  time : trace.length≤coefficient*inputScale before
  boundaries : ∀ current∈trace,current.var.1=before.var.1 ∧
    (∀ slot,(current.stk slot).length≤coefficient*inputScale before) ∧
    RatInput.occupied current.stk≤coefficient*inputScale before ∧
    ∀ slot,¬Work slot→current.stk slot=before.stk slot
  proper : ∀ current∈trace.dropLast,current.l≠some .done
  internal : ∀ current∈trace,∀ point,current.l=some point→
    (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
      node.1.1=before.var.1 ∧ (∀ slot,(node.2 slot).length≤coefficient*inputScale before) ∧
      RatInput.occupied node.2≤coefficient*inputScale before ∧
      ∀ slot,¬Work slot→node.2 slot=before.stk slot) ∧
    ScannerStatement.clock (program .halt point) current.var current.stk≤coefficient*inputScale before

theorem certify {before final : State C} {bound : Nat} (part : Path .halt before final bound)
    (active : final.l=some .done) (time : part.trace.length≤2*inputScale before) : Bounds before part.trace := by
  let M:=inputMass before
  have initial : ∀ slot,(before.stk slot).length≤M:=RatInput.Encoder.point_mass before.stk
  have frames : ∀ slot,¬Work slot→before.stk slot=before.stk slot := by intros;rfl
  have resources:=trace_resources part.trace before before.stk M part.first part.chain initial frames
  have contexts:=trace_context part.trace before part.first part.chain
  have bounded : ∀ current∈part.trace,∀ slot,(current.stk slot).length≤M+2*(M+1) := by
    intro current member slot
    have raw:=(resources current member).1 slot
    simp only [Nat.one_mul] at raw
    exact raw.trans (Nat.add_le_add_left time M)
  have caps:=resource_envelope M
  have proper:=NativeMulLink.no_early_halt_port (program (C:=C) .halt) .done rfl part.trace final part.chain part.last active
  refine ⟨time.trans caps.1,?_,proper,?_⟩
  · intro current member
    refine ⟨contexts current member,?_,?_,(resources current member).2⟩
    · intro slot
      exact (bounded current member slot).trans ((Nat.le_mul_of_pos_left _ (by decide : 0<16)).trans caps.2.1)
    · exact (RatInput.Encoder.occupied_bound _ _ (bounded current member)).trans caps.2.1
  · intro current member point selected
    have internal:=internal_resources current point _ (bounded current member)
    refine ⟨?_,internal.2.trans caps.2.2.2⟩
    intro node inside
    obtain ⟨context,nodeLengths,nodeFrames⟩:=internal.1 node inside
    refine ⟨context.trans (contexts current member),?_,?_,?_⟩
    · intro slot
      exact (nodeLengths slot).trans ((Nat.le_mul_of_pos_left _ (by decide : 0<16)).trans caps.2.2.1)
    · exact (RatInput.Encoder.occupied_bound _ _ nodeLengths).trans caps.2.2.1
    · intro slot untouched
      exact (nodeFrames slot untouched).trans ((resources current member).2 slot untouched)

noncomputable def statementClock (current : State C) : Nat :=
  current.l.elim 0 (fun point => ScannerStatement.clock (program .halt point) current.var current.stk)
noncomputable def clockSum (trace : List (State C)) : Nat := (trace.dropLast.map statementClock).sum

theorem clockSum_le {before : State C} {trace : List (State C)} (facts : Bounds before trace) :
    clockSum trace≤coefficient^2*(inputScale before)^2 := by
  let cap:=coefficient*inputScale before
  have each : ∀ value∈trace.dropLast.map statementClock,value≤cap := by
    intro value member
    obtain ⟨current,inside,rfl⟩:=List.mem_map.mp member
    cases active : current.l with
    | none => simp only [statementClock,active,Option.elim_none,Nat.zero_le]
    | some point =>
      simp only [statementClock,active,Option.elim_some]
      exact (facts.internal current (List.mem_of_mem_dropLast inside) point active).2
  have sum : clockSum trace≤trace.dropLast.length*cap := by
    simpa only [clockSum,List.length_map,Nat.nsmul_eq_mul] using List.sum_le_length_nsmul (trace.dropLast.map statementClock) cap each
  have count : trace.dropLast.length≤cap := by rw [List.length_dropLast];exact (Nat.sub_le _ _).trans facts.time
  exact (sum.trans (Nat.mul_le_mul_right cap count)).trans_eq (by dsimp only [cap];ring)

theorem charged_le {before : State C} {trace : List (State C)} (facts : Bounds before trace) :
    trace.length+clockSum trace≤(coefficient^2+coefficient)*(inputScale before)^2 := by
  have positive : 1 ≤ inputScale before := by unfold inputScale;omega
  have power : inputScale before ≤ (inputScale before)^2 := by simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1 ≤ 2)
  have count:=facts.time.trans (Nat.mul_le_mul_left coefficient power)
  exact (Nat.add_le_add count (clockSum_le facts)).trans_eq (by ring)

end RootB234.PrepEntry.ScalarPacket
