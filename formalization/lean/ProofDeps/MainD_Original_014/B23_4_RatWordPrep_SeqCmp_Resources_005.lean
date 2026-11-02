module

public import B23_4_RatWordPrep_SeqCmp_Two_004

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.SeqCmp

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM

variable {C : Type*}

theorem program_actions (point : Label) : ScannerClock.actions (program (C := C) .halt point) ≤ 32 := by
  cases point with
  | pair second point =>
    rw [program,LabelMap.statement_actions,StoreIso.statement_actions]
    exact RatPair.Link.program_actions point
  | cmp second point =>
    rw [program,LabelMap.statement_actions]
    exact (RatCmp.Link.program_actions point).trans (by decide)
  | discard second point =>
    rw [program,LabelMap.statement_actions]
    exact (RatDrop.program_actions point).trans (by decide)
  | capture second => exact of_decide_eq_true rfl
  | emit => exact of_decide_eq_true rfl
  | done => exact Nat.zero_le _

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C := C) .halt point) ≤ 32 := by
  cases point with
  | pair second point =>
    rw [program,LabelMap.statement_pushes,StoreIso.statement_pushes]
    exact RatPair.Link.program_pushes point
  | cmp second point =>
    rw [program,LabelMap.statement_pushes]
    exact (RatCmp.Link.program_pushes point).trans (by decide)
  | discard second point =>
    rw [program,LabelMap.statement_pushes]
    exact (RatDrop.program_pushes point).trans (by decide)
  | capture second => exact Nat.zero_le _
  | emit => exact of_decide_eq_true rfl
  | done => exact Nat.zero_le _

private theorem writes_store {σ τ Λ : Type*} (iso : σ ≃ τ) (allowed : RatInput.Stack → Prop)
    (body : TM2.Stmt RatInput.Alphabet Λ σ) :
    StackIso.WritesOnly allowed (StoreIso.statement iso body) ↔ StackIso.WritesOnly allowed body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih => exact and_congr Iff.rfl ih
  | peek _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ a b => exact and_congr a b
  | goto _ | halt => rfl

private theorem writes_mono {σ Λ : Type*} (body : TM2.Stmt RatInput.Alphabet Λ σ)
    (old new : RatInput.Stack → Prop) (included : ∀ slot, old slot → new slot)
    (good : StackIso.WritesOnly old body) : StackIso.WritesOnly new body := by
  induction body with
  | push slot _ _ ih | pop slot _ _ ih => exact ⟨included slot good.1, ih good.2⟩
  | peek _ _ _ ih | load _ _ ih => exact ih good
  | branch _ _ _ a b => exact ⟨a good.1,b good.2⟩
  | goto _ | halt => trivial

theorem program_writes (point : Label) : StackIso.WritesOnly RatPair.Link.Work (program (C := C) .halt point) := by
  cases point with
  | pair second point =>
    rw [program,StackIso.writes_labelMap,writes_store]
    exact RatPair.Link.program_writes point
  | cmp second point =>
    rw [program,StackIso.writes_labelMap]
    apply writes_mono _ RatCmp.Link.Work _ _ (RatCmp.Link.program_writes point)
    intro slot owned
    fin_cases slot <;> simp_all [RatCmp.Link.Work,RatPair.Link.Work,RatInput.Encoder.Work]
  | discard second point =>
    rw [program,StackIso.writes_labelMap]
    apply writes_mono _ (fun slot => slot=15 ∨ slot=3) _ _ (RatDrop.program_writes point)
    intro slot owned
    rcases owned with rfl | rfl <;> simp [RatPair.Link.Work,RatInput.Encoder.Work]
  | capture second => exact ⟨by decide,trivial⟩
  | emit => exact ⟨by decide,by decide,trivial⟩
  | done => trivial

theorem step_resources (before after : State C) (bound : Nat)
    (edge : TM2.step (program .halt) before = some after)
    (bounded : ∀ slot, (before.stk slot).length ≤ bound) :
    (∀ slot, (after.stk slot).length ≤ bound+32) ∧
      ∀ slot, ¬RatPair.Link.Work slot → after.stk slot=before.stk slot := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have eq : after=TM2.stepAux (program .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      refine ⟨fun slot => (AuxWorkspace.endpoint_bound _ _ _ bound bounded slot).trans
        (Nat.add_le_add_left (program_pushes point) bound), ?_⟩
      intro slot untouched
      exact StackIso.nodes_frame _ _ (program_writes point) memory contents slot untouched
        _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_resources (trace : List (State C)) (before : State C)
    (background : RatInput.Stack → List Bool) (bound : Nat)
    (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (program .halt) a=some b))
    (bounded : ∀ slot,(before.stk slot).length≤bound)
    (frame : ∀ slot,¬RatPair.Link.Work slot→before.stk slot=background slot) :
    ∀ current∈trace, (∀ slot,(current.stk slot).length≤bound+32*trace.length) ∧
      ∀ slot,¬RatPair.Link.Work slot→current.stk slot=background slot := by
  induction trace generalizing before bound with
  | nil => simp
  | cons firstState rest ih =>
    have eq : firstState=before := Option.some.inj first
    subst firstState
    cases rest with
    | nil =>
      intro current member
      have eq := List.mem_singleton.mp member
      subst current
      exact ⟨fun slot => (bounded slot).trans (by simp),frame⟩
    | cons next rest =>
      obtain ⟨edge,tailChain⟩ := List.isChain_cons_cons.mp chain
      have step := step_resources before next bound edge bounded
      intro current member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨fun slot => (bounded slot).trans (Nat.le_add_right _ _),frame⟩
      · have tail := ih next (bound+32) rfl tailChain step.1
          (fun slot untouched => (step.2 slot untouched).trans (frame slot untouched)) current later
        refine ⟨?_,tail.2⟩
        intro slot
        have h := tail.1 slot
        simp only [List.length_cons] at h ⊢
        omega

theorem internal_resources (current : State C) (point : Label) (bound : Nat)
    (bounded : ∀ slot,(current.stk slot).length≤bound) :
    (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
      (∀ slot,(node.2 slot).length≤bound+32) ∧
        ∀ slot,¬RatPair.Link.Work slot→node.2 slot=current.stk slot) ∧
      ScannerStatement.clock (program .halt point) current.var current.stk≤64*(bound+33) := by
  refine ⟨?_,?_⟩
  · intro node member
    exact ⟨fun slot => (AuxWorkspace.node_bound _ _ _ bound bounded node member slot).trans
      (Nat.add_le_add_left (program_pushes point) bound),
      fun slot untouched => StackIso.nodes_frame _ _ (program_writes point) current.var current.stk slot untouched node member⟩
  · exact (ScannerClock.clock_bound (program .halt point) current.var current.stk bound bounded).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions point))
        (Nat.add_le_add_right (Nat.add_le_add_left (program_pushes point) bound) 1))

def twoSpace (background : RatInput.Stack → List Bool) (a b c d : Rat) (tail scratch : List Bool) : Nat :=
  RatInput.occupied (entry false background (C := Unit) default a b (RatPair.input c d tail) scratch).stk +
    32*twoTime background a b c d tail scratch

theorem actual_two_bounded (background : RatInput.Stack → List Bool)
    (memory : Store C) (a b c d : Rat) (tail scratch : List Bool) :
    ∃ trace : List (State C), ∃ final : State C,
      trace.head? = some (entry false background memory a b (RatPair.input c d tail) scratch) ∧
      trace.IsChain (fun before after => TM2.step (program .halt) before = some after) ∧
      trace.getLast? = some final ∧ final.l=some .done ∧
      registers final.var=((registers memory).1,decide (a≤b),decide (c≤d)) ∧
      final.stk=Function.update (RatPair.Link.initial background tail scratch) 3 [decide (a≤b),decide (c≤d)] ∧
      trace.length≤twoTime background a b c d tail scratch ∧
      (∀ current∈trace, (∀ slot,(current.stk slot).length≤twoSpace background a b c d tail scratch) ∧
        RatInput.occupied current.stk≤16*twoSpace background a b c d tail scratch ∧
        ∀ slot,¬RatPair.Link.Work slot→current.stk slot=background slot) ∧
      (∀ current∈trace.dropLast,current.l≠some .done ∧
        ∀ point,current.l=some point→
          (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
            (∀ slot,(node.2 slot).length≤twoSpace background a b c d tail scratch+32) ∧
              ∀ slot,¬RatPair.Link.Work slot→node.2 slot=background slot) ∧
          ScannerStatement.clock (program .halt point) current.var current.stk≤
            64*(twoSpace background a b c d tail scratch+33)) := by
  obtain ⟨trace,final,first,chain,last,active,regs,contents,time⟩ := actual_two .halt background memory a b c d tail scratch
  let before := entry false background memory a b (RatPair.input c d tail) scratch
  have frames : ∀ slot,¬RatPair.Link.Work slot→before.stk slot=background slot :=
    RatPair.Link.initial_frame background _ scratch
  have bounds := trace_resources trace before background (RatInput.occupied before.stk) first chain
    (RatInput.Encoder.point_mass before.stk) frames
  have bounded : ∀ current∈trace,∀ slot,(current.stk slot).length≤twoSpace background a b c d tail scratch := by
    intro current member slot
    exact ((bounds current member).1 slot).trans (by
      dsimp only [twoSpace,entry,before]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left 32 time) _)
  have proper := NativeMulLink.no_early_halt_port (program .halt) .done rfl trace final chain last active
  refine ⟨trace,final,first,chain,last,active,regs,contents,time,?_,?_⟩
  · intro current member
    exact ⟨bounded current member,RatInput.Encoder.occupied_bound current.stk _ (bounded current member),(bounds current member).2⟩
  · intro current member
    refine ⟨proper current member,?_⟩
    intro point selected
    have internal := internal_resources current point _ (bounded current (List.mem_of_mem_dropLast member))
    refine ⟨?_,internal.2⟩
    intro node present
    exact ⟨(internal.1 node present).1,
      fun slot untouched => ((internal.1 node present).2 slot untouched).trans
        ((bounds current (List.mem_of_mem_dropLast member)).2 slot untouched)⟩

end B23_4_RatWordPrep.SeqCmp
