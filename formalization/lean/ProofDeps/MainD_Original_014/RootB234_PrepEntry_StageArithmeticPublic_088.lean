module

public import RootB234_PrepEntry_StageArithmeticResources_087
public import Mathlib.Algebra.Order.BigOperators.Group.List

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.StageArithmetic
open Turing PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM RootB234.PrepExponent RootL01.SymbolicSource
variable {C : Type*}

structure Facts (code : Label → Statement C) (multiply : Bool) (memory : Store C) (before : Bank)
    (x y : Rat) (tail : List Bool) (trace : List (State C)) (afterMemory : Store C) : Prop where
  first : trace.head?=some (state default memory before)
  chain : trace.IsChain (fun a b => TM2.step code a=some b)
  last : trace.getLast?=some (state .done afterMemory (output before (RatInput.Encoder.packet (result multiply x y) tail)))
  context_eq : QLoop.rootContext afterMemory=QLoop.rootContext memory
  time : trace.length≤coefficient*(StageStash.scale before)^4
  boundaries : ∀ current∈trace,QLoop.rootContext current.var=QLoop.rootContext memory ∧
    (∀ slot,(current.stk slot).length≤coefficient*(StageStash.scale before)^4) ∧
    RatInput.occupied current.stk≤coefficient*(StageStash.scale before)^4 ∧
    ∀ slot,¬Work slot→current.stk slot=before slot
  proper : ∀ current∈trace.dropLast,current.l≠some .done ∧
    ∀ point,current.l=some point→
      (∀ node∈AuxWorkspace.nodes (code point) current.var current.stk,
        QLoop.rootContext node.1=QLoop.rootContext memory ∧
        (∀ slot,(node.2 slot).length≤coefficient*(StageStash.scale before)^4) ∧
        RatInput.occupied node.2≤coefficient*(StageStash.scale before)^4 ∧
        ∀ slot,¬Work slot→node.2 slot=before slot) ∧
      ScannerStatement.clock (code point) current.var current.stk≤coefficient*(StageStash.scale before)^4

theorem actual_polynomial (multiply : Bool) (memory : Store C) (before : Bank) (x y : Rat) (tail : List Bool)
    (source : before 15=RatPair.input x y tail) (temporary : before 4=[]) :
    ∃ trace afterMemory,Facts (program multiply .halt) multiply memory before x y tail trace afterMemory := by
  obtain ⟨afterMemory,part,context,count⟩:=actual multiply (.halt : Statement C) memory before x y tail source temporary
  let M:=StageStash.mass before
  have initial : ∀ slot,(before slot).length≤M:=StageStash.point_mass before
  have timeCap : part.trace.length≤timeCoefficient*(M+1)^4:=
    count.trans (actualCost_bound multiply before memory x y tail source)
  have lengths:=trace_resources part.trace (state default memory before) before M part.first part.chain initial (by intros;rfl)
  have contexts:=trace_context part.trace (state default memory before) part.first part.chain
  have bounded : ∀ current∈part.trace,∀ slot,(current.stk slot).length≤M+32*(timeCoefficient*(M+1)^4) := by
    intro current member slot
    exact ((lengths current member).1 slot).trans (Nat.add_le_add_left (Nat.mul_le_mul_left 32 timeCap) M)
  have caps:=resource_envelope M
  have proper:=NativeMulLink.no_early_halt_port (program multiply (C:=C) .halt) .done rfl
    part.trace _ part.chain part.last rfl
  refine ⟨part.trace,afterMemory,⟨part.first,part.chain,part.last,context,timeCap.trans caps.1,?_,?_⟩⟩
  · intro current member
    refine ⟨contexts current member,?_,?_,(lengths current member).2⟩
    · intro slot
      exact (bounded current member slot).trans ((Nat.le_mul_of_pos_left _ (by decide : 0<16)).trans caps.2.1)
    · exact (RatInput.Encoder.occupied_bound current.stk _ (bounded current member)).trans caps.2.1
  · intro current member
    refine ⟨proper current member,?_⟩
    intro point selected
    have internal:=internal_resources (multiply:=multiply) current point _ (bounded current (List.mem_of_mem_dropLast member))
    refine ⟨?_,internal.2.trans caps.2.2.2⟩
    intro node inside
    obtain ⟨held,nodeLengths,frames⟩:=internal.1 node inside
    refine ⟨held.trans (contexts current (List.mem_of_mem_dropLast member)),?_,?_,?_⟩
    · intro slot
      exact (nodeLengths slot).trans ((Nat.le_mul_of_pos_left _ (by decide : 0<16)).trans caps.2.2.1)
    · exact (RatInput.Encoder.occupied_bound node.2 _ nodeLengths).trans caps.2.2.1
    · intro slot safe
      exact (frames slot safe).trans ((lengths current (List.mem_of_mem_dropLast member)).2 slot safe)

theorem program_eq_before_done (multiply : Bool) (caller : Statement C) (point : Label) (different : point≠.done) :
    program multiply caller point=program multiply .halt point := by
  cases point with
  | stash _ | binary _ | restore _ => rfl
  | done => exact False.elim (different rfl)

private theorem chain_same (old target : Label → Statement C) (trace : List (State C))
    (chain : trace.IsChain (fun a b => TM2.step old a=some b))
    (same : ∀ before∈trace.dropLast,∀ point,before.l=some point→target point=old point) :
    trace.IsChain (fun a b => TM2.step target a=some b) := by
  induction trace with
  | nil => exact List.isChain_nil
  | cons first rest ih =>
    cases rest with
    | nil => exact List.isChain_singleton _
    | cons next rest =>
      obtain ⟨edge,tailChain⟩:=List.isChain_cons_cons.mp chain
      apply List.isChain_cons_cons.mpr
      refine ⟨?_,ih tailChain ?_⟩
      · cases first with
        | mk position memory slots =>
          cases position with
          | none => cases edge
          | some point =>
            have equality:=same ⟨some point,memory,slots⟩
              (by rw [List.dropLast_cons_cons]; exact List.mem_cons_self) point rfl
            change some (TM2.stepAux (target point) memory slots)=some next
            rw [equality]
            exact edge
      · intro current present point active
        apply same current _ point active
        rw [List.dropLast_cons_cons]
        exact List.mem_cons_of_mem _ present

theorem retarget (multiply : Bool) (caller : Statement C) {memory afterMemory : Store C} {before : Bank}
    {x y : Rat} {tail : List Bool} {trace : List (State C)}
    (facts : Facts (program multiply .halt) multiply memory before x y tail trace afterMemory) :
    Facts (program multiply caller) multiply memory before x y tail trace afterMemory := by
  have same : ∀ current∈trace.dropLast,∀ point,current.l=some point→
      program multiply caller point=program multiply .halt point := by
    intro current member point selected
    apply program_eq_before_done multiply caller point
    intro equal
    subst point
    exact (facts.proper current member).1 selected
  refine ⟨facts.first,chain_same _ _ _ facts.chain same,facts.last,facts.context_eq,facts.time,facts.boundaries,?_⟩
  intro current member
  refine ⟨(facts.proper current member).1,?_⟩
  intro point selected
  rw [same current member point selected]
  exact (facts.proper current member).2 point selected

noncomputable def statementClock (code : Label → Statement C) (current : State C) : Nat :=
  match current.l with | none => 0 | some point => ScannerStatement.clock (code point) current.var current.stk
noncomputable def traceClockSum (code : Label → Statement C) (trace : List (State C)) : Nat :=
  (trace.dropLast.map (statementClock code)).sum
noncomputable def chargedCost (code : Label → Statement C) (trace : List (State C)) : Nat :=
  trace.length+traceClockSum code trace

variable {code : Label → Statement C} {multiply : Bool} {memory afterMemory : Store C} {before : Bank}
  {x y : Rat} {tail : List Bool} {trace : List (State C)}

theorem traceClockSum_le (facts : Facts code multiply memory before x y tail trace afterMemory) :
    traceClockSum code trace≤coefficient^2*(StageStash.scale before)^8 := by
  let cap:=coefficient*(StageStash.scale before)^4
  have termwise : ∀ value∈trace.dropLast.map (statementClock code),value≤cap := by
    intro value member
    obtain ⟨current,present,rfl⟩:=List.mem_map.mp member
    cases selected : current.l with
    | none => simp only [statementClock,selected,Nat.zero_le]
    | some point =>
      simp only [statementClock,selected]
      exact ((facts.proper current present).2 point selected).2
  have sum : traceClockSum code trace≤trace.dropLast.length*cap := by
    simpa only [traceClockSum,List.length_map,Nat.nsmul_eq_mul] using
      List.sum_le_length_nsmul (trace.dropLast.map (statementClock code)) cap termwise
  have length : trace.dropLast.length≤cap := by
    rw [List.length_dropLast]
    exact (Nat.sub_le trace.length 1).trans facts.time
  calc
    traceClockSum code trace≤cap*cap := sum.trans (Nat.mul_le_mul_right cap length)
    _=_ := by dsimp only [cap];ring

theorem chargedCost_le (facts : Facts code multiply memory before x y tail trace afterMemory) :
    chargedCost code trace≤(coefficient^2+coefficient)*(StageStash.scale before)^8 := by
  have power : (StageStash.scale before)^4≤(StageStash.scale before)^8 :=
    Nat.pow_le_pow_right (scale_positive before) (by decide : 4≤8)
  have count:=facts.time.trans (Nat.mul_le_mul_left coefficient power)
  calc
    chargedCost code trace≤coefficient*(StageStash.scale before)^8+coefficient^2*(StageStash.scale before)^8 :=
      Nat.add_le_add count (traceClockSum_le facts)
    _=_ := by ring

namespace Public

theorem fixed_source (C : Type*) [Finite C] (multiply : Bool) :
    ∃ (code : Label → Statement C) (support : Finset Label),TM2.Supports code support ∧ code .done=.halt ∧
      ∀ (memory : Store C) (before : Bank) (x y : Rat) (tail : List Bool),
        before 15=RatPair.input x y tail → before 4=[] →
        ∃ trace afterMemory,Facts code multiply memory before x y tail trace afterMemory := by
  refine ⟨program multiply .halt,Finset.univ,supports multiply .halt,rfl,?_⟩
  intro memory before x y tail source temporary
  exact actual_polynomial multiply memory before x y tail source temporary

theorem static_caller (multiply : Bool) (caller : Statement C) (memory : Store C) (before : Bank)
    (x y : Rat) (tail : List Bool) (source : before 15=RatPair.input x y tail) (temporary : before 4=[]) :
    ∃ trace afterMemory,Facts (program multiply caller) multiply memory before x y tail trace afterMemory ∧
      chargedCost (program multiply caller) trace≤(coefficient^2+coefficient)*(StageStash.scale before)^8 := by
  obtain ⟨trace,afterMemory,old⟩:=actual_polynomial multiply memory before x y tail source temporary
  have facts:=retarget multiply caller old
  exact ⟨trace,afterMemory,facts,chargedCost_le facts⟩

theorem final_stacks (before : Bank) (value : Rat) (tail : List Bool) :
    output before (RatInput.Encoder.packet value tail) 15=RatInput.Encoder.packet value tail ∧
    ∀ slot,slot≠15→ output before (RatInput.Encoder.packet value tail) slot=before slot := by
  exact ⟨Function.update_self _ _ _,fun slot different => Function.update_of_ne different _ _⟩

end Public
end RootB234.PrepEntry.StageArithmetic
