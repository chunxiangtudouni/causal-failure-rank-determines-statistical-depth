module

public import RootB234_PrepEntry_MainExponentResources_096

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.MainExponent
open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM B23_4_RatWordPrep RootB234.PrepExponent RootL01.SymbolicSource
variable {C : Type*} {I : Instance}

def Endpoint (context : C) (input : StatisticalInput I) (contract : Contract I) (budget : Rat) (final : State C) : Prop :=
  final.l=some .done ∧ callerContext final.var=context ∧
  final.stk 5=NatField.packet (computedExponent (I:=I) budget) [] ∧
  final.stk 8=NatField.packet I.stageCount [] ∧ final.stk 9=NatField.packet I.toolCount [] ∧
  final.stk 15=RatInput.Encoder.packet budget [] ∧
  final.stk 14=NatField.packet (FirstRaw.lastNatural input contract) [] ∧
  final.stk 13=RatInput.Encoder.packet (FirstRaw.firstValue input budget) [] ∧
  final.stk 12=StageFront.feeOutput input [] ∧
  final.stk 2=StageChannels.archive input false [] ∧ final.stk 6=StageChannels.archive input true [] ∧
  ListBlank.mk (final.stk 0)=ListBlank.mk (StageChannels.afterChannels input contract budget++[true]) ∧
  final.stk 7=[] ∧ final.stk 4=[] ∧ final.stk 3=[]

structure Facts (coefficient degree : Nat) (context : C) (input : StatisticalInput I) (contract : Contract I)
    (budget : Rat) (trace : List (State C)) (final : State C) : Prop where
  first : trace.head?=some (entry context (preparationInput input contract budget))
  chain : trace.IsChain (fun a b => TM2.step (program .halt) a=some b)
  last : trace.getLast?=some final
  endpoint : Endpoint context input contract budget final
  bounds : PolynomialBounds coefficient degree (arithmeticScale input contract budget) trace
  contexts : ∀ current∈trace,callerContext current.var=context
  proper : ∀ current∈trace.dropLast,current.l≠some .done
  internal_context : ∀ current∈trace,∀ point,current.l=some point→
    ∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,callerContext node.1=context

/-- Source and uniform constants are fixed before every original input.
No packet, width, exponent, path, fuel, empty scratch or prepared store
is passed by the original caller. -/
theorem actual_polynomial :
    ∃ coefficient degree : Nat,0<coefficient ∧ 0<degree ∧
      ∀ (context : C) (I : Instance) (input : StatisticalInput I) (contract : Contract I) (budget : Rat),
        0<budget→∃ trace final,Facts coefficient degree context input contract budget trace final := by
  obtain ⟨coefficient,degree,cPositive,dPositive,bounded⟩:=time_polynomial
  refine ⟨coefficient,degree,cPositive,dPositive,?_⟩
  intro context I input contract budget positive
  obtain ⟨trace,final,first,chain,last,active,contextEq,exponent,n,j,b,a,prior,fee,p0,p1,cursor,scratch,empty4,empty3,count⟩:=
    actual .halt context input contract budget positive
  let part : Segment (.halt : Statement C) (entry context (preparationInput input contract budget)) final :=
    ⟨trace,first,chain,last⟩
  have capped : trace.length≤coefficient*(arithmeticScale input contract budget)^degree :=
    count.trans (bounded I input contract budget)
  have originalPositive : 1≤arithmeticScale input contract budget := by unfold arithmeticScale;omega
  have resources:=resources_of_cap _ _ part coefficient degree (arithmeticScale input contract budget)
    originalPositive dPositive (original_entry_cap context input contract budget) capped
  have frames:=trace_context trace _ first chain
  have contexts : ∀ current∈trace,callerContext current.var=context := by
    intro current member
    exact (frames current member).trans (entry_context context _)
  have proper:=NativeMulLink.no_early_halt_port (program (C:=C) .halt) .done rfl trace final chain last active
  refine ⟨trace,final,⟨first,chain,last,?_,resources,contexts,proper,?_⟩⟩
  · exact ⟨active,contextEq,exponent,n,j,b,a,prior,fee,p0,p1,cursor,scratch,empty4,empty3⟩
  · intro current member point selected node inside
    exact (RawGetter.nodes_readonly callerContext _ (program_readonly point) current.var current.stk node inside).trans
      (contexts current member)

theorem program_eq_before_done (caller : Statement C) (point : Label) (different : point≠.done) :
    program caller point=program .halt point := by
  cases point with
  | budget _ | exponent _ | natural _ | clear _ | channels _ => rfl
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

noncomputable def statementClock (code : Label → Statement C) (current : State C) : Nat :=
  current.l.elim 0 (fun point => ScannerStatement.clock (code point) current.var current.stk)
noncomputable def callerClockSum (caller : Statement C) (trace : List (State C)) : Nat :=
  (trace.dropLast.map (statementClock (program caller))).sum

structure CallerFacts (caller : Statement C) (coefficient degree : Nat) (context : C)
    (input : StatisticalInput I) (contract : Contract I) (budget : Rat) (trace : List (State C)) (final : State C) : Prop where
  base : Facts coefficient degree context input contract budget trace final
  chain : trace.IsChain (fun a b => TM2.step (program caller) a=some b)
  internal_same : ∀ current∈trace.dropLast,∀ point,current.l=some point→
    AuxWorkspace.nodes (program caller point) current.var current.stk=AuxWorkspace.nodes (program .halt point) current.var current.stk ∧
    ScannerStatement.clock (program caller point) current.var current.stk=ScannerStatement.clock (program .halt point) current.var current.stk
  scan : callerClockSum caller trace≤scanCoefficient C coefficient*(arithmeticScale input contract budget)^(2*degree)
  charge : trace.length+callerClockSum caller trace≤chargeCoefficient C coefficient*(arithmeticScale input contract budget)^(2*degree)

theorem retarget (caller : Statement C) {coefficient degree : Nat} {context : C} {input : StatisticalInput I}
    {contract : Contract I} {budget : Rat} {trace : List (State C)} {final : State C}
    (facts : Facts coefficient degree context input contract budget trace final) :
    CallerFacts caller coefficient degree context input contract budget trace final := by
  have same : ∀ current∈trace.dropLast,∀ point,current.l=some point→program caller point=program .halt point := by
    intro current member point selected
    apply program_eq_before_done caller point
    intro equal
    subst point
    exact facts.proper current member selected
  have clocks : callerClockSum caller trace=clockSum trace := by
    unfold callerClockSum clockSum
    apply congrArg List.sum
    apply List.map_congr_left
    intro current member
    cases active : current.l with
    | none => simp only [statementClock,stateClock,active,Option.elim_none]
    | some point =>
      simp only [statementClock,stateClock,active,Option.elim_some]
      rw [same current member point active]
  refine ⟨facts,chain_same _ _ _ facts.chain same,?_,?_,?_⟩
  · intro current member point selected
    rw [same current member point selected]
    exact ⟨rfl,rfl⟩
  · rw [clocks]
    exact facts.bounds.scan
  · rw [clocks]
    exact facts.bounds.charge

namespace Public

theorem fixed_source (C : Type*) [Fintype C] :
    ∃ (source : Label → Statement C) (support : Finset Label) (coefficient degree : Nat),
      source=program .halt ∧ TM2.Supports source support ∧ source .done=.halt ∧
      0<coefficient ∧ 0<degree ∧
      ∀ (context : C) (I : Instance) (input : StatisticalInput I) (contract : Contract I) (budget : Rat),
        0<budget→∃ trace final,Facts coefficient degree context input contract budget trace final := by
  obtain ⟨coefficient,degree,cPositive,dPositive,all⟩:=actual_polynomial (C:=C)
  exact ⟨program .halt,Finset.univ,coefficient,degree,rfl,supports .halt,rfl,cPositive,dPositive,all⟩

theorem static_caller (caller : Statement C) :
    ∃ coefficient degree : Nat,0<coefficient ∧ 0<degree ∧
      ∀ (context : C) (I : Instance) (input : StatisticalInput I) (contract : Contract I) (budget : Rat),
        0<budget→∃ trace final,CallerFacts caller coefficient degree context input contract budget trace final := by
  obtain ⟨coefficient,degree,cPositive,dPositive,all⟩:=actual_polynomial (C:=C)
  refine ⟨coefficient,degree,cPositive,dPositive,?_⟩
  intro context I input contract budget positive
  obtain ⟨trace,final,facts⟩:=all context I input contract budget positive
  exact ⟨trace,final,retarget caller facts⟩

theorem from_default :
    ∃ coefficient degree : Nat,0<coefficient ∧ 0<degree ∧
      ∀ (I : Instance) (input : StatisticalInput I) (contract : Contract I) (budget : Rat),0<budget→
        ∃ trace final,Facts (C:=Unit) coefficient degree () input contract budget trace final ∧
          trace.head?=some (TM2.init (Γ:=RatInput.Alphabet) (Λ:=Label) (σ:=Store Unit) 0 (preparationInput input contract budget)) := by
  obtain ⟨coefficient,degree,cPositive,dPositive,all⟩:=actual_polynomial (C:=Unit)
  refine ⟨coefficient,degree,cPositive,dPositive,?_⟩
  intro I input contract budget positive
  obtain ⟨trace,final,facts⟩:=all () I input contract budget positive
  exact ⟨trace,final,facts,facts.first.trans (congrArg some (initial_default _))⟩

end Public
end RootB234.PrepEntry.MainExponent
