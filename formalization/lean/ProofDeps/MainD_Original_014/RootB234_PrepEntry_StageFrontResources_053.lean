module

public import RootB234_PrepEntry_StageFrontSyntax_052

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.StageFront

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

variable {C : Type*}

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

variable {I : Instance}

theorem bodyTime_le (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    FirstRaw.bodyTime input contract budget≤128*((preparationInput input contract budget).length+1)^2 := by
  have sub : FirstRaw.bodyTime input contract budget≤FirstRaw.time input contract budget := by
    dsimp only [FirstRaw.bodyTime,FirstRaw.bodyPrefixTime,FirstRaw.time,FirstRaw.prefixTime]
    omega
  exact sub.trans (FirstRaw.time_le input contract budget)

theorem fee_datum_le (input : StatisticalInput I) (contract : Contract I) (budget : Rat)
    (positive : 0<I.stageCount) :
    (encodeDatum (.rational (input.experiment ⟨0,positive⟩).observationFee)).length≤
      (preparationInput input contract budget).length := by
  have sub : (NJ.afterTools input contract budget).length≤(preparationInput input contract budget).length := by
    change (((PSTRTMWordPreparationFront214.preparationData input contract budget).drop 2).flatMap encodeDatum++[true]).length≤
      (encode (PSTRTMWordPreparationFront214.preparationData input contract budget)).length
    have split:=List.take_append_drop 2 (PSTRTMWordPreparationFront214.preparationData input contract budget)
    have encoded:=congrArg (fun data : List Datum => data.flatMap encodeDatum) split
    have lengths:=congrArg List.length encoded
    simp only [List.flatMap_append,List.length_append] at lengths
    simp only [encode,List.length_append]
    omega
  rw [FirstRaw.afterTools_exact,FirstRaw.wireSuffix_positive input contract budget positive] at sub
  simp only [List.length_append] at sub
  omega

theorem fee_time_le (input : StatisticalInput I) (contract : Contract I) (budget : Rat)
    (positive : 0<I.stageCount) :
    RawGetter.time (input.experiment ⟨0,positive⟩).observationFee≤64*((preparationInput input contract budget).length+1)^2 := by
  let L:=(preparationInput input contract budget).length
  let x:=(input.experiment ⟨0,positive⟩).observationFee
  have widths : (PA17TMRatArithmeticParse002.numeratorDigits x).length+
      (PA17TMRatArithmeticParse002.denominatorDigits x).length≤L := by
    have field:=fee_datum_le input contract budget positive
    rw [PA17TMRatArithmeticParse002.datum_length] at field
    change 2*((PA17TMRatArithmeticParse002.numeratorDigits x).length+
      (PA17TMRatArithmeticParse002.denominatorDigits x).length)+4≤L at field
    omega
  have squared : (PA17TMRatArithmeticParse002.numeratorDigits x).length^2+
      (PA17TMRatArithmeticParse002.denominatorDigits x).length^2≤L^2 := by
    have sum:=Nat.pow_le_pow_left widths 2
    nlinarith only [sum,Nat.zero_le ((PA17TMRatArithmeticParse002.numeratorDigits x).length*
      (PA17TMRatArithmeticParse002.denominatorDigits x).length)]
  change RawGetter.time x≤64*(L+1)^2
  dsimp only [RawGetter.time]
  nlinarith only [widths,squared,Nat.zero_le (L^2)]

theorem time_le (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    time input contract budget≤256*((preparationInput input contract budget).length+1)^2 := by
  have body:=bodyTime_le input contract budget
  have base : 1≤((preparationInput input contract budget).length+1)^2 :=
    Nat.pow_le_pow_left (by omega : 1≤(preparationInput input contract budget).length+1) 2
  by_cases positive : 0<I.stageCount
  · have fee:=fee_time_le input contract budget positive
    simp only [time,prefixTime,dite_eq_left positive]
    nlinarith only [body,fee,base]
  · simp only [time,prefixTime,dite_eq_right positive]
    nlinarith only [body,base]

end RootB234.PrepEntry.StageFront
