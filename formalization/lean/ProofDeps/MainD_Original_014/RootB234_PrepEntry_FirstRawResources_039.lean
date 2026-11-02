module

public import RootB234_PrepEntry_FirstRawRun_038

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.FirstRaw

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

theorem lastNatural_width_le (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    (PSTRTMNatValue017.rawPayload (lastNatural input contract)).length≤(preparationInput input contract budget).length := by
  have shape:=List.dropLast_concat_getLast (firstNumbers_nonempty input contract)
  have part : (PSTRTMNatValue017.rawPayload (lastNatural input contract)).length≤
      NatPrefix.payloadMass (firstNumbers input contract) := by
    conv_rhs => rw [←shape]
    simp only [NatPrefix.payloadMass,List.map_append,List.map_cons,List.map_nil,List.sum_append,
      List.sum_cons,List.sum_nil]
    unfold lastNatural
    omega
  exact part.trans ((NatPrefix.payloadMass_le _).trans (firstNumbers_length_le input contract budget))

theorem firstRat_width_le (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    (PA17TMRatArithmeticParse002.numeratorDigits (firstValue input budget)).length+
      (PA17TMRatArithmeticParse002.denominatorDigits (firstValue input budget)).length≤
        (preparationInput input contract budget).length := by
  have field:=firstRat_length_le input contract budget
  rw [PA17TMRatArithmeticParse002.datum_length] at field
  omega

theorem time_le (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    time input contract budget≤128*((preparationInput input contract budget).length+1)^2 := by
  let L:=(preparationInput input contract budget).length
  have tools : (PSTRTMNatValue017.rawPayload I.toolCount).length≤L := by
    change (PSTRTMNatValue017.rawPayload I.toolCount).length≤(preparationInput input contract budget).length
    rw [PSTRTMWordPreparationFront214.preparation_input,NJ.preparationTail_tools]
    simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn,List.length_append,List.length_cons,
      PSTRTMLength004.encodeNat_length]
    omega
  have lastWidth:=lastNatural_width_le input contract budget
  have ratWidths:=firstRat_width_le input contract budget
  have naturalTime : NatPrefix.workTime (firstNumbers input contract)≤32*(L+1)^2 :=
    (NatPrefix.workTime_wire_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (Nat.add_le_add_right (firstNumbers_length_le input contract budget) 1) 2))
  have base : 1≤L+1 := by omega
  have linear : L+1≤(L+1)^2 := by nlinarith only [base]
  have square : 1≤(L+1)^2 := Nat.pow_le_pow_left base 2
  have toolsSquare:=Nat.pow_le_pow_left tools 2
  have ratSquare : (PA17TMRatArithmeticParse002.numeratorDigits (firstValue input budget)).length^2+
      (PA17TMRatArithmeticParse002.denominatorDigits (firstValue input budget)).length^2≤L^2 := by
    have sum:=Nat.pow_le_pow_left ratWidths 2
    change _≤L^2 at sum
    nlinarith only [sum,Nat.zero_le ((PA17TMRatArithmeticParse002.numeratorDigits (firstValue input budget)).length*
      (PA17TMRatArithmeticParse002.denominatorDigits (firstValue input budget)).length)]
  change time input contract budget≤128*(L+1)^2
  dsimp only [time,prefixTime,RawGetter.time]
  change _≤L at lastWidth
  change _≤L at ratWidths
  nlinarith only [tools,toolsSquare,lastWidth,ratWidths,ratSquare,naturalTime,linear,square]

end RootB234.PrepEntry.FirstRaw
