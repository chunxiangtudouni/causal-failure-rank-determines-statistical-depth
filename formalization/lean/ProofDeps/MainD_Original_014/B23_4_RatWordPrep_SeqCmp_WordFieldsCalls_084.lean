module

public import B23_4_RatWordPrep_SeqCmp_WordFieldsPaths_083

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFields

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

theorem round_shared (before : State C) (digits : List Bool)
    (active : before.l=some (.round 0))
    (right : before.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits)
    (left : before.stk 11=[false]) (scratch : before.stk 4=[]) :
    roundCfg (RootB234.RuntimeCounter.Round.entry before.stk ((roundIso C).symm before.var) digits)=before := by
  cases before with
  | mk point memory slots =>
    change point=some (.round 0) at active
    subst point
    change (⟨some (.round 0),roundIso C ((roundIso C).symm memory),
      RootB234.RuntimeCounter.Round.cells slots _ _ _⟩ : State C)=⟨some (.round 0),memory,slots⟩
    rw [Equiv.apply_symm_apply]
    congr 1
    funext slot
    fin_cases slot <;> simp_all [RootB234.RuntimeCounter.Round.cells]

theorem actual_round (caller : Statement C) (before : State C) (digits : List Bool)
    (active : before.l=some (.round 0))
    (right : before.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits)
    (left : before.stk 11=[false]) (scratch : before.stk 4=[]) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (if PSTRTMIncrement009.valueDigits digits=0 then .done else .symbol .boot) ∧
      final.var.2.2=before.var.2.2 ∧
      final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet (RootB234.RuntimeCounter.Round.Raw.outputDigits digits) ∧
      final.stk 11=[false] ∧ final.stk 4=[] ∧
      (∀ slot,slot≠4→slot≠10→slot≠11→final.stk slot=before.stk slot) ∧
      run.trace.length≤256*RootB234.RuntimeCounter.Round.scale before.stk digits := by
  obtain ⟨trace,final,facts⟩ := RootB234.RuntimeCounter.Round.actual_polynomial
    before.stk ((roundIso C).symm before.var) digits
  have path := transport_path (roundIso C) roundLabel _ caller (fun point => point≠7 ∧ point≠8)
    trace _ final facts.first facts.chain facts.last
    (by
      intro current member point selected
      exact ⟨fun equal => (facts.proper current member).1 (equal ▸ selected),
        fun equal => (facts.proper current member).2 (equal ▸ selected)⟩)
    (by intro point different; simp only [roundLabel,different.1,different.2,ite_false,program])
  let run : Segment caller before (roundCfg final) :=
    ⟨trace.map roundCfg,path.1.trans (congrArg some (round_shared before digits active right left scratch)),
      path.2.1,path.2.2⟩
  obtain ⟨outRight,outLeft,outScratch⟩ := RootB234.RuntimeCounter.Round.exact_output facts
  refine ⟨roundCfg final,run,?_,?_,outRight,outLeft,outScratch,?_,?_⟩
  · change final.l.map roundLabel=some _
    rw [facts.port]
    by_cases zero : PSTRTMIncrement009.valueDigits digits=0 <;> simp [roundLabel,zero]
  · exact congrArg (fun v : RoundContext C => v.2.2) facts.context
  · intro slot n4 n10 n11
    exact RootB234.RuntimeCounter.Round.exact_frame facts slot (by
      simp only [RootB234.RuntimeCounter.Round.Work,n4,n10,n11,or_self,not_false_eq_true])
  · simpa only [run,List.length_map] using facts.time

theorem target_shared (before : State C) (active : before.l=some (.target .boot)) :
    targetCfg (⟨some .boot,(rawIso C).symm before.var,before.stk⟩ : RawGetter.State (RawContext C))=before := by
  cases before with
  | mk point memory slots =>
    change point=some (.target .boot) at active
    subst point
    change (⟨some (.target .boot),rawIso C ((rawIso C).symm memory),slots⟩ : State C)=_
    rw [Equiv.apply_symm_apply]

theorem actual_target (caller : Statement C) (before : State C) (x : Rat) (suffix : List Bool)
    (active : before.l=some (.target .boot))
    (right : ListBlank.mk (before.stk 0)=ListBlank.mk (encodeDatum (.rational x)++suffix++[true])) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.targetMove 0) ∧ final.var.2.2=before.var.2.2 ∧
      final.stk 15=RatInput.Encoder.packet x (before.stk 15) ∧
      ListBlank.mk (final.stk 0)=ListBlank.mk (suffix++[true]) ∧
      (∀ slot,slot≠0→slot≠1→slot≠15→final.stk slot=before.stk slot) ∧
      run.trace.length≤RawGetter.time x := by
  obtain ⟨trace,final,parsed,first,chain,last,_member,activeFinal,context,contents,tape,
      scratch,_target,time,boundaries,_proper⟩ :=
    RawGetter.actual_current_bounded before.stk ((rawIso C).symm before.var) x suffix right
  have path := single_port_path (rawIso C) targetLabel (RawGetter.program .halt) caller .done rfl
    trace _ final first chain last activeFinal
    (by intro point different; simp only [targetLabel,different,ite_false,program])
  let run : Segment caller before (targetCfg final) :=
    ⟨trace.map targetCfg,path.1.trans (congrArg some (target_shared before active)),path.2.1,path.2.2⟩
  have finalFrame := (boundaries final (List.mem_of_getLast? last)).2.2.2
  refine ⟨targetCfg final,run,?_,?_,?_,?_,?_,?_⟩
  · change final.l.map targetLabel=some (.targetMove 0)
    rw [activeFinal]
    rfl
  · exact congrArg (fun v : RawContext C => v.2.2) context
  · change final.stk 15=_
    rw [contents,Function.update_self]
  · have rightTape := congrArg Tape.right₀ tape
    simp only [Tape.mk₂,Tape.mk'_right₀] at rightTape
    change ListBlank.mk (final.stk 0)=_
    rw [contents,Function.update_of_ne (by decide : (0 : RatInput.Stack)≠15)]
    exact rightTape
  · intro slot n0 n1 n15
    change final.stk slot=_
    by_cases s7 : slot=7
    · subst slot
      rw [contents,Function.update_of_ne (by decide : (7 : RatInput.Stack)≠15)]
      exact scratch
    · exact finalFrame slot (by simp only [RawGetter.Work,n0,n1,n15,s7,or_self,not_false_eq_true])
  · simpa only [run,List.length_map] using time

def naturalLabel (symbolMode : Bool) (point : RawNat.Label) : Label :=
  if symbolMode then symbolLabel point else countLabel point

def naturalCfg (symbolMode : Bool) (before : RawNat.State (Channels.Store C)) : State C :=
  LabelMap.configuration (naturalLabel symbolMode) (StoreIso.configuration (naturalIso C) before)

theorem natural_shared (symbolMode : Bool) (before : State C)
    (active : before.l=some (if symbolMode then .symbol .boot else .count .boot)) :
    naturalCfg symbolMode (⟨some .boot,(naturalIso C).symm before.var,before.stk⟩ : RawNat.State (Channels.Store C))=before := by
  cases before with
  | mk point memory slots =>
    change point=some (if symbolMode then .symbol .boot else .count .boot) at active
    subst point
    change (⟨some (naturalLabel symbolMode .boot),naturalIso C ((naturalIso C).symm memory),slots⟩ : State C)=_
    rw [Equiv.apply_symm_apply]
    cases symbolMode <;> rfl

theorem actual_natural (symbolMode : Bool) (caller : Statement C) (before : State C)
    (number : Nat) (suffix : List Bool)
    (active : before.l=some (if symbolMode then .symbol .boot else .count .boot))
    (right : ListBlank.mk (before.stk 0)=ListBlank.mk (encodeDatum (.natural number)++suffix++[true])) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (if symbolMode then .symbolMove 2 else .countMove 2) ∧
      final.var.2=before.var.2 ∧ final.stk 15=NatField.packet number (before.stk 15) ∧
      ListBlank.mk (final.stk 0)=ListBlank.mk (suffix++[true]) ∧
      (∀ slot,slot≠0→slot≠1→slot≠15→final.stk slot=before.stk slot) ∧
      run.trace.length≤RawNat.time number := by
  obtain ⟨trace,final,parsed,first,chain,last,_member,activeFinal,context,contents,tape,
      scratch,_target,time,boundaries,_proper⟩ :=
    RawNat.actual_current_bounded before.stk ((naturalIso C).symm before.var) number suffix right
  have path := single_port_path (naturalIso C) (naturalLabel symbolMode) (RawNat.program .halt)
    caller .done rfl trace _ final first chain last activeFinal (by
      intro point different
      cases symbolMode <;> simp [naturalLabel,countLabel,symbolLabel,different,program] <;> rfl)
  let run : Segment caller before (naturalCfg symbolMode final) :=
    ⟨trace.map (naturalCfg symbolMode),
      path.1.trans (congrArg some (natural_shared symbolMode before active)),path.2.1,path.2.2⟩
  have finalFrame := (boundaries final (List.mem_of_getLast? last)).2.2.2
  refine ⟨naturalCfg symbolMode final,run,?_,context,?_,?_,?_,?_⟩
  · change final.l.map (naturalLabel symbolMode)=some _
    rw [activeFinal]
    cases symbolMode <;> rfl
  · change final.stk 15=_
    rw [contents,Function.update_self]
  · have rightTape := congrArg Tape.right₀ tape
    simp only [Tape.mk₂,Tape.mk'_right₀] at rightTape
    change ListBlank.mk (final.stk 0)=_
    rw [contents,Function.update_of_ne (by decide : (0 : RatInput.Stack)≠15)]
    exact rightTape
  · intro slot n0 n1 n15
    change final.stk slot=_
    by_cases s7 : slot=7
    · subst slot
      rw [contents,Function.update_of_ne (by decide : (7 : RatInput.Stack)≠15)]
      exact scratch
    · exact finalFrame slot (by simp only [RawNat.Work,n0,n1,n15,s7,or_self,not_false_eq_true])
  · simpa only [run,List.length_map] using time

end B23_4_RatWordPrep.WordFields

