module

public import B23_4_RatWordPrep_SeqCmp_LookupPaths_092

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.Lookup

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

theorem builder_shared (rename : RootB234.RuntimeCounter.Builder.Label → Label)
    (roles : RatInput.Stack ≃ RatInput.Stack) (before : State C) (number : Nat) (tail : List Bool)
    (active : before.l=some (rename 0))
    (source : before.stk (roles 8)=NatField.packet number tail) (scratch : before.stk (roles 4)=[]) :
    builderCfg rename (RootB234.RuntimeCounter.Builder.atState roles before.stk 0
      ((WordFields.packetIso C).symm before.var).1 ((WordFields.packetIso C).symm before.var).2
      (NatField.packet number tail) [] (before.stk (roles 10)) (before.stk (roles 11)))=before := by
  have bank : RootB234.RuntimeCounter.Builder.atBank roles before.stk (NatField.packet number tail)
      [] (before.stk (roles 10)) (before.stk (roles 11))=before.stk := by
    funext slot
    unfold RootB234.RuntimeCounter.Builder.atBank
    split_ifs with h8 h4 h10 h11
    · subst slot; exact source.symm
    · subst slot; exact scratch.symm
    · subst slot; rfl
    · subst slot; rfl
    · rfl
  cases before with
  | mk point memory slots =>
    change point=some (rename 0) at active
    subst point
    change (⟨some (rename 0),WordFields.packetIso C ((WordFields.packetIso C).symm memory),
      RootB234.RuntimeCounter.Builder.atBank roles slots _ _ _ _⟩ : State C)=_
    rw [Equiv.apply_symm_apply]
    exact congrArg (fun cells => (⟨some (rename 0),memory,cells⟩ : State C)) bank

theorem actual_builder (truth : Bool) (caller : Statement C)
    (rename : RootB234.RuntimeCounter.Builder.Label → Label) (roles : RatInput.Stack ≃ RatInput.Stack)
    (before : State C) (number : Nat) (tail : List Bool)
    (active : before.l=some (rename 0))
    (source : before.stk (roles 8)=NatField.packet number tail) (scratch : before.stk (roles 4)=[])
    (same : ∀ point,point≠5→program truth caller (rename point)=
      LabelMap.statement rename (StoreIso.statement (WordFields.packetIso C)
        (RootB234.RuntimeCounter.Builder.atProgram roles false point))) :
    ∃ (final : State C) (run : Segment truth caller before final),
      final.l=some (rename 5) ∧ final.var.2.2=before.var.2.2 ∧
      final.stk=RootB234.RuntimeCounter.Builder.atBank roles before.stk (NatField.packet number tail) []
        (RootB234.RuntimeCounter.Round.Raw.packet (PSTRTMNatValue017.rawPayload number)) [false] ∧
      run.trace.length≤(before.stk (roles 10)).length+(before.stk (roles 11)).length+
        2*(PSTRTMNatValue017.rawPayload number).length+14 := by
  let registers := (WordFields.packetIso C).symm before.var
  obtain ⟨trace,facts⟩ := RootB234.RuntimeCounter.Builder.at_actual roles false
    before.stk registers.1 registers.2 number tail (before.stk (roles 10)) (before.stk (roles 11))
  let final := RootB234.RuntimeCounter.Builder.Public.finalState roles false before.stk registers.1 number tail
  have path := single_port_path (WordFields.packetIso C) rename _ truth caller 5 rfl
    trace _ final facts.first facts.chain facts.last rfl same
  let run : Segment truth caller before (builderCfg rename final) :=
    ⟨trace.map (builderCfg rename),path.1.trans
      (congrArg some (builder_shared rename roles before number tail active source scratch)),path.2.1,path.2.2⟩
  refine ⟨builderCfg rename final,run,rfl,?_,rfl,?_⟩
  · change registers.1.2.2=before.var.2.2
    rfl
  · simpa only [run,List.length_map] using facts.count

theorem round_shared (rename : RootB234.RuntimeCounter.Round.Label → Label) (before : State C)
    (digits : List Bool) (active : before.l=some (rename 0))
    (right : before.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits)
    (left : before.stk 11=[false]) (scratch : before.stk 4=[]) :
    roundCfg rename (RootB234.RuntimeCounter.Round.entry before.stk ((WordFields.roundIso C).symm before.var) digits)=before := by
  cases before with
  | mk point memory slots =>
    change point=some (rename 0) at active
    subst point
    change (⟨some (rename 0),WordFields.roundIso C ((WordFields.roundIso C).symm memory),
      RootB234.RuntimeCounter.Round.cells slots _ _ _⟩ : State C)=⟨some (rename 0),memory,slots⟩
    rw [Equiv.apply_symm_apply]
    congr 1
    funext slot
    fin_cases slot <;> simp_all [RootB234.RuntimeCounter.Round.cells]

theorem actual_round (truth : Bool) (caller : Statement C)
    (rename : RootB234.RuntimeCounter.Round.Label → Label) (before : State C) (digits : List Bool)
    (active : before.l=some (rename 0))
    (right : before.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits)
    (left : before.stk 11=[false]) (scratch : before.stk 4=[])
    (same : ∀ point,point≠7→point≠8→program truth caller (rename point)=
      LabelMap.statement rename (StoreIso.statement (WordFields.roundIso C)
        (RootB234.RuntimeCounter.Round.program point))) :
    ∃ (final : State C) (run : Segment truth caller before final),
      final.l=some (rename (if PSTRTMIncrement009.valueDigits digits=0 then 7 else 8)) ∧
      final.var.2.2=before.var.2.2 ∧
      final.stk=RootB234.RuntimeCounter.Round.cells before.stk
        (RootB234.RuntimeCounter.Round.Raw.packet (RootB234.RuntimeCounter.Round.Raw.outputDigits digits)) [false] [] ∧
      run.trace.length≤256*RootB234.RuntimeCounter.Round.scale before.stk digits := by
  obtain ⟨trace,final,facts⟩ := RootB234.RuntimeCounter.Round.actual_polynomial
    before.stk ((WordFields.roundIso C).symm before.var) digits
  have path := transport_path (WordFields.roundIso C) rename _ truth caller (fun point => point≠7 ∧ point≠8)
    trace _ final facts.first facts.chain facts.last
    (by
      intro current member point selected
      exact ⟨fun equal => (facts.proper current member).1 (equal ▸ selected),
        fun equal => (facts.proper current member).2 (equal ▸ selected)⟩)
    (by intro point different; exact same point different.1 different.2)
  let run : Segment truth caller before (roundCfg rename final) :=
    ⟨trace.map (roundCfg rename),path.1.trans (congrArg some (round_shared rename before digits active right left scratch)),
      path.2.1,path.2.2⟩
  refine ⟨roundCfg rename final,run,?_,?_,facts.contents,?_⟩
  · change final.l.map rename=some _
    rw [facts.port]
    rfl
  · exact congrArg (fun v : RoundContext C => v.2.2) facts.context
  · simpa only [run,List.length_map] using facts.time

end B23_4_RatWordPrep.Lookup
