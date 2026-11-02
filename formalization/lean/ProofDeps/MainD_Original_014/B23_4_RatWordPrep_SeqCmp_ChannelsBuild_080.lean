module

public import B23_4_RatWordPrep_SeqCmp_ChannelsCalls_078

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.Channels

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

theorem build_shared (before : State C) (number : Nat) (tail : List Bool)
    (active : before.l=some (.build 0)) (source : before.stk 8=NatField.packet number tail)
    (scratch : before.stk 4=[]) :
    buildCfg (RootB234.RuntimeCounter.Builder.atState RootB234.RuntimeCounter.Builder.Public.source8Roles
      before.stk 0 ((packetIso C).symm before.var).1 ((packetIso C).symm before.var).2
      (NatField.packet number tail) [] (before.stk 10) (before.stk 11))=before := by
  cases before with
  | mk point memory slots =>
    change point=some (.build 0) at active
    subst point
    change (⟨some (.build 0),packetIso C ((packetIso C).symm memory),
      RootB234.RuntimeCounter.Builder.bank slots _ _ _ _⟩ : State C)=⟨some (.build 0),memory,slots⟩
    rw [Equiv.apply_symm_apply]
    congr 1
    funext slot
    fin_cases slot <;> simp_all [RootB234.RuntimeCounter.Builder.bank]

theorem actual_build (caller : Statement C) (before : State C) (number : Nat) (tail : List Bool)
    (active : before.l=some (.build 0)) (source : before.stk 8=NatField.packet number tail)
    (scratch : before.stk 4=[]) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.round 0) ∧ final.var.2=before.var.2 ∧
      final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet (false::PSTRTMNatValue017.rawPayload number) ∧
      final.stk 11=[false] ∧ final.stk 4=[] ∧
      (∀ slot,slot≠4→slot≠10→slot≠11→final.stk slot=before.stk slot) ∧
      run.trace.length≤(before.stk 10).length+(before.stk 11).length+
        2*(PSTRTMNatValue017.rawPayload number).length+14 := by
  let registers := (packetIso C).symm before.var
  obtain ⟨trace,facts⟩ := RootB234.RuntimeCounter.Builder.Public.from8Twice_actual
    before.stk registers.1 registers.2 number tail (before.stk 10) (before.stk 11)
  let final := RootB234.RuntimeCounter.Builder.Public.finalState
    RootB234.RuntimeCounter.Builder.Public.source8Roles true before.stk registers.1 number tail
  have path := build_path caller trace _ final facts.first facts.chain facts.last rfl
  let run : Segment caller before (buildCfg final) :=
    ⟨trace.map buildCfg,path.1.trans (congrArg some (build_shared before number tail active source scratch)),
      path.2.1,path.2.2⟩
  refine ⟨buildCfg final,run,rfl,?_,rfl,rfl,rfl,?_,?_⟩
  · change registers.1.2=before.var.2
    rfl
  · intro slot n4 n10 n11
    change RootB234.RuntimeCounter.Builder.bank before.stk _ _ _ _ slot=before.stk slot
    by_cases s8 : slot=8
    · subst slot
      exact source.symm
    · simp only [RootB234.RuntimeCounter.Builder.bank,s8,n4,n10,n11,ite_false]
  · simpa only [run,List.length_map] using facts.count

end B23_4_RatWordPrep.Channels
