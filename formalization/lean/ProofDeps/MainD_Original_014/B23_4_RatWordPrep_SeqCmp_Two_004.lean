module

public import B23_4_RatWordPrep_SeqCmp_Round_003

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.SeqCmp

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

variable {C : Type*}

def twoTime (background : RatInput.Stack → List Bool) (a b c d : Rat) (tail scratch : List Bool) : Nat :=
  roundTime background a b (RatPair.input c d tail) scratch + roundTime background c d tail scratch + 2

/-- Four actual rational packets; no comparison answer, trace, length,
fuel or operand premise. Both comparator calls and both operand disposals
belong to this one fixed source and one joined trace. -/
theorem actual_two (caller : Statement C) (background : RatInput.Stack → List Bool)
    (memory : Store C) (a b c d : Rat) (tail scratch : List Bool) :
    ∃ trace : List (State C), ∃ final : State C,
      trace.head? = some (entry false background memory a b (RatPair.input c d tail) scratch) ∧
      trace.IsChain (fun before after => TM2.step (program caller) before = some after) ∧
      trace.getLast? = some final ∧ final.l = some .done ∧
      registers final.var = ((registers memory).1, decide (a ≤ b), decide (c ≤ d)) ∧
      final.stk = Function.update (RatPair.Link.initial background tail scratch) 3
        [decide (a ≤ b), decide (c ≤ d)] ∧
      trace.length ≤ twoTime background a b c d tail scratch := by
  obtain ⟨middle,front,frontActive,frontRegs,frontContents⟩ :=
    actual_round caller false background memory a b (RatPair.input c d tail) scratch
  have shared : entry true background middle.var c d tail scratch = middle := by
    cases middle with
    | mk position memory contents =>
      change position = some (.pair true (.collect 0)) at frontActive
      change contents = RatPair.Link.initial background (RatPair.input c d tail) scratch at frontContents
      subst position; subst contents; rfl
  obtain ⟨last,back,backActive,backRegs,backContents⟩ :=
    actual_round caller true background middle.var c d tail scratch
  let back' : Segment caller middle last (roundTime background c d tail scratch) :=
    ⟨back.trace,back.head.trans (congrArg some shared),back.chain,back.last,back.count⟩
  have bits : registers last.var = ((registers memory).1,decide (a ≤ b),decide (c ≤ d)) := by
    rw [backRegs,frontRegs]
    rfl
  let final : State C := ⟨some .done,last.var,Function.update last.stk 3 [decide (a ≤ b),decide (c ≤ d)]⟩
  have edge : TM2.step (program caller) last = some final := by
    cases last with
    | mk position memory contents =>
      change position = some .emit at backActive
      subst position
      change some (TM2.stepAux (program caller .emit) memory contents) = _
      dsimp only [program,TM2.stepAux]
      rw [bits,Function.update_self,Function.update_idem]
      have empty : contents 3 = [] := by rw [show contents = _ from backContents]; rfl
      rw [empty]
  let emit : Segment caller last final 2 :=
    ⟨[last,final],rfl,List.isChain_cons_cons.mpr ⟨edge,List.isChain_singleton _⟩,rfl,Nat.le_refl _⟩
  let whole := (front.append back').append emit
  refine ⟨whole.trace,final,whole.head,whole.chain,whole.last,rfl,bits,?_,whole.count⟩
  change Function.update last.stk 3 _ = _
  rw [backContents]

theorem uniform_two (caller : Statement C) :
    ∃ source : Label → Statement C, source .done = caller ∧
      ∀ (background : RatInput.Stack → List Bool) (memory : Store C)
        (a b c d : Rat) (tail scratch : List Bool),
        ∃ trace : List (State C), ∃ final : State C,
          trace.head? = some (entry false background memory a b (RatPair.input c d tail) scratch) ∧
          trace.IsChain (fun before after => TM2.step source before = some after) ∧
          trace.getLast? = some final ∧ final.l = some .done ∧
          registers final.var = ((registers memory).1, decide (a ≤ b), decide (c ≤ d)) ∧
          final.stk = Function.update (RatPair.Link.initial background tail scratch) 3
            [decide (a ≤ b), decide (c ≤ d)] ∧
          trace.length ≤ twoTime background a b c d tail scratch := by
  exact ⟨program caller,rfl,actual_two caller⟩

end B23_4_RatWordPrep.SeqCmp
