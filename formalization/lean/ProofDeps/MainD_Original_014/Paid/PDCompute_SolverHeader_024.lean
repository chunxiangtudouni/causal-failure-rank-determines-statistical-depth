module

public import Paid.PDCompute_EndpointPairCode_023

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)

/-- Logical contents of the constant-size, actually live solver header.
The cell map includes the original natural arguments and rational data. -/
def Header (state : State) (base : ℕ) (values : ℕ → Cell) : Prop :=
  ∀ slot < headerWords, base+slot ∈ state.live ∧ state.heap (base+slot)=values slot

theorem Header.ratBinarySlots {before : State} {base : ℕ} {values : ℕ → Cell}
    (header : Header before base values) (input : List Cell)
    (left right target : ℕ) (operation : RatOp) (x y value : ℚ)
    (hleft : left < headerWords) (hright : right < headerWords)
    (hx : values left=.rational x) (hy : values right=.rational y)
    (hbase : before.register .fresh=.natural base) (hoperation : operation.eval x y=some value) :
    linearExecute input (ratBinarySlots operation left right target) before=
      some (ratBinarySlotsResult before base left right target value) ∧
    Header (ratBinarySlotsResult before base left right target value) base
      (Function.update values target (.rational value)) := by
  constructor
  · exact ratBinarySlots_execute input before base left right target operation x y value hbase
      (header left hleft).1 (header right hright).1
      ((header left hleft).2.trans hx) ((header right hright).2.trans hy) hoperation
  · intro slot inside
    constructor
    · exact ratBinarySlotsResult_live_mono before base left right target value (header slot inside).1
    · rw [ratBinarySlotsResult_heap]
      by_cases hs : slot=target
      · subst slot
        simp only [Function.update_self]
      · rw [Function.update_of_ne (fun he => hs (Nat.add_left_cancel he)),Function.update_of_ne hs]
        exact (header slot inside).2

theorem Header.frame {before after : State} {base : ℕ} {values : ℕ → Cell}
    (header : Header before base values)
    (hheap : ∀ slot < headerWords, after.heap (base+slot)=before.heap (base+slot))
    (hlive : before.live ⊆ after.live) : Header after base values := by
  intro slot inside
  exact ⟨hlive (header slot inside).1,(hheap slot inside).trans (header slot inside).2⟩

theorem Header.update {before after : State} {base : ℕ} {values : ℕ → Cell}
    (header : Header before base values) (target : ℕ) (value : Cell)
    (hheap : after.heap=Function.update before.heap (base+target) value)
    (hlive : before.live ⊆ after.live) : Header after base (Function.update values target value) := by
  intro slot inside
  refine ⟨hlive (header slot inside).1,?_⟩
  rw [hheap]
  by_cases hs : slot=target
  · subst slot
    simp only [Function.update_self]
  · rw [Function.update_of_ne (fun he => hs (Nat.add_left_cancel he)),Function.update_of_ne hs]
    exact (header slot inside).2

theorem Header.value {state : State} {base : ℕ} {values : ℕ → Cell}
    (header : Header state base values) (slot : ℕ) (inside : slot < headerWords) :
    state.heap (base+slot)=values slot := (header slot inside).2

theorem Header.live {state : State} {base : ℕ} {values : ℕ → Cell}
    (header : Header state base values) (slot : ℕ) (inside : slot < headerWords) :
    base+slot ∈ state.live := (header slot inside).1

end PDCompute.Solver
