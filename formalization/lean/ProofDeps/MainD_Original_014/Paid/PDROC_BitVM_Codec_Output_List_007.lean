module

public import Paid.PDROC_BitVM_Codec_Output_List_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Codec.OutputList

open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

def countInitState (word output ticks : List Bool) (store : CountStore) : CountState :=
  ⟨some 2, store, emitSlots word output [] ticks⟩

def countInitialized (output ticks : List Bool) (old : BoolOnStacks.Store 51) : CountState :=
  ⟨some 0, (old, none), emitSlots (encodeNat 0) output [] ticks⟩

theorem count_init_cons (bit : Bool) (word output ticks : List Bool) (store : CountStore) :
    TM2.step countProgram (countInitState (bit :: word) output ticks store) =
      some (countInitState word output ticks (store.1, some bit)) := by
  change (some ⟨some 2, (store.1, some bit),
    Function.update (emitSlots (bit :: word) output [] ticks) 0 word⟩ : Option CountState) = _
  have same : Function.update (emitSlots (bit :: word) output [] ticks) 0 word =
      emitSlots word output [] ticks := by
    funext role
    fin_cases role <;> simp [emitSlots]
  rw [same]
  rfl

theorem count_init_nil (output ticks : List Bool) (store : CountStore) :
    TM2.step countProgram (countInitState [] output ticks store) =
      some (countInitialized output ticks store.1) := by
  change (some ⟨some 0, (store.1, none),
    Function.update (Function.update (Function.update (Function.update
      (emitSlots [] output [] ticks) 0 []) 0 [false]) 0 [false, false])
      0 [true, false, false]⟩ : Option CountState) = _
  have same : Function.update (Function.update (Function.update (Function.update
      (emitSlots [] output [] ticks) 0 []) 0 [false]) 0 [false, false])
      0 [true, false, false] = emitSlots (encodeNat 0) output [] ticks := by
    funext role
    fin_cases role <;> simp [emitSlots, encodeNat, natBits]
  rw [same]
  rfl

def countInitTrace : List Bool → List Bool → List Bool → CountStore → List CountState
  | [], output, ticks, store =>
      [countInitState [] output ticks store, countInitialized output ticks store.1]
  | bit :: word, output, ticks, store =>
      countInitState (bit :: word) output ticks store ::
        countInitTrace word output ticks (store.1, some bit)

theorem countInit_head (word output ticks : List Bool) (store : CountStore) :
    (countInitTrace word output ticks store).head? =
      some (countInitState word output ticks store) := by
  cases word <;> rfl

theorem countInit_last (word output ticks : List Bool) (store : CountStore) :
    (countInitTrace word output ticks store).getLast? =
      some (countInitialized output ticks store.1) := by
  induction word generalizing store with
  | nil => rfl
  | cons bit word ih =>
    rw [countInitTrace, List.getLast?_cons, ih]
    rfl

theorem countInit_length (word output ticks : List Bool) (store : CountStore) :
    (countInitTrace word output ticks store).length = word.length + 2 := by
  induction word generalizing store with
  | nil => rfl
  | cons bit word ih => simp only [countInitTrace, List.length_cons, ih]

theorem countInit_chain (word output ticks : List Bool) (store : CountStore) :
    (countInitTrace word output ticks store).IsChain
      (fun a b => TM2.step countProgram a = some b) := by
  induction word generalizing store with
  | nil =>
    exact List.isChain_cons_cons.mpr ⟨count_init_nil output ticks store, List.isChain_singleton _⟩
  | cons bit word ih =>
    apply List.IsChain.cons (ih (store.1, some bit))
    intro after member
    rw [countInit_head] at member
    have same : after = countInitState word output ticks (store.1, some bit) :=
      (Option.mem_some_iff.mp member).symm
    subst after
    exact count_init_cons bit word output ticks store

theorem countInitialized_tape (output ticks : List Bool) (old : BoolOnStacks.Store 51) :
    countTape (countInitialized output ticks old) = Tape.mk₁ (encodeNat 0) := rfl

/-- The finalizer first REALLY discards the last loaded Cell, REALLY
pushes the zero count, then consumes the actual unary emissions. No count
or prepared binary tape is an input. Previous reverse output is retained.
The only empty role is the scratch returned by each genuine emit. -/
theorem count_complete (word output ticks : List Bool) (store : CountStore) :
    ∃ (run : List CountState) (after : CountState),
      run.head? = some (countInitState word output ticks store) ∧
      run.IsChain (fun a b => TM2.step countProgram a = some b) ∧
      run.getLast? = some after ∧ TM2.step countProgram after = none ∧
      after.l = none ∧ countTape after = Tape.mk₁ (encodeNat ticks.length) ∧
      after.stk 3 = [] ∧ after.stk 1 = output ∧
      run.length ≤ word.length + 2 + countCost 0 ticks.length := by
  obtain ⟨second, after, secondHead, secondChain, secondLast, halt, halted,
    finalTape, finalTicks, finalOutput, size⟩ :=
    count_loop ticks (countInitialized output ticks store.1) 0 rfl rfl
      (countInitialized_tape output ticks store.1)
  let first := countInitTrace word output ticks store
  have actual := PDROC.BitVM.Log.TwoStack.join_chain first second
    (countInitialized output ticks store.1) (countInit_chain word output ticks store)
      secondChain (countInit_last word output ticks store) secondHead
  have last : (first ++ second.tail).getLast? = some after := by
    have notOne : second.length ≠ 1 := by
      intro one
      have equal : countInitialized output ticks store.1 = after := by
        cases second with
        | nil => simp only [List.head?_nil, reduceCtorEq] at secondHead
        | cons head tail =>
          have same : head = countInitialized output ticks store.1 := Option.some.inj secondHead
          have empty : tail = [] := List.length_eq_zero_iff.mp (by simpa [List.length_cons] using one)
          subst head
          subst tail
          exact Option.some.inj secondLast
      have impossible := congrArg (fun state : CountState => state.l) equal
      rw [halted] at impossible
      cases impossible
    simp only [List.getLast?_append, List.getLast?_tail, notOne, ↓reduceIte,
      secondLast, Option.some_or]
  refine ⟨first ++ second.tail, after, ?_, actual, last, halt, halted,
    ?_, finalTicks, finalOutput, ?_⟩
  · simp only [List.head?_append, first, countInit_head, Option.some_or]
  · simpa only [Nat.zero_add] using finalTape
  · simp only [List.length_append, List.length_tail, first, countInit_length]
    omega

end PDROC.BitVM.Codec.OutputList
