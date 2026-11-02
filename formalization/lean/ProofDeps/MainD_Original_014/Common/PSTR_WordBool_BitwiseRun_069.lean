module

public import Common.PSTR_WordBool_BitwiseKernel_068

/-! A single actual AND/OR operand trace, including output reversal and
physical width restoration. All widths, including0, use the same four labels.
The pair list is only a proof annotation of the two actual operand stacks. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.Bitwise

open Turing
open PSTRWordVM

def outputs (isOr : Bool) (pairs : List (Bool × Bool)) : List Bool :=
  pairs.map (fun pair => combine isOr pair.1 pair.2)

def forwardTrace (isOr : Bool) (background : Stack → List Bool) :
    Store → List (Bool × Bool) → List Bool → Nat → List State
  | memory, [], reversed, used =>
      [state background 0 memory [] [] reversed [] (List.replicate used true),
       state background 1 (false, false) [] [] reversed [] (List.replicate used true)]
  | memory, pair :: later, reversed, used =>
      state background 0 memory ((pair :: later).map Prod.fst) ((pair :: later).map Prod.snd)
        reversed (List.replicate (later.length + 1) true) (List.replicate used true) ::
      forwardTrace isOr background pair later (combine isOr pair.1 pair.2 :: reversed) (used + 1)

theorem forward_head (isOr : Bool) (background : Stack → List Bool) (memory : Store)
    (pairs : List (Bool × Bool)) (reversed : List Bool) (used : Nat) :
    (forwardTrace isOr background memory pairs reversed used).head? =
      some (state background 0 memory (pairs.map Prod.fst) (pairs.map Prod.snd) reversed
        (List.replicate pairs.length true) (List.replicate used true)) := by
  cases pairs <;> rfl

theorem forward_nonempty (isOr : Bool) (background : Stack → List Bool) (memory : Store)
    (pairs : List (Bool × Bool)) (reversed : List Bool) (used : Nat) :
    forwardTrace isOr background memory pairs reversed used ≠ [] := by
  intro empty
  have head := forward_head isOr background memory pairs reversed used
  rw [empty] at head
  cases head

theorem forward_chain (isOr : Bool) (caller : Statement) (background : Stack → List Bool)
    (memory : Store) (pairs : List (Bool × Bool)) (reversed : List Bool) (used : Nat) :
    (forwardTrace isOr background memory pairs reversed used).IsChain
      (fun before after => TM2.step (program isOr caller) before = some after) := by
  induction pairs generalizing memory reversed used with
  | nil => exact List.isChain_cons_cons.mpr ⟨step_forward_end isOr caller background memory reversed _, by simp⟩
  | cons pair later ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_, ih _ _ _⟩
    intro next present
    rw [forward_head] at present
    have same := (Option.mem_some_iff.mp present).symm
    subst next
    simpa only [List.map_cons, List.replicate_succ] using
      step_forward isOr caller background memory pair.1 pair.2 (later.map Prod.fst)
        (later.map Prod.snd) reversed (List.replicate later.length true) (List.replicate used true)

theorem forward_last (isOr : Bool) (background : Stack → List Bool) (memory : Store)
    (pairs : List (Bool × Bool)) (reversed : List Bool) (used : Nat) :
    (forwardTrace isOr background memory pairs reversed used).getLast? =
      some (state background 1 (false, false) [] [] ((outputs isOr pairs).reverse ++ reversed) []
        (List.replicate (used + pairs.length) true)) := by
  induction pairs generalizing memory reversed used with
  | nil => simp only [forwardTrace, outputs, List.map_nil, List.reverse_nil, List.nil_append,
      List.getLast?_cons_cons, List.getLast?_singleton, List.length_nil, Nat.add_zero]
  | cons pair later ih =>
    rw [forwardTrace, List.getLast?_cons_of_ne_nil (forward_nonempty _ _ _ _ _ _), ih]
    simp only [outputs, List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons]
    have same : used + 1 + later.length = used + (later.length + 1) := by omega
    rw [same]

theorem forward_length (isOr : Bool) (background : Stack → List Bool) (memory : Store)
    (pairs : List (Bool × Bool)) (reversed : List Bool) (used : Nat) :
    (forwardTrace isOr background memory pairs reversed used).length = pairs.length + 2 := by
  induction pairs generalizing memory reversed used with
  | nil => rfl
  | cons pair later ih => simp only [forwardTrace, List.length_cons, ih]

def reverseTrace (background : Stack → List Bool) : Store → List Bool → List Bool → Nat → List State
  | memory, [], result, used =>
      [state background 1 memory result [] [] [] (List.replicate used true),
       state background 2 (false, false) result [] [] [] (List.replicate used true)]
  | memory, bit :: later, result, used =>
      state background 1 memory result [] (bit :: later) [] (List.replicate used true) ::
        reverseTrace background (true, bit) later (bit :: result) used

theorem reverse_head (background : Stack → List Bool) (memory : Store) (reversed result : List Bool) (used : Nat) :
    (reverseTrace background memory reversed result used).head? =
      some (state background 1 memory result [] reversed [] (List.replicate used true)) := by
  cases reversed <;> rfl

theorem reverse_nonempty (background : Stack → List Bool) (memory : Store) (reversed result : List Bool) (used : Nat) :
    reverseTrace background memory reversed result used ≠ [] := by
  intro empty
  have head := reverse_head background memory reversed result used
  rw [empty] at head
  cases head

theorem reverse_chain (isOr : Bool) (caller : Statement) (background : Stack → List Bool)
    (memory : Store) (reversed result : List Bool) (used : Nat) :
    (reverseTrace background memory reversed result used).IsChain
      (fun before after => TM2.step (program isOr caller) before = some after) := by
  induction reversed generalizing memory result with
  | nil => exact List.isChain_cons_cons.mpr ⟨step_reverse_end isOr caller background memory result _, by simp⟩
  | cons bit later ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_, ih _ _⟩
    intro next present
    rw [reverse_head] at present
    have same := (Option.mem_some_iff.mp present).symm
    subst next
    exact step_reverse isOr caller background memory bit result later _

theorem reverse_last (background : Stack → List Bool) (memory : Store) (reversed result : List Bool) (used : Nat) :
    (reverseTrace background memory reversed result used).getLast? =
      some (state background 2 (false, false) (reversed.reverse ++ result) [] [] [] (List.replicate used true)) := by
  induction reversed generalizing memory result with
  | nil => rfl
  | cons bit later ih =>
    rw [reverseTrace, List.getLast?_cons_of_ne_nil (reverse_nonempty _ _ _ _ _), ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem reverse_length (background : Stack → List Bool) (memory : Store) (reversed result : List Bool) (used : Nat) :
    (reverseTrace background memory reversed result used).length = reversed.length + 2 := by
  induction reversed generalizing memory result with
  | nil => rfl
  | cons bit later ih => simp only [reverseTrace, List.length_cons, ih]

def restoreTrace (background : Stack → List Bool) : Store → List Bool → Nat → Nat → List State
  | memory, result, room, 0 =>
      [state background 2 memory result [] [] (List.replicate room true) [],
       state background 3 (false, false) result [] [] (List.replicate room true) []]
  | memory, result, room, used + 1 =>
      state background 2 memory result [] [] (List.replicate room true) (List.replicate (used + 1) true) ::
        restoreTrace background (true, true) result (room + 1) used

theorem restore_head (background : Stack → List Bool) (memory : Store) (result : List Bool) (room used : Nat) :
    (restoreTrace background memory result room used).head? =
      some (state background 2 memory result [] [] (List.replicate room true) (List.replicate used true)) := by
  cases used <;> rfl

theorem restore_nonempty (background : Stack → List Bool) (memory : Store) (result : List Bool) (room used : Nat) :
    restoreTrace background memory result room used ≠ [] := by
  intro empty
  have head := restore_head background memory result room used
  rw [empty] at head
  cases head

theorem restore_chain (isOr : Bool) (caller : Statement) (background : Stack → List Bool)
    (memory : Store) (result : List Bool) (room used : Nat) :
    (restoreTrace background memory result room used).IsChain
      (fun before after => TM2.step (program isOr caller) before = some after) := by
  induction used generalizing memory room with
  | zero => exact List.isChain_cons_cons.mpr ⟨step_restore_end isOr caller background memory result _, by simp⟩
  | succ used ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_, ih _ _⟩
    intro next present
    rw [restore_head] at present
    have same := (Option.mem_some_iff.mp present).symm
    subst next
    simpa only [List.replicate_succ] using
      step_restore isOr caller background memory result (List.replicate room true) (List.replicate used true)

theorem restore_last (background : Stack → List Bool) (memory : Store) (result : List Bool) (room used : Nat) :
    (restoreTrace background memory result room used).getLast? =
      some (state background 3 (false, false) result [] [] (List.replicate (room + used) true) []) := by
  induction used generalizing memory room with
  | zero => rfl
  | succ used ih =>
    rw [restoreTrace, List.getLast?_cons_of_ne_nil (restore_nonempty _ _ _ _ _), ih]
    have same : room + 1 + used = room + (used + 1) := by omega
    rw [same]

theorem restore_length (background : Stack → List Bool) (memory : Store) (result : List Bool) (room used : Nat) :
    (restoreTrace background memory result room used).length = used + 2 := by
  induction used generalizing memory room with
  | zero => rfl
  | succ used ih => simp only [restoreTrace, List.length_cons, ih]

def actualTrace (isOr : Bool) (background : Stack → List Bool) (memory : Store) (pairs : List (Bool × Bool)) : List State :=
  (forwardTrace isOr background memory pairs [] 0 ++
    (reverseTrace background (false, false) (outputs isOr pairs).reverse [] pairs.length).tail) ++
    (restoreTrace background (false, false) (outputs isOr pairs) 0 pairs.length).tail

theorem actual_run (isOr : Bool) (caller : Statement) (background : Stack → List Bool)
    (memory : Store) (pairs : List (Bool × Bool)) :
    (actualTrace isOr background memory pairs).head? =
        some (state background 0 memory (pairs.map Prod.fst) (pairs.map Prod.snd) []
          (List.replicate pairs.length true) []) ∧
      (actualTrace isOr background memory pairs).IsChain
        (fun before after => TM2.step (program isOr caller) before = some after) ∧
      (actualTrace isOr background memory pairs).getLast? =
        some (state background 3 (false, false) (outputs isOr pairs) [] []
          (List.replicate pairs.length true) []) ∧
      (actualTrace isOr background memory pairs).length = 3 * pairs.length + 4 := by
  let front := forwardTrace isOr background memory pairs [] 0
  let back := reverseTrace background (false, false) (outputs isOr pairs).reverse [] pairs.length
  let endPart := restoreTrace background (false, false) (outputs isOr pairs) 0 pairs.length
  let middle := state background 1 (false, false) [] [] (outputs isOr pairs).reverse [] (List.replicate pairs.length true)
  let next := state background 2 (false, false) (outputs isOr pairs) [] [] [] (List.replicate pairs.length true)
  have frontHead := forward_head isOr background memory pairs [] 0
  have frontLast : front.getLast? = some middle := by
    simpa only [front, middle, List.append_nil, Nat.zero_add] using forward_last isOr background memory pairs [] 0
  have backHead : back.head? = some middle := reverse_head _ _ _ _ _
  have backLast : back.getLast? = some next := by
    simpa only [back, next, List.reverse_reverse, List.append_nil] using
      reverse_last background (false, false) (outputs isOr pairs).reverse [] pairs.length
  have endHead : endPart.head? = some next := restore_head _ _ _ _ _
  have backEq : back = middle :: back.tail := by
    obtain ⟨rest, same⟩ := List.head?_eq_some_iff.mp backHead
    rw [same]
    rfl
  have endEq : endPart = next :: endPart.tail := by
    obtain ⟨rest, same⟩ := List.head?_eq_some_iff.mp endHead
    rw [same]
    rfl
  have firstJoin := NativeTrace.join_chain front middle back.tail frontLast
    (forward_chain isOr caller background memory pairs [] 0) (backEq ▸ reverse_chain isOr caller background _ _ _ _)
  have firstLast : (front ++ back.tail).getLast? = some next :=
    (NativeTrace.join_last front middle back.tail frontLast).trans ((congrArg List.getLast? backEq).symm.trans backLast)
  refine ⟨?_, NativeTrace.join_chain _ _ _ firstLast firstJoin (endEq ▸ restore_chain isOr caller background _ _ _ _), ?_, ?_⟩
  · change ((front ++ back.tail) ++ endPart.tail).head? = _
    rw [List.head?_append, List.head?_append, frontHead]
    rfl
  · have finalLast : endPart.getLast? = some (state background 3 (false, false)
        (outputs isOr pairs) [] [] (List.replicate pairs.length true) []) := by
      simpa only [endPart, Nat.zero_add] using restore_last background (false, false) (outputs isOr pairs) 0 pairs.length
    exact (NativeTrace.join_last _ _ _ firstLast).trans
      ((congrArg List.getLast? endEq).symm.trans finalLast)
  · have fl := forward_length isOr background memory pairs [] 0
    have rl := reverse_length background (false, false) (outputs isOr pairs).reverse [] pairs.length
    have el := restore_length background (false, false) (outputs isOr pairs) 0 pairs.length
    have ol : (outputs isOr pairs).length = pairs.length := List.length_map _
    simp only [actualTrace, List.length_append, List.length_tail, fl, rl, el, List.length_reverse, ol]
    omega

def pairBits {width : Nat} (left right : BitVec width) : List (Bool × Bool) :=
  List.ofFn (fun point : Fin width => (left.getLsbD point.val, right.getLsbD point.val))

def wordResult {width : Nat} (isOr : Bool) (left right : BitVec width) : BitVec width :=
  if isOr then left ||| right else left &&& right

theorem pairBits_left {width : Nat} (left right : BitVec width) :
    (pairBits left right).map Prod.fst = WordBank.bits left := by
  simp only [pairBits, List.map_ofFn, WordBank.bits, Function.comp_def]

theorem pairBits_right {width : Nat} (left right : BitVec width) :
    (pairBits left right).map Prod.snd = WordBank.bits right := by
  simp only [pairBits, List.map_ofFn, WordBank.bits, Function.comp_def]

theorem outputs_pairBits {width : Nat} (isOr : Bool) (left right : BitVec width) :
    outputs isOr (pairBits left right) = WordBank.bits (wordResult isOr left right) := by
  cases isOr <;> simp only [outputs, pairBits, List.map_ofFn, combine, wordResult, WordBank.bits,
    Bool.false_eq_true, ite_false, ite_true, BitVec.getLsbD_and, BitVec.getLsbD_or, Function.comp_def]

end PaperProofs.Common.Native.PSTRWordBool.Bitwise
