module

public import Common.PSTR_WordBool_NatWordCode_047

/-! Actual cleanup of every virtual-left cell and reading of the real unary
Nat header. Header length is a trace witness supplied by the actual callee's
ListBlank output; executable code tests actual bits, never a ghost fuel. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.NatWordIO

open Turing

theorem head_value (right : List Bool) :
    (ListBlank.mk right).head = right.head?.getD false := by
  cases right <;> rfl

theorem header_false (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (right left value reverseWord width used : List Bool)
    (observed : right.head?.getD false = false) :
    TM2.step (program caller) (state background 1 memory right left value reverseWord width used) =
      some (state background 2 (right.head?.isSome, false) right.tail left value reverseWord width used) := by
  change some (TM2.stepAux (program caller 1) memory
    (cells background right left value reverseWord width used)) = _
  simp only [program_one, TM2.stepAux, cells_right, capture, observed, Bool.cond_false, jump]
  rw [update_right]
  rfl

theorem header_true_step (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (right left value reverseWord width used : List Bool)
    (observed : right.head?.getD false = true) :
    TM2.step (program caller) (state background 1 memory right left value reverseWord width used) =
      some (state background 1 (true, true) right.tail (true :: left) value reverseWord width used) := by
  cases right with
  | nil => cases observed
  | cons bit right =>
    cases bit with
    | false => cases observed
    | true => exact header_true caller background memory right left value reverseWord width used

def clearLeftTrace (background : Stack → List Bool) :
    Store → List Bool → List Bool → List Bool → List Bool → List Bool → List Bool → List State
  | memory, right, [], value, reverseWord, width, used =>
      [state background 0 memory right [] value reverseWord width used,
        state background 1 (false, false) right [] value reverseWord width used]
  | memory, right, bit :: left, value, reverseWord, width, used =>
      state background 0 memory right (bit :: left) value reverseWord width used ::
        clearLeftTrace background (true, bit) right left value reverseWord width used

theorem clearLeftTrace_head (background : Stack → List Bool) (memory : Store)
    (right left value reverseWord width used : List Bool) :
    (clearLeftTrace background memory right left value reverseWord width used).head? =
      some (state background 0 memory right left value reverseWord width used) := by
  cases left <;> rfl

theorem clearLeftTrace_length (background : Stack → List Bool) (memory : Store)
    (right left value reverseWord width used : List Bool) :
    (clearLeftTrace background memory right left value reverseWord width used).length = left.length + 2 := by
  induction left generalizing memory with
  | nil => rfl
  | cons bit left ih => simp only [clearLeftTrace, List.length_cons, ih]

theorem clearLeftTrace_last (background : Stack → List Bool) (memory : Store)
    (right left value reverseWord width used : List Bool) :
    (clearLeftTrace background memory right left value reverseWord width used).getLast? =
      some (state background 1 (false, false) right [] value reverseWord width used) := by
  induction left generalizing memory with
  | nil => rfl
  | cons bit left ih =>
    rw [clearLeftTrace, StatementClock.prepend_last _ _ (by rw [clearLeftTrace_length]; omega), ih]

theorem clearLeftTrace_chain (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (right left value reverseWord width used : List Bool) :
    (clearLeftTrace background memory right left value reverseWord width used).IsChain
      (fun before after => TM2.step (program caller) before = some after) := by
  induction left generalizing memory with
  | nil => exact List.isChain_cons_cons.mpr ⟨clear_left_done caller background memory right value reverseWord width used,
      List.isChain_singleton _⟩
  | cons bit left ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_, ih (true, bit)⟩
    intro next present
    rw [clearLeftTrace_head] at present
    have same := Option.some.inj (Option.mem_def.mp present)
    subst next
    exact clear_left_bit caller background memory bit right left value reverseWord width used

theorem clearLeftTrace_fields (background : Stack → List Bool) (memory : Store)
    (right left value reverseWord width used : List Bool) :
    ∀ current ∈ clearLeftTrace background memory right left value reverseWord width used,
      ∃ (remaining : List Bool) (flags : Label × Store),
        current = state background flags.1 flags.2 right remaining value reverseWord width used ∧
        remaining.length ≤ left.length := by
  induction left generalizing memory with
  | nil =>
    intro current present
    simp only [clearLeftTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · exact ⟨[], (0, memory), rfl, le_rfl⟩
    · exact ⟨[], (1, (false, false)), rfl, le_rfl⟩
  | cons bit left ih =>
    intro current present
    rcases List.mem_cons.mp present with same | later
    · subst current
      exact ⟨bit :: left, (0, memory), rfl, le_rfl⟩
    · obtain ⟨remaining, flags, same, small⟩ := ih (true, bit) current later
      exact ⟨remaining, flags, same, small.trans (by simp only [List.length_cons]; omega)⟩

def Header (length : Nat) (payload : ListBlank Bool) (right : List Bool) : Prop :=
  ListBlank.mk right = ListBlank.append (List.replicate length true) (ListBlank.cons false payload)

theorem header_zero_observed (payload : ListBlank Bool) (right : List Bool)
    (certificate : Header 0 payload right) : right.head?.getD false = false := by
  change ListBlank.mk right = ListBlank.cons false payload at certificate
  rw [← head_value right, certificate, ListBlank.head_cons]

theorem header_succ_observed (length : Nat) (payload : ListBlank Bool) (right : List Bool)
    (certificate : Header (length + 1) payload right) : right.head?.getD false = true := by
  change ListBlank.mk right = ListBlank.cons true
    (ListBlank.append (List.replicate length true) (ListBlank.cons false payload)) at certificate
  rw [← head_value right, certificate, ListBlank.head_cons]

theorem header_tail (length : Nat) (payload : ListBlank Bool) (right : List Bool)
    (certificate : Header (length + 1) payload right) : Header length payload right.tail := by
  change ListBlank.mk right = ListBlank.cons true
    (ListBlank.append (List.replicate length true) (ListBlank.cons false payload)) at certificate
  change ListBlank.mk right.tail = _
  rw [← ListBlank.tail_mk, certificate, ListBlank.tail_cons]

def headerTrace (background : Stack → List Bool) :
    Store → Nat → List Bool → List Bool → List Bool → List Bool → List Bool → List Bool → List State
  | memory, 0, right, left, value, reverseWord, width, used =>
      [state background 1 memory right left value reverseWord width used,
        state background 2 (right.head?.isSome, false) right.tail left value reverseWord width used]
  | memory, length + 1, right, left, value, reverseWord, width, used =>
      state background 1 memory right left value reverseWord width used ::
        headerTrace background (true, true) length right.tail (true :: left) value reverseWord width used

theorem headerTrace_head (background : Stack → List Bool) (memory : Store) (length : Nat)
    (right left value reverseWord width used : List Bool) :
    (headerTrace background memory length right left value reverseWord width used).head? =
      some (state background 1 memory right left value reverseWord width used) := by
  cases length <;> rfl

theorem headerTrace_length (background : Stack → List Bool) (memory : Store) (length : Nat)
    (right left value reverseWord width used : List Bool) :
    (headerTrace background memory length right left value reverseWord width used).length = length + 2 := by
  induction length generalizing memory right left with
  | zero => rfl
  | succ length ih => simp only [headerTrace, List.length_cons, ih]

theorem headerTrace_last (background : Stack → List Bool) (memory : Store) (length : Nat)
    (right left value reverseWord width used : List Bool) :
    (headerTrace background memory length right left value reverseWord width used).getLast? =
      some (state background 2 ((right.drop length).head?.isSome, false) (right.drop (length + 1))
        (List.replicate length true ++ left) value reverseWord width used) := by
  induction length generalizing memory right left with
  | zero => cases right <;> rfl
  | succ length ih =>
    rw [headerTrace, StatementClock.prepend_last _ _ (by rw [headerTrace_length]; omega), ih]
    simp only [List.drop_tail, List.replicate_succ', List.append_assoc,
      List.cons_append, List.nil_append]

theorem headerTrace_chain (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (length : Nat) (payload : ListBlank Bool) (right left value reverseWord width used : List Bool)
    (certificate : Header length payload right) :
    (headerTrace background memory length right left value reverseWord width used).IsChain
      (fun before after => TM2.step (program caller) before = some after) := by
  induction length generalizing memory right left with
  | zero =>
    exact List.isChain_cons_cons.mpr ⟨header_false caller background memory right left value reverseWord width used
      (header_zero_observed payload right certificate), List.isChain_singleton _⟩
  | succ length ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_, ih (true, true) right.tail (true :: left) (header_tail length payload right certificate)⟩
    intro next present
    rw [headerTrace_head] at present
    have same := Option.some.inj (Option.mem_def.mp present)
    subst next
    exact header_true_step caller background memory right left value reverseWord width used
      (header_succ_observed length payload right certificate)

theorem headerTrace_fields (background : Stack → List Bool) (memory : Store) (length : Nat)
    (right left value reverseWord width used : List Bool) :
    ∀ current ∈ headerTrace background memory length right left value reverseWord width used,
      ∃ (remaining counter : List Bool) (flags : Label × Store),
        current = state background flags.1 flags.2 remaining counter value reverseWord width used ∧
        remaining.length ≤ right.length ∧ counter.length ≤ left.length + length := by
  induction length generalizing memory right left with
  | zero =>
    intro current present
    simp only [headerTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · exact ⟨right, left, (1, memory), rfl, le_rfl, by omega⟩
    · exact ⟨right.tail, left, (2, (right.head?.isSome, false)), rfl,
        by simp only [List.length_tail]; omega, by omega⟩
  | succ length ih =>
    intro current present
    rcases List.mem_cons.mp present with same | later
    · subst current
      exact ⟨right, left, (1, memory), rfl, le_rfl, by omega⟩
    · obtain ⟨remaining, counter, flags, same, dataBound, countBound⟩ :=
        ih (true, true) right.tail (true :: left) current later
      refine ⟨remaining, counter, flags, same, ?_, ?_⟩
      · simp only [List.length_tail] at dataBound
        omega
      · simp only [List.length_cons] at countBound
        omega

end PaperProofs.Common.Native.PSTRWordBool.NatWordIO
