module

public import Common.PSTR_WordVM_FieldRead_002
public import Common.PSTR_WordBool_NativeTrace_006

/-! One SAME actual finite TM2 run copies an arbitrary-width field,
restores its source and real width tally, empties BOTH scratch stacks and
executes a real HALT. Source counts and occupied finite stack lengths are
proved here; raw Bool/track adapters and native compilation remain separate. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordVM.FieldCopy

open Turing

def restoreStart (memory : Store) (reverseWord word target width : List Bool) : State :=
  state (some 1) memory word target width reverseWord (List.replicate reverseWord.length true)

def restoreFinal (reverseWord word target width : List Bool) : State :=
  state (some 2) (false, false) (reverseWord.reverse ++ word)
    (reverseWord.reverse ++ target) (List.replicate reverseWord.length true ++ width) [] []

def restoreTrace (memory : Store) : List Bool → List Bool → List Bool → List Bool → List State
  | [], word, target, width =>
      [restoreStart memory [] word target width, restoreFinal [] word target width]
  | bit :: later, word, target, width =>
      restoreStart memory (bit :: later) word target width ::
        restoreTrace (true, bit) later (bit :: word) (bit :: target) (true :: width)

theorem restoreTrace_nonempty (memory : Store) (reverseWord word target width : List Bool) :
    restoreTrace memory reverseWord word target width ≠ [] := by
  cases reverseWord <;> intro equality <;> cases equality

theorem restoreTrace_head (memory : Store) (reverseWord word target width : List Bool) :
    (restoreTrace memory reverseWord word target width).head? =
      some (restoreStart memory reverseWord word target width) := by
  cases reverseWord <;> rfl

theorem restoreTrace_decomp (memory : Store) (reverseWord word target width : List Bool) :
    restoreTrace memory reverseWord word target width =
      restoreStart memory reverseWord word target width ::
        (restoreTrace memory reverseWord word target width).tail := by
  cases reverseWord <;> rfl

theorem restoreTrace_last (memory : Store) (reverseWord word target width : List Bool) :
    (restoreTrace memory reverseWord word target width).getLast? =
      some (restoreFinal reverseWord word target width) := by
  induction reverseWord generalizing memory word target width with
  | nil => rfl
  | cons bit later ih =>
    rw [restoreTrace, last_cons_of_nonempty _ _ (restoreTrace_nonempty _ _ _ _ _), ih]
    simp only [restoreFinal, List.reverse_cons, List.length_cons,
      List.replicate_succ', List.append_assoc, List.cons_append, List.nil_append]

theorem restoreTrace_chain (memory : Store) (reverseWord word target width : List Bool) :
    (restoreTrace memory reverseWord word target width).IsChain
      (fun before after => TM2.step program before = some after) := by
  induction reverseWord generalizing memory word target width with
  | nil =>
    apply List.isChain_cons_cons.mpr
    refine ⟨?_, List.isChain_singleton _⟩
    simpa only [restoreStart, restoreFinal, List.length_nil, List.replicate_zero,
      List.reverse_nil, List.nil_append] using restore_done memory word target width []
  | cons bit later ih =>
    apply prepend_chain (TM2.step program)
      (restoreStart memory (bit :: later) word target width)
      (restoreStart (true, bit) later (bit :: word) (bit :: target) (true :: width))
      (restoreTrace (true, bit) later (bit :: word) (bit :: target) (true :: width))
      (restoreTrace_head _ _ _ _ _)
    · simpa only [restoreStart, List.length_cons, List.replicate_succ] using
        restore_bit memory bit word target width later (List.replicate later.length true)
    · exact ih _ _ _ _

theorem restoreTrace_length (memory : Store) (reverseWord word target width : List Bool) :
    (restoreTrace memory reverseWord word target width).length = reverseWord.length + 2 := by
  induction reverseWord generalizing memory word target width with
  | nil => rfl
  | cons bit later ih =>
    simp only [restoreTrace, List.length_cons, ih]

theorem restoreTrace_mass (memory : Store) (reverseWord word target width : List Bool) :
    ∀ configuration ∈ restoreTrace memory reverseWord word target width,
      occupied configuration ≤ 3 * reverseWord.length + word.length + target.length + width.length := by
  induction reverseWord generalizing memory word target width with
  | nil =>
    intro configuration present
    simp only [restoreTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · simp only [restoreStart, occupied_state, List.length_nil, List.length_replicate]
      omega
    · simp only [restoreFinal, occupied_state, List.length_append,
        List.length_reverse, List.length_nil, List.length_replicate]
      omega
  | cons bit later ih =>
    intro configuration present
    rcases List.mem_cons.mp present with same | after
    · subst configuration
      simp only [restoreStart, occupied_state, List.length_cons, List.length_replicate]
      omega
    · have bound := ih (true, bit) (bit :: word) (bit :: target) (true :: width) configuration after
      simp only [List.length_cons] at bound ⊢
      omega

def copyStart (memory : Store) (word suffix target : List Bool) : State :=
  readStart memory word suffix target [] []

def copyPort (word suffix target : List Bool) : State :=
  state (some 2) (false, false) (word ++ suffix) (word ++ target)
    (List.replicate word.length true) [] []

def copyFinal (word suffix target : List Bool) : State :=
  state none (false, false) (word ++ suffix) (word ++ target)
    (List.replicate word.length true) [] []

def copyBack (memory : Store) (word suffix target : List Bool) : List State :=
  restoreTrace (false, lastRead memory word) word.reverse suffix target []

theorem copyMiddle_eq (memory : Store) (word suffix target : List Bool) :
    readFinal memory word suffix target [] [] =
      restoreStart (false, lastRead memory word) word.reverse suffix target [] := by
  simp only [readFinal, restoreStart, List.append_nil, List.length_reverse]

theorem copyBack_decomp (memory : Store) (word suffix target : List Bool) :
    readFinal memory word suffix target [] [] :: (copyBack memory word suffix target).tail =
      copyBack memory word suffix target := by
  unfold copyBack
  rw [copyMiddle_eq]
  exact (restoreTrace_decomp _ _ _ _ _).symm

def copyPortTrace (memory : Store) (word suffix target : List Bool) : List State :=
  readTrace memory word suffix target [] [] ++ (copyBack memory word suffix target).tail

theorem copyPortTrace_head (memory : Store) (word suffix target : List Bool) :
    (copyPortTrace memory word suffix target).head? = some (copyStart memory word suffix target) := by
  rw [copyPortTrace, List.head?_append, readTrace_head]
  rfl

theorem copyPortTrace_chain (memory : Store) (word suffix target : List Bool) :
    (copyPortTrace memory word suffix target).IsChain
      (fun before after => TM2.step program before = some after) := by
  have back := restoreTrace_chain (false, lastRead memory word) word.reverse suffix target []
  change (copyBack memory word suffix target).IsChain _ at back
  rw [← copyBack_decomp memory word suffix target] at back
  exact PSTRWordBool.NativeTrace.join_chain _ _ _ (readTrace_last _ _ _ _ _ _)
    (readTrace_chain _ _ _ _ _ _) back

theorem copyPortTrace_last (memory : Store) (word suffix target : List Bool) :
    (copyPortTrace memory word suffix target).getLast? = some (copyPort word suffix target) := by
  calc
    _ = (readFinal memory word suffix target [] [] :: (copyBack memory word suffix target).tail).getLast? :=
      PSTRWordBool.NativeTrace.join_last _ _ _ (readTrace_last _ _ _ _ _ _)
    _ = (copyBack memory word suffix target).getLast? := congrArg List.getLast? (copyBack_decomp _ _ _ _)
    _ = some (copyPort word suffix target) := by
      unfold copyBack
      rw [restoreTrace_last]
      simp only [restoreFinal, copyPort, List.reverse_reverse, List.length_reverse, List.append_nil]

theorem copyPortTrace_length (memory : Store) (word suffix target : List Bool) :
    (copyPortTrace memory word suffix target).length = 2 * word.length + 3 := by
  simp only [copyPortTrace, List.length_append, List.length_tail, copyBack,
    readTrace_length, restoreTrace_length, List.length_reverse]
  omega

theorem copyPortTrace_mass (memory : Store) (word suffix target : List Bool) :
    ∀ configuration ∈ copyPortTrace memory word suffix target,
      occupied configuration ≤ 3 * word.length + suffix.length + target.length := by
  intro configuration present
  rcases List.mem_append.mp present with outward | returning
  · have mass := readTrace_mass memory word suffix target [] [] configuration outward
    simp only [List.length_nil] at mass
    omega
  · have member : configuration ∈ copyBack memory word suffix target :=
      List.mem_of_mem_tail returning
    have bound := restoreTrace_mass (false, lastRead memory word) word.reverse suffix target []
      configuration member
    simp only [List.length_reverse, List.length_nil, Nat.add_zero] at bound
    exact bound

def copyTrace (memory : Store) (word suffix target : List Bool) : List State :=
  copyPortTrace memory word suffix target ++ [copyFinal word suffix target]

theorem copyTrace_head (memory : Store) (word suffix target : List Bool) :
    (copyTrace memory word suffix target).head? = some (copyStart memory word suffix target) := by
  rw [copyTrace, List.head?_append, copyPortTrace_head]
  rfl

theorem copyTrace_last (memory : Store) (word suffix target : List Bool) :
    (copyTrace memory word suffix target).getLast? = some (copyFinal word suffix target) :=
  List.getLast?_append_cons _ _ []

theorem copyTrace_chain (memory : Store) (word suffix target : List Bool) :
    (copyTrace memory word suffix target).IsChain
      (fun before after => TM2.step program before = some after) := by
  apply PSTRWordBool.NativeTrace.join_chain _ (copyPort word suffix target)
    [copyFinal word suffix target] (copyPortTrace_last _ _ _ _) (copyPortTrace_chain _ _ _ _)
  exact List.isChain_cons_cons.mpr
    ⟨terminal_step (false, false) (word ++ suffix) (word ++ target)
      (List.replicate word.length true) [] [], List.isChain_singleton _⟩

theorem copyTrace_length (memory : Store) (word suffix target : List Bool) :
    (copyTrace memory word suffix target).length = 2 * word.length + 4 := by
  simp only [copyTrace, List.length_append, List.length_cons, List.length_nil, copyPortTrace_length]

theorem copyTrace_transitions (memory : Store) (word suffix target : List Bool) :
    (copyTrace memory word suffix target).length - 1 = 2 * word.length + 3 := by
  rw [copyTrace_length]
  omega

theorem copyFinal_halted (word suffix target : List Bool) :
    TM2.step program (copyFinal word suffix target) = none := rfl

theorem copyTrace_mass (memory : Store) (word suffix target : List Bool) :
    ∀ configuration ∈ copyTrace memory word suffix target,
      occupied configuration ≤ 3 * word.length + suffix.length + target.length := by
  intro configuration present
  rcases List.mem_append.mp present with before | final
  · exact copyPortTrace_mass memory word suffix target configuration before
  · have same := List.mem_singleton.mp final
    subst configuration
    simp only [copyFinal, occupied_state, List.length_append, List.length_replicate, List.length_nil]
    omega

theorem copyTrace_stack_bound (memory : Store) (word suffix target : List Bool) :
    ∀ configuration ∈ copyTrace memory word suffix target, ∀ slot,
      (configuration.stk slot).length ≤ 3 * word.length + suffix.length + target.length := by
  intro configuration present slot
  exact (each_stack_le_occupied configuration slot).trans (copyTrace_mass _ _ _ _ _ present)

/-- Concrete internal-entry execution, not a raw Bool/track adapter theorem.
The source field and arbitrary suffix are restored, the destination gains
that SAME field, the real width tally returns and both scratch stacks empty. -/
theorem actual_copy (memory : Store) (word suffix target : List Bool) :
    (copyTrace memory word suffix target).head? = some (copyStart memory word suffix target) ∧
    (copyTrace memory word suffix target).IsChain
      (fun before after => TM2.step program before = some after) ∧
    (copyTrace memory word suffix target).getLast? = some (copyFinal word suffix target) ∧
    TM2.step program (copyFinal word suffix target) = none ∧
    (copyFinal word suffix target).stk 0 = word ++ suffix ∧
    (copyFinal word suffix target).stk 1 = word ++ target ∧
    (copyFinal word suffix target).stk 2 = List.replicate word.length true ∧
    (copyFinal word suffix target).stk 3 = [] ∧
    (copyFinal word suffix target).stk 4 = [] ∧
    (copyTrace memory word suffix target).length = 2 * word.length + 4 ∧
    ∀ configuration ∈ copyTrace memory word suffix target,
      occupied configuration ≤ 3 * word.length + suffix.length + target.length :=
  ⟨copyTrace_head _ _ _ _, copyTrace_chain _ _ _ _, copyTrace_last _ _ _ _,
    copyFinal_halted _ _ _, rfl, rfl, rfl, rfl, rfl,
    copyTrace_length _ _ _ _, copyTrace_mass _ _ _ _⟩

end PaperProofs.Common.Native.PSTRWordVM.FieldCopy
