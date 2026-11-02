module

public import Common.PSTR_WordVM_FieldCode_001

/-! Exact actual first-pass trace: pop one real width cell per word bit,
reverse that bit onto the word backup, and retain the consumed tally.
These trace descriptors do not occur in the executable control store. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordVM.FieldCopy

open Turing

def lastRead (memory : Store) : List Bool → Bool
  | [] => memory.2
  | bit :: later => lastRead (true, bit) later

def readStart (memory : Store) (word suffix target reverseWord usedWidth : List Bool) : State :=
  state (some 0) memory (word ++ suffix) target
    (List.replicate word.length true) reverseWord usedWidth

def readFinal (memory : Store) (word suffix target reverseWord usedWidth : List Bool) : State :=
  state (some 1) (false, lastRead memory word) suffix target []
    (word.reverse ++ reverseWord) (List.replicate word.length true ++ usedWidth)

def readTrace (memory : Store) :
    List Bool → List Bool → List Bool → List Bool → List Bool → List State
  | [], suffix, target, reverseWord, usedWidth =>
      [readStart memory [] suffix target reverseWord usedWidth,
        readFinal memory [] suffix target reverseWord usedWidth]
  | bit :: later, suffix, target, reverseWord, usedWidth =>
      readStart memory (bit :: later) suffix target reverseWord usedWidth ::
        readTrace (true, bit) later suffix target (bit :: reverseWord) (true :: usedWidth)

theorem readTrace_nonempty (memory : Store) (word suffix target reverseWord usedWidth : List Bool) :
    readTrace memory word suffix target reverseWord usedWidth ≠ [] := by
  cases word <;> intro equality <;> cases equality

theorem readTrace_head (memory : Store) (word suffix target reverseWord usedWidth : List Bool) :
    (readTrace memory word suffix target reverseWord usedWidth).head? =
      some (readStart memory word suffix target reverseWord usedWidth) := by
  cases word <;> rfl

theorem readTrace_last (memory : Store) (word suffix target reverseWord usedWidth : List Bool) :
    (readTrace memory word suffix target reverseWord usedWidth).getLast? =
      some (readFinal memory word suffix target reverseWord usedWidth) := by
  induction word generalizing memory reverseWord usedWidth with
  | nil => rfl
  | cons bit later ih =>
    rw [readTrace, last_cons_of_nonempty _ _ (readTrace_nonempty _ _ _ _ _ _), ih]
    simp only [readFinal, lastRead, List.reverse_cons, List.length_cons,
      List.replicate_succ', List.append_assoc, List.cons_append, List.nil_append]

theorem readTrace_chain (memory : Store) (word suffix target reverseWord usedWidth : List Bool) :
    (readTrace memory word suffix target reverseWord usedWidth).IsChain
      (fun before after => TM2.step program before = some after) := by
  induction word generalizing memory reverseWord usedWidth with
  | nil =>
    apply List.isChain_cons_cons.mpr
    refine ⟨?_, List.isChain_singleton _⟩
    simpa only [readStart, readFinal, lastRead, List.nil_append, List.reverse_nil,
      List.length_nil, List.replicate_zero] using read_done memory suffix target reverseWord usedWidth
  | cons bit later ih =>
    apply prepend_chain (TM2.step program)
      (readStart memory (bit :: later) suffix target reverseWord usedWidth)
      (readStart (true, bit) later suffix target (bit :: reverseWord) (true :: usedWidth))
      (readTrace (true, bit) later suffix target (bit :: reverseWord) (true :: usedWidth))
      (readTrace_head _ _ _ _ _ _)
    · simpa only [readStart, List.cons_append, List.length_cons, List.replicate_succ] using
        read_bit memory bit (later ++ suffix) target (List.replicate later.length true)
          reverseWord usedWidth
    · exact ih _ _ _

theorem readTrace_length (memory : Store) (word suffix target reverseWord usedWidth : List Bool) :
    (readTrace memory word suffix target reverseWord usedWidth).length = word.length + 2 := by
  induction word generalizing memory reverseWord usedWidth with
  | nil => rfl
  | cons bit later ih =>
    simp only [readTrace, List.length_cons, ih]

theorem readTrace_mass (memory : Store) (word suffix target reverseWord usedWidth : List Bool) :
    ∀ configuration ∈ readTrace memory word suffix target reverseWord usedWidth,
      occupied configuration =
        2 * word.length + suffix.length + target.length + reverseWord.length + usedWidth.length := by
  induction word generalizing memory reverseWord usedWidth with
  | nil =>
    intro configuration present
    simp only [readTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · simp only [readStart, occupied_state, List.length_append, List.length_nil,
        List.length_replicate]
      omega
    · simp only [readFinal, occupied_state, List.length_append, List.length_reverse,
        List.length_nil, List.length_replicate]
      omega
  | cons bit later ih =>
    intro configuration present
    rcases List.mem_cons.mp present with same | after
    · subst configuration
      simp only [readStart, occupied_state, List.length_append, List.length_cons,
        List.length_replicate]
      omega
    · have mass := ih (true, bit) (bit :: reverseWord) (true :: usedWidth) configuration after
      simp only [List.length_cons] at mass ⊢
      omega

end PaperProofs.Common.Native.PSTRWordVM.FieldCopy
