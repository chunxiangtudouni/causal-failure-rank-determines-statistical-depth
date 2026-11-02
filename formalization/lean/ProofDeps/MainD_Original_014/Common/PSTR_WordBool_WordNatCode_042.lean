module

public import Common.PSTR_WordBool_ContextLift_041
public import Common.PSTR_TM_TrimValue_104

/-! Actual Word-field to raw Nat input formatter for reused Nat callees.
Permanent bank10 is framed. Only field3, virtualL1/virtualR0 and scratch12
are touched. Width/counters are actual lists, never finite-control values.
The caller begins at active6 after the real5→6 goto. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.WordNatIO

open Turing
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMTrimCode103 (keepReverse trimmed)

abbrev Stack := Fin 16
abbrev Label := Fin 7
abbrev Store := Bool × Bool
abbrev Alphabet (_ : Stack) := Bool
abbrev State := TM2.Cfg Alphabet Label Store
abbrev Statement := TM2.Stmt Alphabet Label Store

def capture (_memory : Store) (value : Option Bool) : Store :=
  (value.isSome, value.getD false)

def jump (label : Label) : Statement := .goto (fun _ => label)

def program (caller : Statement) (label : Label) : Statement :=
  match label.val with
  | 0 => .pop 3 capture (.branch Prod.fst
      (.push 1 Prod.snd (jump 0)) (jump 1))
  | 1 => .pop 1 capture (.branch Prod.fst
      (.branch Prod.snd (.push 1 (fun _ => true) (jump 2)) (jump 1))
      (.push 0 (fun _ => false) (.push 12 (fun _ => true) (jump 3))))
  | 2 => .pop 1 capture (.branch Prod.fst
      (.push 0 Prod.snd (.push 12 (fun _ => true) (jump 2))) (jump 3))
  | 3 => .push 0 (fun _ => false) (jump 4)
  | 4 => .pop 12 capture (.branch Prod.fst
      (.push 0 (fun _ => true) (jump 4)) (jump 5))
  | 5 => jump 6
  | _ => caller

theorem program_zero (caller : Statement) : program caller 0 =
    .pop 3 capture (.branch Prod.fst (.push 1 Prod.snd (jump 0)) (jump 1)) := rfl

theorem program_one (caller : Statement) : program caller 1 =
    .pop 1 capture (.branch Prod.fst
      (.branch Prod.snd (.push 1 (fun _ => true) (jump 2)) (jump 1))
      (.push 0 (fun _ => false) (.push 12 (fun _ => true) (jump 3)))) := rfl

theorem program_two (caller : Statement) : program caller 2 =
    .pop 1 capture (.branch Prod.fst
      (.push 0 Prod.snd (.push 12 (fun _ => true) (jump 2))) (jump 3)) := rfl

theorem program_three (caller : Statement) : program caller 3 =
    .push 0 (fun _ => false) (jump 4) := rfl

theorem program_four (caller : Statement) : program caller 4 =
    .pop 12 capture (.branch Prod.fst (.push 0 (fun _ => true) (jump 4)) (jump 5)) := rfl

theorem program_five (caller : Statement) : program caller 5 = jump 6 := rfl

def cells (background : Stack → List Bool) (word left output counter : List Bool) (slot : Stack) : List Bool :=
  if slot = 3 then word else if slot = 1 then left else
    if slot = 0 then output else if slot = 12 then counter else background slot

def state (background : Stack → List Bool) (label : Label) (memory : Store)
    (word left output counter : List Bool) : State :=
  ⟨some label, memory, cells background word left output counter⟩

theorem cells_word (background : Stack → List Bool) (word left output counter : List Bool) :
    cells background word left output counter 3 = word := rfl

theorem cells_left (background : Stack → List Bool) (word left output counter : List Bool) :
    cells background word left output counter 1 = left := rfl

theorem cells_output (background : Stack → List Bool) (word left output counter : List Bool) :
    cells background word left output counter 0 = output := rfl

theorem cells_counter (background : Stack → List Bool) (word left output counter : List Bool) :
    cells background word left output counter 12 = counter := rfl

theorem cells_frame (background : Stack → List Bool) (word left output counter : List Bool)
    (slot : Stack) (notWord : slot ≠ 3) (notLeft : slot ≠ 1) (notOutput : slot ≠ 0) (notCounter : slot ≠ 12) :
    cells background word left output counter slot = background slot := by
  simp only [cells, ite_eq_right notWord, ite_eq_right notLeft, ite_eq_right notOutput, ite_eq_right notCounter]

theorem update_word (background : Stack → List Bool) (word left output counter replacement : List Bool) :
    Function.update (cells background word left output counter) 3 replacement =
      cells background replacement left output counter := by
  funext slot
  fin_cases slot <;> simp [cells, Function.update]

theorem update_left (background : Stack → List Bool) (word left output counter replacement : List Bool) :
    Function.update (cells background word left output counter) 1 replacement =
      cells background word replacement output counter := by
  funext slot
  fin_cases slot <;> simp [cells, Function.update]

theorem update_output (background : Stack → List Bool) (word left output counter replacement : List Bool) :
    Function.update (cells background word left output counter) 0 replacement =
      cells background word left replacement counter := by
  funext slot
  fin_cases slot <;> simp [cells, Function.update]

theorem update_counter (background : Stack → List Bool) (word left output counter replacement : List Bool) :
    Function.update (cells background word left output counter) 12 replacement =
      cells background word left output replacement := by
  funext slot
  fin_cases slot <;> simp [cells, Function.update]

def encodedWord (word : List Bool) : List Bool :=
  List.replicate (trimmed word).length true ++ false :: trimmed word

theorem encodedWord_correct (word : List Bool) :
    encodedWord word = encodeNat (PSTRTMIncrement009.valueDigits word) := by
  unfold encodedWord
  rw [PSTRTMTrimValue104.trimmed_canonical]
  have length : (PSTRTMNatValue017.rawPayload (PSTRTMIncrement009.valueDigits word)).length =
      natBits (PSTRTMIncrement009.valueDigits word) := by
    simp only [PSTRTMNatValue017.rawPayload, List.length_ofFn]
  rw [length]
  exact (List.append_assoc (List.replicate (natBits (PSTRTMIncrement009.valueDigits word)) true)
    [false] (PSTRTMNatValue017.rawPayload (PSTRTMIncrement009.valueDigits word))).symm

theorem reverse_bit (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (bit : Bool) (word left output counter : List Bool) :
    TM2.step (program caller) (state background 0 memory (bit :: word) left output counter) =
      some (state background 0 (true, bit) word (bit :: left) output counter) := by
  change some (TM2.stepAux (program caller 0) memory
    (cells background (bit :: word) left output counter)) = _
  simp only [program_zero, TM2.stepAux, cells_word, List.head?_cons, List.tail_cons, capture,
    Option.isSome_some, Option.getD_some, Bool.cond_true, jump]
  rw [update_word, cells_left, update_left]
  rfl

theorem reverse_done (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (left output counter : List Bool) :
    TM2.step (program caller) (state background 0 memory [] left output counter) =
      some (state background 1 (false, false) [] left output counter) := by
  change some (TM2.stepAux (program caller 0) memory (cells background [] left output counter)) = _
  simp only [program_zero, TM2.stepAux, cells_word, List.head?_nil, List.tail_nil, capture,
    Option.isSome_none, Option.getD_none, Bool.cond_false, jump]
  rw [update_word]
  rfl

def reverseTrace (background : Stack → List Bool) :
    Store → List Bool → List Bool → List Bool → List Bool → List State
  | memory, [], left, output, counter =>
      [state background 0 memory [] left output counter,
        state background 1 (false, false) [] left output counter]
  | memory, bit :: word, left, output, counter =>
      state background 0 memory (bit :: word) left output counter ::
        reverseTrace background (true, bit) word (bit :: left) output counter

theorem reverseTrace_head (background : Stack → List Bool) (memory : Store)
    (word left output counter : List Bool) :
    (reverseTrace background memory word left output counter).head? =
      some (state background 0 memory word left output counter) := by
  cases word <;> rfl

theorem reverseTrace_nonempty (background : Stack → List Bool) (memory : Store)
    (word left output counter : List Bool) :
    reverseTrace background memory word left output counter ≠ [] := by
  cases word <;> intro impossible <;> cases impossible

theorem reverseTrace_length (background : Stack → List Bool) (memory : Store)
    (word left output counter : List Bool) :
    (reverseTrace background memory word left output counter).length = word.length + 2 := by
  induction word generalizing memory left with
  | nil => rfl
  | cons bit word ih => simp only [reverseTrace, List.length_cons, ih]

theorem reverseTrace_last (background : Stack → List Bool) (memory : Store)
    (word left output counter : List Bool) :
    (reverseTrace background memory word left output counter).getLast? =
      some (state background 1 (false, false) [] (word.reverse ++ left) output counter) := by
  induction word generalizing memory left with
  | nil => rfl
  | cons bit word ih =>
    rw [reverseTrace, StatementClock.prepend_last _ _ (by rw [reverseTrace_length]; omega), ih]
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

theorem reverseTrace_chain (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (word left output counter : List Bool) :
    (reverseTrace background memory word left output counter).IsChain
      (fun before after => TM2.step (program caller) before = some after) := by
  induction word generalizing memory left with
  | nil => exact List.isChain_cons_cons.mpr ⟨reverse_done caller background memory left output counter,
      List.isChain_singleton _⟩
  | cons bit word ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_, ih (true, bit) (bit :: left)⟩
    intro next present
    rw [reverseTrace_head] at present
    have same := Option.some.inj (Option.mem_def.mp present)
    subst next
    exact reverse_bit caller background memory bit word left output counter

theorem reverseTrace_fields (background : Stack → List Bool) (memory : Store)
    (word left output counter : List Bool) :
    ∀ current ∈ reverseTrace background memory word left output counter,
      ∃ (remaining reversed : List Bool) (flags : Label × Store),
        current = state background flags.1 flags.2 remaining reversed output counter ∧
        remaining.length + reversed.length = word.length + left.length := by
  induction word generalizing memory left with
  | nil =>
    intro current present
    simp only [reverseTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · exact ⟨[], left, (0, memory), rfl, rfl⟩
    · exact ⟨[], left, (1, (false, false)), rfl, rfl⟩
  | cons bit word ih =>
    intro current present
    rcases List.mem_cons.mp present with same | later
    · subst current
      exact ⟨bit :: word, left, (0, memory), rfl, rfl⟩
    · obtain ⟨remaining, reversed, flags, same, mass⟩ := ih (true, bit) (bit :: left) current later
      refine ⟨remaining, reversed, flags, same, ?_⟩
      simp only [List.length_cons] at mass ⊢
      omega

end PaperProofs.Common.Native.PSTRWordBool.WordNatIO
