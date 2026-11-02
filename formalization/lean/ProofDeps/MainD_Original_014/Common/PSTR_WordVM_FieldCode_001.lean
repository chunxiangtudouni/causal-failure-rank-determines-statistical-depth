module

public import Mathlib.Computability.TuringMachine.StackTuringMachine
public import Mathlib.Data.List.Chain
public import Mathlib.Tactic.FinCases
public meta import Lean.Elab.Tactic.Omega

/-! Fixed finite source for a reusable word-field copy. Width is a REAL
stack of TRUE cells. Neither width nor a bound occurs in code/control.
The source word, destination and both real backup stacks are manipulated
by actual TM2 push/pop operations. Raw entry/exit codecs are separate. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordVM.FieldCopy

open Turing

abbrev Stack := Fin 5
abbrev Label := Fin 3
abbrev Alphabet (_ : Stack) := Bool
abbrev Store := Bool × Bool
abbrev State := TM2.Cfg Alphabet Label Store

def captureWidth (memory : Store) (value : Option Bool) : Store :=
  (value.isSome, memory.2)

def captureData (_ : Store) (value : Option Bool) : Store :=
  (value.isSome, value.getD false)

def program (label : Label) : TM2.Stmt Alphabet Label Store :=
  if label = 0 then
    .pop 2 captureWidth
      (.branch Prod.fst
        (.pop 0 captureData
          (.push 3 Prod.snd (.push 4 (fun _ => true) (.goto (fun _ => 0)))))
        (.goto (fun _ => 1)))
  else if label = 1 then
    .pop 3 captureData
      (.branch Prod.fst
        (.push 0 Prod.snd
          (.push 1 Prod.snd
            (.pop 4 (fun memory _ => memory)
              (.push 2 (fun _ => true) (.goto (fun _ => 1))))))
        (.goto (fun _ => 2)))
  else .halt

def slots (word target width reverseWord usedWidth : List Bool) : Stack → List Bool :=
  fun slot => if slot = 0 then word else if slot = 1 then target else
    if slot = 2 then width else if slot = 3 then reverseWord else usedWidth

def state (label : Option Label) (memory : Store)
    (word target width reverseWord usedWidth : List Bool) : State :=
  ⟨label, memory, slots word target width reverseWord usedWidth⟩

theorem slots_zero (word target width reverseWord usedWidth : List Bool) :
    slots word target width reverseWord usedWidth 0 = word := rfl

theorem slots_one (word target width reverseWord usedWidth : List Bool) :
    slots word target width reverseWord usedWidth 1 = target := rfl

theorem slots_two (word target width reverseWord usedWidth : List Bool) :
    slots word target width reverseWord usedWidth 2 = width := rfl

theorem slots_three (word target width reverseWord usedWidth : List Bool) :
    slots word target width reverseWord usedWidth 3 = reverseWord := rfl

theorem slots_four (word target width reverseWord usedWidth : List Bool) :
    slots word target width reverseWord usedWidth 4 = usedWidth := rfl

theorem update_word (word target width reverseWord usedWidth replacement : List Bool) :
    Function.update (slots word target width reverseWord usedWidth) 0 replacement =
      slots replacement target width reverseWord usedWidth := by
  funext slot
  fin_cases slot <;> simp [slots]

theorem update_target (word target width reverseWord usedWidth replacement : List Bool) :
    Function.update (slots word target width reverseWord usedWidth) 1 replacement =
      slots word replacement width reverseWord usedWidth := by
  funext slot
  fin_cases slot <;> simp [slots]

theorem update_width (word target width reverseWord usedWidth replacement : List Bool) :
    Function.update (slots word target width reverseWord usedWidth) 2 replacement =
      slots word target replacement reverseWord usedWidth := by
  funext slot
  fin_cases slot <;> simp [slots]

theorem update_reverse (word target width reverseWord usedWidth replacement : List Bool) :
    Function.update (slots word target width reverseWord usedWidth) 3 replacement =
      slots word target width replacement usedWidth := by
  funext slot
  fin_cases slot <;> simp [slots]

theorem update_used (word target width reverseWord usedWidth replacement : List Bool) :
    Function.update (slots word target width reverseWord usedWidth) 4 replacement =
      slots word target width reverseWord replacement := by
  funext slot
  fin_cases slot <;> simp [slots]

theorem read_bit (memory : Store) (bit : Bool)
    (word target width reverseWord usedWidth : List Bool) :
    TM2.step program (state (some 0) memory (bit :: word) target
      (true :: width) reverseWord usedWidth) =
      some (state (some 0) (true, bit) word target width
        (bit :: reverseWord) (true :: usedWidth)) := by
  simp [state, program, TM2.step, TM2.stepAux, captureWidth, captureData,
    slots_zero, slots_two, slots_three, slots_four,
    update_word, update_width, update_reverse, update_used]

theorem read_done (memory : Store) (word target reverseWord usedWidth : List Bool) :
    TM2.step program (state (some 0) memory word target [] reverseWord usedWidth) =
      some (state (some 1) (false, memory.2) word target [] reverseWord usedWidth) := by
  simp [state, program, TM2.step, TM2.stepAux, captureWidth,
    slots_two, update_width]

theorem restore_bit (memory : Store) (bit : Bool)
    (word target width reverseWord usedWidth : List Bool) :
    TM2.step program (state (some 1) memory word target width
      (bit :: reverseWord) (true :: usedWidth)) =
      some (state (some 1) (true, bit) (bit :: word) (bit :: target)
        (true :: width) reverseWord usedWidth) := by
  simp [state, program, TM2.step, TM2.stepAux, captureData,
    slots_zero, slots_one, slots_two, slots_three, slots_four,
    update_reverse, update_word, update_target,
    update_used, update_width]

theorem restore_done (memory : Store) (word target width usedWidth : List Bool) :
    TM2.step program (state (some 1) memory word target width [] usedWidth) =
      some (state (some 2) (false, false) word target width [] usedWidth) := by
  simp [state, program, TM2.step, TM2.stepAux, captureData,
    slots_three, update_reverse]

theorem terminal_step (memory : Store) (word target width reverseWord usedWidth : List Bool) :
    TM2.step program (state (some 2) memory word target width reverseWord usedWidth) =
      some (state none memory word target width reverseWord usedWidth) := rfl

theorem halted_step (memory : Store) (word target width reverseWord usedWidth : List Bool) :
    TM2.step program (state none memory word target width reverseWord usedWidth) = none := rfl

def occupied (configuration : State) : Nat :=
  (configuration.stk 0).length + (configuration.stk 1).length +
    (configuration.stk 2).length + (configuration.stk 3).length +
    (configuration.stk 4).length

theorem occupied_state (label : Option Label) (memory : Store)
    (word target width reverseWord usedWidth : List Bool) :
    occupied (state label memory word target width reverseWord usedWidth) =
      word.length + target.length + width.length + reverseWord.length + usedWidth.length := rfl

theorem each_stack_le_occupied (configuration : State) (slot : Stack) :
    (configuration.stk slot).length ≤ occupied configuration := by
  fin_cases slot
  · change (configuration.stk 0).length ≤ occupied configuration
    unfold occupied
    omega
  · change (configuration.stk 1).length ≤ occupied configuration
    unfold occupied
    omega
  · change (configuration.stk 2).length ≤ occupied configuration
    unfold occupied
    omega
  · change (configuration.stk 3).length ≤ occupied configuration
    unfold occupied
    omega
  · change (configuration.stk 4).length ≤ occupied configuration
    unfold occupied
    omega

theorem supports : TM2.Supports program (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    fin_cases label <;> simp [program, TM2.SupportsStmt]

theorem prepend_chain {α : Type*} (step : α → Option α)
    (first next : α) (trace : List α) (head : trace.head? = some next)
    (edge : step first = some next)
    (chain : trace.IsChain (fun before after => step before = some after)) :
    (first :: trace).IsChain (fun before after => step before = some after) := by
  cases trace with
  | nil => simp at head
  | cons item later =>
    have same : item = next := Option.some.inj head
    subst item
    exact List.isChain_cons_cons.mpr ⟨edge, chain⟩

theorem last_cons_of_nonempty {α : Type*} (first : α) (later : List α)
    (nonempty : later ≠ []) : (first :: later).getLast? = later.getLast? := by
  cases later with
  | nil => exact (nonempty rfl).elim
  | cons item tail => exact List.getLast?_cons_cons

end PaperProofs.Common.Native.PSTRWordVM.FieldCopy
