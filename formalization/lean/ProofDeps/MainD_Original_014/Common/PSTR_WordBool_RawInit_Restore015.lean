module

public import Common.PSTR_WordBool_RawInit_MarkSeek014

/-! Starting at the permanent right sentinel, this fixed table moves
LEFT along the pair parity to the unique temporary selected flag, really
writes it back to FALSE, and really moves LEFT to the next source cell.
Every payload bit and the entire arbitrary suffix remain unchanged. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.Restore

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMSeq005

def machine : Machine 4 := fun label symbol =>
  match label.val with
  | 0 => some (1,.move .left)
  | 1 => some (2,.move .left)
  | 2 => if symbol then some (3,.write false) else some (1,.move .left)
  | 3 => some (4,.move .left)
  | _ => none

def state (label : Fin 5) (left right : List Bool) : MachineState 4 := ⟨label,Tape.mk₂ left right⟩
def reversePairs (bits : List Bool) : List Bool := bits.flatMap (fun bit => [bit,false])

theorem pairs_reverse (bits : List Bool) : (MarkSeek.pairs bits).reverse = reversePairs bits.reverse := by
  induction bits with
  | nil => rfl
  | cons bit later ih =>
    simp [MarkSeek.pairs,reversePairs,List.reverse_cons,List.flatMap_append] at ih ⊢
    exact ih

def start (left remaining : List Bool) (bit : Bool) (suffix : List Bool) : MachineState 4 :=
  match remaining with
  | [] => state 1 (true :: left) (bit :: suffix)
  | first :: later => state 1 (false :: (reversePairs later ++ bit :: true :: left)) (first :: suffix)

def finish (left remaining : List Bool) (bit : Bool) (suffix : List Bool) : MachineState 4 :=
  ⟨4,(Tape.mk₂ left (false :: bit :: (MarkSeek.pairs remaining.reverse ++ suffix))).move .left⟩

def walkTrace (left : List Bool) : List Bool → Bool → List Bool → List (MachineState 4)
  | [], bit, suffix =>
    [state 1 (true :: left) (bit :: suffix),
     state 2 left (true :: bit :: suffix),
     state 3 left (false :: bit :: suffix),
     finish left [] bit suffix]
  | first :: later, bit, suffix =>
    [state 1 (false :: (reversePairs later ++ bit :: true :: left)) (first :: suffix),
     state 2 (reversePairs later ++ bit :: true :: left) (false :: first :: suffix)] ++
      walkTrace left later bit (false :: first :: suffix)

theorem walk_head (left remaining : List Bool) (bit : Bool) (suffix : List Bool) :
    (walkTrace left remaining bit suffix).head? = some (start left remaining bit suffix) := by
  cases remaining <;> rfl

theorem walk_length (left remaining : List Bool) (bit : Bool) (suffix : List Bool) :
    (walkTrace left remaining bit suffix).length = 2*remaining.length+4 := by
  induction remaining generalizing suffix with
  | nil => rfl
  | cons first later ih =>
    simp only [walkTrace,List.length_append,List.length_cons,List.length_nil,ih]
    omega

theorem walk_last (left remaining : List Bool) (bit : Bool) (suffix : List Bool) :
    (walkTrace left remaining bit suffix).getLast? = some (finish left remaining bit suffix) := by
  induction remaining generalizing suffix with
  | nil => rfl
  | cons first later ih =>
    have nonempty : walkTrace left later bit (false :: first :: suffix) ≠ [] := by
      intro empty
      have size := walk_length left later bit (false :: first :: suffix)
      simp only [empty,List.length_nil] at size
      omega
    simp only [walkTrace,List.cons_append,List.nil_append,List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil nonempty,ih]
    simp [finish,MarkSeek.pairs,List.reverse_cons,List.flatMap_append,List.append_assoc]

theorem walk_chain (left remaining : List Bool) (bit : Bool) (suffix : List Bool) :
    (walkTrace left remaining bit suffix).IsChain (fun before after => TM0.step machine before = some after) := by
  induction remaining generalizing suffix with
  | nil =>
    simp [walkTrace,finish,MarkSeek.pairs,state,TM0.step,machine,Tape.mk₂,List.isChain_cons_cons]
  | cons first later ih =>
    rw [walkTrace]
    apply List.IsChain.append
    · apply List.isChain_cons_cons.mpr
      refine ⟨?_,.singleton _⟩
      simp [TM0.step,state,machine,Tape.mk₂]
    · exact ih _
    · intro before beforeLast after afterHead
      simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at beforeLast
      simp only [walk_head,Option.mem_some_iff] at afterHead
      subst before
      subst after
      cases later <;> simp [start,TM0.step,state,machine,reversePairs,Tape.mk₂]

def initial (left higher : List Bool) (bit : Bool) (suffix : List Bool) : MachineState 4 :=
  state 0 ((MarkSeek.pairs higher).reverse ++ bit :: true :: left) suffix

def final (left higher : List Bool) (bit : Bool) (suffix : List Bool) : MachineState 4 :=
  ⟨4,(Tape.mk₂ left (false :: bit :: (MarkSeek.pairs higher ++ suffix))).move .left⟩

def trace (left higher : List Bool) (bit : Bool) (suffix : List Bool) : List (MachineState 4) :=
  initial left higher bit suffix :: walkTrace left higher.reverse bit suffix

theorem actual (left higher : List Bool) (bit : Bool) (suffix : List Bool) (inputLength : Nat) :
    ∃ path, RunsFrom machine (initial left higher bit suffix) path (final left higher bit suffix) ∧
      path.length = 2*higher.length+5 ∧
      ∀ clock, visitedSpace machine inputLength (path.take clock) ≤ inputLength+4*higher.length+11 := by
  have firstStep : TM0.step machine (initial left higher bit suffix) = some (start left higher.reverse bit suffix) := by
    simp only [initial,pairs_reverse]
    cases higher.reverse <;> simp [start,state,TM0.step,machine,reversePairs,Tape.mk₂]
  have chain : (trace left higher bit suffix).IsChain (fun before after => TM0.step machine before = some after) := by
    apply (walk_chain left higher.reverse bit suffix).cons
    intro next member
    simp only [walk_head,Option.mem_some_iff] at member
    subst next
    exact firstStep
  have last : (trace left higher bit suffix).getLast? = some (final left higher bit suffix) := by
    have nonempty : walkTrace left higher.reverse bit suffix ≠ [] := by
      intro empty
      have size := walk_length left higher.reverse bit suffix
      simp only [empty,List.length_nil] at size
      omega
    rw [trace,List.getLast?_cons_of_ne_nil nonempty,walk_last]
    simp only [finish,final,List.reverse_reverse]
  have length : (trace left higher bit suffix).length = 2*higher.length+5 := by
    simp only [trace,List.length_cons,walk_length,List.length_reverse]
  refine ⟨trace left higher bit suffix,⟨rfl,chain,last,?_⟩,length,?_⟩
  · simp [final,TM0.step,machine]
  · intro clock
    have space := PSTRTMTrace002.visitedSpace_le machine inputLength ((trace left higher bit suffix).take clock)
    have short := List.length_take_le' clock (trace left higher bit suffix)
    omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit.Restore
