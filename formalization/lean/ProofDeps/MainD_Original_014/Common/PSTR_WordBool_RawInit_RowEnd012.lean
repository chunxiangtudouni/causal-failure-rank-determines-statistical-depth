module

public import Common.PSTR_WordBool_RawInit_Shape001
public import Common.PSTR_TM_Seq_005
public import Common.PSTR_TM_RawNat_010

/-! Actual fixed-stride output-end search. A true presence bit at offset1
of every33-cell row drives the loop. The first absent presence bit is
read on the actual blank extension, followed by one real LEFT. No row
count or output length is supplied to the finite machine. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.RowEnd

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMSeq005

def machine : Machine 34 := fun label symbol =>
  if label.val = 0 then some (1,.move .right)
  else if label.val = 1 then
    if symbol then some (2,.move .right) else some (34,.move .left)
  else if inside : label.val < 34 then
    some (⟨if label.val = 33 then 1 else label.val+1,by split_ifs <;> omega⟩,.move .right)
  else none

def state (label : Fin 35) (left right : List Bool) : MachineState 34 :=
  ⟨label,Tape.mk₂ left right⟩

def countLabel (remaining : Nat) : Fin 35 :=
  ⟨if remaining = 0 then 1 else 34 - min remaining 32,by split_ifs <;> omega⟩

theorem count_lookup (remaining : Fin 32) (symbol : Bool) :
    machine (countLabel (remaining.val+1)) symbol =
      some (countLabel remaining.val,.move .right) := by
  fin_cases remaining <;> rfl

def walkInto (left : List Bool) : List Bool → List Bool → List (MachineState 34) → List (MachineState 34)
  | [], _, continuation => continuation
  | bit :: later, suffix, continuation =>
    state (countLabel (later.length+1)) left (bit :: (later ++ suffix)) ::
      walkInto (bit :: left) later suffix continuation

theorem walk_length (left bits suffix : List Bool) (continuation : List (MachineState 34)) :
    (walkInto left bits suffix continuation).length = bits.length + continuation.length := by
  induction bits generalizing left with
  | nil => simp only [walkInto,List.length_nil,Nat.zero_add]
  | cons bit later ih => simp only [walkInto,List.length_cons,ih]; omega

theorem walk_head (left bits suffix : List Bool) (continuation : List (MachineState 34))
    (head : continuation.head? = some (state 1 (bits.reverse ++ left) suffix)) :
    (walkInto left bits suffix continuation).head? =
      some (state (countLabel bits.length) left (bits ++ suffix)) := by
  cases bits with
  | nil => simpa [walkInto,countLabel] using head
  | cons bit later => rfl

theorem walk_last (left bits suffix : List Bool) (continuation : List (MachineState 34))
    (nonempty : continuation ≠ []) :
    (walkInto left bits suffix continuation).getLast? = continuation.getLast? := by
  induction bits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    have restNonempty : walkInto (bit :: left) later suffix continuation ≠ [] := by
      have room := List.length_pos_iff.mpr nonempty
      have size := walk_length (bit :: left) later suffix continuation
      intro empty
      simp only [empty,List.length_nil] at size
      omega
    rw [walkInto,List.getLast?_cons_of_ne_nil restNonempty,ih]

theorem walk_chain (left bits suffix : List Bool) (continuation : List (MachineState 34))
    (short : bits.length ≤ 32)
    (head : continuation.head? = some (state 1 (bits.reverse ++ left) suffix))
    (chain : continuation.IsChain (fun before after => TM0.step machine before = some after)) :
    (walkInto left bits suffix continuation).IsChain
      (fun before after => TM0.step machine before = some after) := by
  induction bits generalizing left with
  | nil => exact chain
  | cons bit later ih =>
    have tailHead : continuation.head? = some (state 1 (later.reverse ++ (bit :: left)) suffix) := by
      simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using head
    have tailShort : later.length ≤ 32 := by simpa only [List.length_cons] using Nat.le_of_succ_le short
    have nextHead := walk_head (bit :: left) later suffix continuation tailHead
    apply (ih (bit :: left) tailShort tailHead).cons
    intro next member
    simp only [nextHead,Option.mem_some_iff] at member
    subst next
    have labelStep := count_lookup (⟨later.length,by simp only [List.length_cons] at short; omega⟩ : Fin 32) bit
    simpa only [TM0.step,state,labelStep,Tape.mk₂] using
      (show TM0.step machine
        (state (countLabel (later.length+1)) left (bit :: (later ++ suffix))) =
        some (state (countLabel later.length) (bit :: left) (later ++ suffix)) by
          simp [TM0.step,state,labelStep,Tape.mk₂])

def block (bit : Bool) : List Bool := true :: bit :: List.replicate 31 false
def blocks (bits : List Bool) : List Bool := bits.flatMap block

def scanTrace (left : List Bool) : List Bool → List (MachineState 34)
  | [] => [state 1 left []]
  | bit :: later =>
    state 1 left (blocks (bit :: later)) ::
      walkInto (true :: left) (bit :: List.replicate 31 false) (blocks later)
        (scanTrace ((block bit).reverse ++ left) later)

theorem scan_head (left bits : List Bool) :
    (scanTrace left bits).head? = some (state 1 left (blocks bits)) := by
  cases bits <;> rfl

theorem scan_nonempty (left bits : List Bool) : scanTrace left bits ≠ [] := by
  intro empty
  have head := scan_head left bits
  simp only [empty,List.head?_nil,reduceCtorEq] at head

theorem scan_last (left bits : List Bool) :
    (scanTrace left bits).getLast? = some (state 1 ((blocks bits).reverse ++ left) []) := by
  induction bits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    have walkNonempty : walkInto (true :: left) (bit :: List.replicate 31 false) (blocks later)
        (scanTrace ((block bit).reverse ++ left) later) ≠ [] := by
      intro empty
      have size := walk_length (true :: left) (bit :: List.replicate 31 false) (blocks later)
        (scanTrace ((block bit).reverse ++ left) later)
      simp only [empty,List.length_nil,List.length_cons,List.length_replicate] at size
      omega
    rw [scanTrace,List.getLast?_cons_of_ne_nil walkNonempty,walk_last _ _ _ _ (scan_nonempty _ _),ih]
    simp only [blocks,List.flatMap_cons,List.reverse_append,List.append_assoc]

theorem scan_length (left bits : List Bool) : (scanTrace left bits).length = 33*bits.length+1 := by
  induction bits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    simp only [scanTrace,List.length_cons,walk_length,List.length_replicate,ih]
    omega

theorem scan_chain (left bits : List Bool) :
    (scanTrace left bits).IsChain (fun before after => TM0.step machine before = some after) := by
  induction bits generalizing left with
  | nil => exact .singleton _
  | cons bit later ih =>
    have continuationHead := scan_head ((block bit).reverse ++ left) later
    have endpoint : (bit :: List.replicate 31 false).reverse ++ (true :: left) =
        (block bit).reverse ++ left := by simp [block,List.reverse_cons]
    rw [← endpoint] at continuationHead
    have walking := walk_chain (true :: left) (bit :: List.replicate 31 false) (blocks later)
      (scanTrace ((block bit).reverse ++ left) later) (by simp) continuationHead (ih _)
    have head := walk_head (true :: left) (bit :: List.replicate 31 false) (blocks later)
      (scanTrace ((block bit).reverse ++ left) later) continuationHead
    apply walking.cons
    intro next member
    simp only [head,Option.mem_some_iff] at member
    subst next
    simp [TM0.step,state,machine,blocks,block,countLabel,Tape.mk₂]

def rows (bits : List Bool) : List Bool := rowBits true true ++ bits.flatMap (rowBits false)

theorem normal_padded (bits : List Bool) :
    bits.flatMap (rowBits false) ++ [false] = false :: blocks bits := by
  induction bits with
  | nil => rfl
  | cons bit later ih =>
    simp only [List.flatMap_cons,List.append_assoc,ih,blocks,block,rowBits]
    rfl

theorem rows_padded (bits : List Bool) : rows bits ++ [false] = true :: blocks (true :: bits) := by
  simp only [rows,List.append_assoc,normal_padded,blocks,List.flatMap_cons,block,rowBits]
  rfl

def initial (left bits : List Bool) : MachineState 34 := state 0 left (rows bits)
def finish (left bits : List Bool) : MachineState 34 := state 34 ((rows bits).reverse ++ left) []
def trace (left bits : List Bool) : List (MachineState 34) :=
  [initial left bits] ++ scanTrace (true :: left) (true :: bits) ++ [finish left bits]

theorem actual (left bits : List Bool) (inputLength : Nat) :
    ∃ path, RunsFrom machine (initial left bits) path (finish left bits) ∧
      path.length = 33*(bits.length+1)+3 ∧
      ∀ clock, visitedSpace machine inputLength (path.take clock) ≤ inputLength+66*(bits.length+1)+7 := by
  have paddedTape : Tape.mk₂ left (rows bits) = Tape.mk₂ left (true :: blocks (true :: bits)) := by
    rw [← rows_padded]
    change Tape.mk' (ListBlank.mk left) (ListBlank.mk (rows bits)) = Tape.mk' (ListBlank.mk left) (ListBlank.mk (rows bits ++ [false]))
    rw [PSTRTMRawNat010.blank_append_false]
  have reversePadded : (blocks (true :: bits)).reverse ++ (true :: left) =
      false :: ((rows bits).reverse ++ left) := by
    have rev := congrArg List.reverse (rows_padded bits)
    simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append] at rev
    simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using congrArg (fun xs => xs ++ left) rev.symm
  have firstStep : TM0.step machine (initial left bits) =
      some (state 1 (true :: left) (blocks (true :: bits))) := by
    unfold initial state
    rw [paddedTape]
    simp [TM0.step,machine,Tape.mk₂]
  have lastStep : TM0.step machine (state 1 ((blocks (true :: bits)).reverse ++ (true :: left)) []) =
      some (finish left bits) := by
    rw [reversePadded]
    simp [TM0.step,state,machine,finish,Tape.mk₂]
    rw [show ListBlank.mk [false] = ListBlank.mk ([] : List Bool) from PSTRTMRawNat010.blank_append_false []]
  have chain : (trace left bits).IsChain (fun before after => TM0.step machine before = some after) := by
    have start : ([initial left bits] ++ scanTrace (true :: left) (true :: bits)).IsChain
        (fun before after => TM0.step machine before = some after) := by
      apply List.IsChain.append (.singleton _) (scan_chain _ _)
      intro before beforeLast after afterHead
      simp only [List.getLast?_singleton,Option.mem_some_iff] at beforeLast
      simp only [scan_head,Option.mem_some_iff] at afterHead
      subst before
      subst after
      exact firstStep
    apply List.IsChain.append start (.singleton _)
    intro before beforeLast after afterHead
    simp only [List.getLast?_append,scan_last,Option.some_or,Option.mem_some_iff] at beforeLast
    simp only [List.head?_singleton,Option.mem_some_iff] at afterHead
    subst before
    subst after
    exact lastStep
  have length : (trace left bits).length = 33*(bits.length+1)+3 := by
    simp only [trace,List.length_append,List.length_cons,List.length_nil,scan_length]
    omega
  refine ⟨trace left bits,⟨rfl,chain,?_,?_⟩,length,?_⟩
  · simp only [trace,List.getLast?_append,List.getLast?_singleton,Option.some_or]
  · simp [TM0.step,machine,finish,state]
  · intro clock
    have space := PSTRTMTrace002.visitedSpace_le machine inputLength ((trace left bits).take clock)
    have short := List.length_take_le' clock (trace left bits)
    omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit.RowEnd
