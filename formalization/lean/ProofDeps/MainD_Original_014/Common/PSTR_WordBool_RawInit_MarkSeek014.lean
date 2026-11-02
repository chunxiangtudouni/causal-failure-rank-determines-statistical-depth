module

public import Common.PSTR_WordBool_RawInit_RowAppend013

/-! Actual source-bit selection. Entry0 reads the original payload bit,
moves LEFT, writes the temporary selected flag, crosses arbitrary data
only at the fixed pair parity, then crosses the real zero gap to the
first output bottom bit. The read bit stays in finite control throughout.
No source value or output position is a machine argument. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.MarkSeek

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMSeq005

def bodyLabel (saved : Bool) (phase : Fin 7) : Fin 15 :=
  ⟨1 + (if saved then 7 else 0) + phase.val,by split_ifs <;> omega⟩

def bodyCode (saved : Bool) (phase : Fin 7) (symbol : Bool) : Option (Fin 15 × TM0.Stmt Bool) :=
  match phase.val with
  | 0 => some (bodyLabel saved 1,.write true)
  | 1 => some (bodyLabel saved 2,.move .right)
  | 2 => some (bodyLabel saved 3,.move .right)
  | 3 => some (bodyLabel saved (if symbol then 5 else 4),.move .right)
  | 4 => some (bodyLabel saved 3,.move .right)
  | 5 => some (bodyLabel saved 6,.move .right)
  | _ => if symbol then none else some (bodyLabel saved 6,.move .right)

def machine : Machine 14 := fun label symbol =>
  if label.val = 0 then some (bodyLabel symbol 0,.move .left)
  else if lower : label.val < 8 then
    bodyCode false ⟨label.val-1,by omega⟩ symbol
  else bodyCode true ⟨label.val-8,by omega⟩ symbol

def state (saved : Bool) (phase : Fin 7) (left right : List Bool) : MachineState 14 :=
  ⟨bodyLabel saved phase,Tape.mk₂ left right⟩

theorem body_lookup (saved : Bool) (phase : Fin 7) (symbol : Bool) :
    machine (bodyLabel saved phase) symbol = bodyCode saved phase symbol := by
  cases saved <;> fin_cases phase <;> rfl

def pairs (bits : List Bool) : List Bool := bits.flatMap (fun bit => [false,bit])

def fieldTrace (saved : Bool) (left : List Bool) : List Bool → List Bool → List (MachineState 14)
  | [], suffix => [state saved 3 left (true :: false :: suffix)]
  | bit :: later, suffix =>
    [state saved 3 left (false :: bit :: (pairs later ++ true :: false :: suffix)),
     state saved 4 (false :: left) (bit :: (pairs later ++ true :: false :: suffix))] ++
      fieldTrace saved (bit :: false :: left) later suffix

theorem field_head (saved : Bool) (left bits suffix : List Bool) :
    (fieldTrace saved left bits suffix).head? =
      some (state saved 3 left (pairs bits ++ true :: false :: suffix)) := by
  cases bits <;> rfl

theorem field_last (saved : Bool) (left bits suffix : List Bool) :
    (fieldTrace saved left bits suffix).getLast? =
      some (state saved 3 ((pairs bits).reverse ++ left) (true :: false :: suffix)) := by
  induction bits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    have nonempty : fieldTrace saved (bit :: false :: left) later suffix ≠ [] := by
      intro empty
      have head := field_head saved (bit :: false :: left) later suffix
      simp only [empty,List.head?_nil,reduceCtorEq] at head
    simp only [fieldTrace,List.cons_append,List.nil_append,List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil nonempty,ih]
    simp [pairs,List.append_assoc]

theorem field_length (saved : Bool) (left bits suffix : List Bool) :
    (fieldTrace saved left bits suffix).length = 2*bits.length+1 := by
  induction bits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    simp only [fieldTrace,List.length_append,List.length_cons,List.length_nil,ih]
    omega

theorem field_chain (saved : Bool) (left bits suffix : List Bool) :
    (fieldTrace saved left bits suffix).IsChain (fun before after => TM0.step machine before = some after) := by
  induction bits generalizing left with
  | nil => exact .singleton _
  | cons bit later ih =>
    rw [fieldTrace]
    apply List.IsChain.append
    · apply List.isChain_cons_cons.mpr
      refine ⟨?_,.singleton _⟩
      simp [TM0.step,state,body_lookup,bodyCode,Tape.mk₂]
    · exact ih _
    · intro before beforeLast after afterHead
      simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at beforeLast
      simp only [field_head,Option.mem_some_iff] at afterHead
      subst before
      subst after
      simp [TM0.step,state,body_lookup,bodyCode,Tape.mk₂,pairs]

def gapTrace (saved : Bool) (left : List Bool) : Nat → List Bool → List (MachineState 14)
  | 0, tail => [state saved 6 left (true :: tail)]
  | gap+1, tail => state saved 6 left (false :: (List.replicate gap false ++ true :: tail)) ::
      gapTrace saved (false :: left) gap tail

theorem gap_head (saved : Bool) (left tail : List Bool) (gap : Nat) :
    (gapTrace saved left gap tail).head? =
      some (state saved 6 left (List.replicate gap false ++ true :: tail)) := by
  cases gap <;> rfl

theorem gap_length (saved : Bool) (left tail : List Bool) (gap : Nat) :
    (gapTrace saved left gap tail).length = gap+1 := by
  induction gap generalizing left with
  | zero => rfl
  | succ gap ih => simp only [gapTrace,List.length_cons,ih]

theorem gap_last (saved : Bool) (left tail : List Bool) (gap : Nat) :
    (gapTrace saved left gap tail).getLast? =
      some (state saved 6 (List.replicate gap false ++ left) (true :: tail)) := by
  induction gap generalizing left with
  | zero => rfl
  | succ gap ih =>
    have nonempty : gapTrace saved (false :: left) gap tail ≠ [] := by
      intro empty
      have size := gap_length saved (false :: left) tail gap
      simp only [empty,List.length_nil] at size
      omega
    rw [gapTrace,List.getLast?_cons_of_ne_nil nonempty,ih]
    simp only [List.replicate_succ,List.cons_append]
    have same : List.replicate gap false ++ false :: left = false :: (List.replicate gap false ++ left) := by
      calc
        List.replicate gap false ++ false :: left = (List.replicate gap false ++ [false]) ++ left := by
          simp only [List.append_assoc,List.singleton_append]
        _ = false :: (List.replicate gap false ++ left) := by
          rw [← List.replicate_succ']
          rfl
    rw [same]

theorem gap_chain (saved : Bool) (left tail : List Bool) (gap : Nat) :
    (gapTrace saved left gap tail).IsChain (fun before after => TM0.step machine before = some after) := by
  induction gap generalizing left with
  | zero => exact .singleton _
  | succ gap ih =>
    apply (ih (false :: left)).cons
    intro next member
    simp only [gap_head,Option.mem_some_iff] at member
    subst next
    simp [TM0.step,state,body_lookup,bodyCode,Tape.mk₂]

def initial (left higher : List Bool) (bit : Bool) (gap : Nat) (tail : List Bool) : MachineState 14 :=
  ⟨0,Tape.mk₂ (false :: left)
    (bit :: (pairs higher ++ true :: false :: (List.replicate gap false ++ true :: tail)))⟩

def selectedLeft (left higher : List Bool) (bit : Bool) : List Bool :=
  (pairs higher).reverse ++ bit :: true :: left

def finish (left higher : List Bool) (bit : Bool) (gap : Nat) (tail : List Bool) : MachineState 14 :=
  state bit 6 (List.replicate gap false ++ false :: true :: selectedLeft left higher bit) (true :: tail)

def prefixTrace (left higher : List Bool) (bit : Bool) (gap : Nat) (tail : List Bool) : List (MachineState 14) :=
  let right := bit :: (pairs higher ++ true :: false :: (List.replicate gap false ++ true :: tail))
  [initial left higher bit gap tail,
   state bit 0 left (false :: right),
   state bit 1 left (true :: right),
   state bit 2 (true :: left) right]

def trace (left higher : List Bool) (bit : Bool) (gap : Nat) (tail : List Bool) : List (MachineState 14) :=
  prefixTrace left higher bit gap tail ++
    fieldTrace bit (bit :: true :: left) higher (List.replicate gap false ++ true :: tail) ++
    [state bit 5 (true :: selectedLeft left higher bit)
      (false :: (List.replicate gap false ++ true :: tail))] ++
    gapTrace bit (false :: true :: selectedLeft left higher bit) gap tail

theorem actual (left higher : List Bool) (bit : Bool) (gap : Nat) (tail : List Bool) (inputLength : Nat) :
    ∃ path, RunsFrom machine (initial left higher bit gap tail) path (finish left higher bit gap tail) ∧
      path.length = 2*higher.length+gap+7 ∧
      ∀ clock, visitedSpace machine inputLength (path.take clock) ≤ inputLength+4*higher.length+2*gap+15 := by
  have leadChain : (prefixTrace left higher bit gap tail ++
      fieldTrace bit (bit :: true :: left) higher (List.replicate gap false ++ true :: tail)).IsChain
      (fun before after => TM0.step machine before = some after) := by
    apply List.IsChain.append
    · cases bit <;> simp [prefixTrace,initial,state,TM0.step,machine,bodyLabel,bodyCode,Tape.mk₂,List.isChain_cons_cons]
    · exact field_chain _ _ _ _
    · intro before beforeLast after afterHead
      simp only [prefixTrace,List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at beforeLast
      simp only [field_head,Option.mem_some_iff] at afterHead
      subst before
      subst after
      simp [TM0.step,state,body_lookup,bodyCode,Tape.mk₂]
  have middleChain : ((prefixTrace left higher bit gap tail ++
      fieldTrace bit (bit :: true :: left) higher (List.replicate gap false ++ true :: tail)) ++
      [state bit 5 (true :: selectedLeft left higher bit)
        (false :: (List.replicate gap false ++ true :: tail))]).IsChain
      (fun before after => TM0.step machine before = some after) := by
    apply List.IsChain.append leadChain (.singleton _)
    intro before beforeLast after afterHead
    simp only [List.getLast?_append,field_last,Option.some_or,Option.mem_some_iff] at beforeLast
    simp only [List.head?_singleton,Option.mem_some_iff] at afterHead
    subst before
    subst after
    simp [TM0.step,state,body_lookup,bodyCode,selectedLeft,Tape.mk₂]
  have chain : (trace left higher bit gap tail).IsChain
      (fun before after => TM0.step machine before = some after) := by
    apply List.IsChain.append middleChain (gap_chain _ _ _ _)
    intro before beforeLast after afterHead
    simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or,Option.mem_some_iff] at beforeLast
    simp only [gap_head,Option.mem_some_iff] at afterHead
    subst before
    subst after
    simp [TM0.step,state,body_lookup,bodyCode,Tape.mk₂]
  have length : (trace left higher bit gap tail).length = 2*higher.length+gap+7 := by
    simp only [trace,List.length_append,prefixTrace,List.length_cons,List.length_nil,field_length,gap_length]
    omega
  refine ⟨trace left higher bit gap tail,⟨rfl,chain,?_,?_⟩,length,?_⟩
  · simp only [trace,List.getLast?_append,gap_last,Option.some_or,finish]
  · simp [finish,state,TM0.step,body_lookup,bodyCode,Tape.mk₂]
  · intro clock
    have space := PSTRTMTrace002.visitedSpace_le machine inputLength ((trace left higher bit gap tail).take clock)
    have short := List.length_take_le' clock (trace left higher bit gap tail)
    omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit.MarkSeek
