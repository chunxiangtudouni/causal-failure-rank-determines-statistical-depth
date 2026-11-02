module

public import Paid.PDROC_BitVM_Codec_NatWriter_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Codec.NatWriter

open Turing

/-- After scanning, LEFT contains the reversed bare Nat and target is
actually empty. Pop each ACTUAL bit to target, then write the real FALSE
natural-Cell tag. No length, Nat value or host reversal is in this code. -/
def drainProgram (_ : Unit) : ClearStatement :=
  .pop 1 (fun _ symbol => symbol)
    (.branch Option.isSome
      (.push 2 (fun symbol => symbol.getD false) (.goto (fun _ => ())))
      (.push 2 (fun _ => false) .halt))

def drainState (label : Option Unit) (store : Option Bool) (word target : List Bool) : ClearState :=
  ⟨label, store, PDROC.BitVM.Log.TwoStack.threeStacks [] word target⟩

theorem drain_cons (bit : Bool) (word target : List Bool) (store : Option Bool) :
    TM2.step drainProgram (drainState (some ()) store (bit :: word) target) =
      some (drainState (some ()) (some bit) word (bit :: target)) := by
  change (some ⟨some (), some bit, Function.update (Function.update
    (PDROC.BitVM.Log.TwoStack.threeStacks [] (bit :: word) target) 1 word) 2 (bit :: target)⟩ :
      Option ClearState) = _
  rw [PDROC.BitVM.Native.Copy.update_second, PDROC.BitVM.Native.Copy.update_third]
  rfl

theorem drain_nil (target : List Bool) (store : Option Bool) :
    TM2.step drainProgram (drainState (some ()) store [] target) =
      some (drainState none none [] (false :: target)) := by
  change (some ⟨none, none, Function.update (Function.update
    (PDROC.BitVM.Log.TwoStack.threeStacks [] [] target) 1 []) 2 (false :: target)⟩ :
      Option ClearState) = _
  rw [PDROC.BitVM.Native.Copy.update_second, PDROC.BitVM.Native.Copy.update_third]
  rfl

def drainTrace : List Bool → List Bool → Option Bool → List ClearState
  | [], target, store => [drainState (some ()) store [] target, drainState none none [] (false :: target)]
  | bit :: word, target, store => drainState (some ()) store (bit :: word) target ::
      drainTrace word (bit :: target) (some bit)

theorem drain_head (word target : List Bool) (store : Option Bool) :
    (drainTrace word target store).head? = some (drainState (some ()) store word target) := by
  cases word <;> rfl

theorem drain_last (word target : List Bool) (store : Option Bool) :
    (drainTrace word target store).getLast? =
      some (drainState none none [] (false :: (word.reverse ++ target))) := by
  induction word generalizing target store with
  | nil => rfl
  | cons bit word ih =>
    rw [drainTrace, List.getLast?_cons, ih]
    simp only [Option.getD_some, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem drain_length (word target : List Bool) (store : Option Bool) :
    (drainTrace word target store).length = word.length + 2 := by
  induction word generalizing target store with
  | nil => rfl
  | cons bit word ih => simp only [drainTrace, List.length_cons, ih]

theorem drain_chain (word target : List Bool) (store : Option Bool) :
    (drainTrace word target store).IsChain (fun a b => TM2.step drainProgram a = some b) := by
  induction word generalizing target store with
  | nil => exact List.isChain_cons_cons.mpr ⟨drain_nil target store, List.isChain_singleton _⟩
  | cons bit word ih =>
    apply List.IsChain.cons (ih (bit :: target) (some bit))
    intro after member
    rw [drain_head] at member
    have same : after = drainState (some ()) (some bit) word (bit :: target) :=
      (Option.mem_some_iff.mp member).symm
    subst after
    exact drain_cons bit word target store

def headerRoles : PDROC.BitVM.Log.Header.Stack ↪ Stack :=
  ⟨fun role => if role = 0 then 0 else if role = 1 then 2 else 1, by
    intro left right equal
    fin_cases left <;> fin_cases right <;> simp_all⟩

abbrev Label := Fin 10
abbrev Store := Option Bool × Unit
abbrev State := TM2.Cfg Alphabet Label Store
abbrev Statement := TM2.Stmt Alphabet Label Store

def headerLabels (label : PDROC.BitVM.Log.Header.Label) : Label := ⟨3 + label.val, by omega⟩

/-- The target is first REALLY cleared and temporarily holds the actual
width ticks. Header payload reads really consume all of those ticks. The
native LEFT then holds the reversed full Nat word, so no fourth role is
needed even when all seven Rat-phase temporary registers are live. -/
def program (label : Label) : Statement :=
  if label = 0 then PDROC.BitVM.Native.Inline.statement (fun _ : Unit => 0) 1
    (PDROC.BitVM.Kernel.NatResult.program ())
  else if label = 1 then PDROC.BitVM.Native.Inline.statement (fun _ : Unit => 1) 2 (clearProgram 1 ())
  else if label = 2 then PDROC.BitVM.Native.Inline.statement (fun _ : Unit => 2) 3 (clearProgram 2 ())
  else if small : label.val < 7 then PDROC.BitVM.Native.Inline.statement headerLabels 7
    (PDROC.BitVM.Native.Lift.statement headerRoles
      (PDROC.BitVM.Log.Header.program ⟨label.val - 3, by omega⟩))
  else if label = 7 then PDROC.BitVM.Native.Inline.statement (fun _ : Unit => 7) 8 (clearProgram 0 ())
  else if label = 8 then PDROC.BitVM.Native.Inline.statement (fun _ : Unit => 8) 9 (drainProgram ())
  else .halt

theorem materialize_agrees (label : Unit) : program 0 =
    PDROC.BitVM.Native.Inline.statement (fun _ : Unit => 0) 1
      (PDROC.BitVM.Kernel.NatResult.program label) := by
  cases label
  rfl

theorem left_agrees (label : Unit) : program 1 =
    PDROC.BitVM.Native.Inline.statement (fun _ : Unit => 1) 2 (clearProgram 1 label) := by
  cases label
  rfl

theorem target_agrees (label : Unit) : program 2 =
    PDROC.BitVM.Native.Inline.statement (fun _ : Unit => 2) 3 (clearProgram 2 label) := by
  cases label
  rfl

theorem header_agrees (label : PDROC.BitVM.Log.Header.Label) : program (headerLabels label) =
    PDROC.BitVM.Native.Inline.statement headerLabels 7
      (PDROC.BitVM.Native.Lift.machine headerRoles PDROC.BitVM.Log.Header.program label) := by
  fin_cases label <;> rfl

theorem right_agrees (label : Unit) : program 7 =
    PDROC.BitVM.Native.Inline.statement (fun _ : Unit => 7) 8 (clearProgram 0 label) := by
  cases label
  rfl

theorem drain_agrees (label : Unit) : program 8 =
    PDROC.BitVM.Native.Inline.statement (fun _ : Unit => 8) 9 (drainProgram label) := by
  cases label
  rfl

end PDROC.BitVM.Codec.NatWriter
