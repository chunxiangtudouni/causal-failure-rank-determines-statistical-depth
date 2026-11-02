module

public import Paid.PDROC_BitVM_Native_CopyRun_011

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Codec.OutputList

open Turing PDROC.BitVM.Log.TwoStack

def copyState (label : Option Label) (store : Store) (source target scratch : List Bool) : State :=
  PDROC.BitVM.Native.Copy.state label store source target scratch

/-- Real first pass: every source pop pushes the actual Bool to BOTH
scratch and reverse output. Store is only Option Bool, never a word/Nat. -/
def copyReverseFirst : Statement :=
  .pop 0 (fun _ symbol => symbol)
    (.branch Option.isSome
      (.push 2 (fun symbol => symbol.getD false)
        (.push 1 (fun symbol => symbol.getD false) (.goto (fun _ => 0))))
      (.goto (fun _ => 1)))

/-- The second pass restores the source from reversed scratch and leaves
the already reversed output alone. This is a fixed finite program. -/
def copyReverseProgram (label : Label) : Statement :=
  if label = 0 then copyReverseFirst else if label = 1 then drain 2 0 1 .halt else .halt

theorem copyReverse_cons (bit : Bool) (rest target scratch : List Bool) (store : Store) :
    TM2.step copyReverseProgram (copyState (some 0) store (bit :: rest) target scratch) =
      some (copyState (some 0) (some bit) rest (bit :: target) (bit :: scratch)) := by
  change (some ⟨some 0, some bit,
    Function.update (Function.update (Function.update (threeStacks (bit :: rest) target scratch)
      0 rest) 2 (bit :: scratch)) 1 (bit :: target)⟩ : Option State) = _
  rw [PDROC.BitVM.Native.Copy.update_first, PDROC.BitVM.Native.Copy.update_third,
    PDROC.BitVM.Native.Copy.update_second]
  rfl

theorem copyReverse_nil (target scratch : List Bool) (store : Store) :
    TM2.step copyReverseProgram (copyState (some 0) store [] target scratch) =
      some (copyState (some 1) none [] target scratch) := by
  change (some ⟨some 1, none, Function.update (threeStacks [] target scratch) 0 []⟩ : Option State) = _
  rw [PDROC.BitVM.Native.Copy.update_first]
  rfl

def copyReverseFirstTrace : List Bool → List Bool → List Bool → Store → List State
  | [], target, scratch, store =>
      [copyState (some 0) store [] target scratch, copyState (some 1) none [] target scratch]
  | bit :: rest, target, scratch, store =>
      copyState (some 0) store (bit :: rest) target scratch ::
        copyReverseFirstTrace rest (bit :: target) (bit :: scratch) (some bit)

theorem copyReverseFirst_head (word target scratch : List Bool) (store : Store) :
    (copyReverseFirstTrace word target scratch store).head? =
      some (copyState (some 0) store word target scratch) := by
  cases word <;> rfl

theorem copyReverseFirst_last (word target scratch : List Bool) (store : Store) :
    (copyReverseFirstTrace word target scratch store).getLast? =
      some (copyState (some 1) none [] (word.reverse ++ target) (word.reverse ++ scratch)) := by
  induction word generalizing target scratch store with
  | nil => rfl
  | cons bit rest ih =>
    rw [copyReverseFirstTrace, List.getLast?_cons, ih]
    simp only [Option.getD_some, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem copyReverseFirst_length (word target scratch : List Bool) (store : Store) :
    (copyReverseFirstTrace word target scratch store).length = word.length + 2 := by
  induction word generalizing target scratch store with
  | nil => rfl
  | cons bit rest ih => simp only [copyReverseFirstTrace, List.length_cons, ih]

theorem copyReverseFirst_chain (word target scratch : List Bool) (store : Store) :
    (copyReverseFirstTrace word target scratch store).IsChain
      (fun before after => TM2.step copyReverseProgram before = some after) := by
  induction word generalizing target scratch store with
  | nil =>
    exact List.isChain_cons_cons.mpr ⟨copyReverse_nil target scratch store, List.isChain_singleton _⟩
  | cons bit rest ih =>
    apply List.IsChain.cons (ih (bit :: target) (bit :: scratch) (some bit))
    intro after member
    rw [copyReverseFirst_head] at member
    have equal : after = copyState (some 0) (some bit) rest (bit :: target) (bit :: scratch) :=
      (Option.mem_some_iff.mp member).symm
    subst after
    exact copyReverse_cons bit rest target scratch store

theorem copyReverse_supports : TM2.Supports copyReverseProgram (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    fin_cases label <;> simp [copyReverseProgram, copyReverseFirst, drain, TM2.SupportsStmt]

end PDROC.BitVM.Codec.OutputList
