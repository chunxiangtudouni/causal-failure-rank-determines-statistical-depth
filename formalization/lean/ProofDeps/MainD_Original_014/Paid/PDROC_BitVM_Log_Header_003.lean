module

public import Paid.PDROC_BitVM_Log_Header_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Log.Header

open Turing

/-- The payload is consumed by actual Bool ticks, including false data bits. -/
def payloadTrace : List Bool → List Bool → List Bool → Store → List State
  | [], suffix, archive, store =>
      [state (some 1) store suffix [] archive, state (some 2) none suffix [] archive]
  | bit :: digits, suffix, archive, store =>
      state (some 1) store ((bit :: digits) ++ suffix)
        (List.replicate (bit :: digits).length true) archive ::
      payloadTrace digits suffix (bit :: archive) (some bit)

theorem payloadTrace_head (digits suffix archive : List Bool) (store : Store) :
    (payloadTrace digits suffix archive store).head? =
      some (state (some 1) store (digits ++ suffix) (List.replicate digits.length true) archive) := by
  cases digits <;> rfl

theorem payloadTrace_last (digits suffix archive : List Bool) (store : Store) :
    (payloadTrace digits suffix archive store).getLast? =
      some (state (some 2) none suffix [] (digits.reverse ++ archive)) := by
  induction digits generalizing archive store with
  | nil => rfl
  | cons bit digits ih =>
    rw [payloadTrace, List.getLast?_cons, ih]
    simp only [Option.getD_some, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem payloadTrace_length (digits suffix archive : List Bool) (store : Store) :
    (payloadTrace digits suffix archive store).length = digits.length + 2 := by
  induction digits generalizing archive store with
  | nil => rfl
  | cons bit digits ih => simp only [payloadTrace, List.length_cons, ih]

theorem payloadTrace_chain (digits suffix archive : List Bool) (store : Store) :
    (payloadTrace digits suffix archive store).IsChain
      (fun before after => TM2.step program before = some after) := by
  induction digits generalizing archive store with
  | nil =>
    apply List.isChain_cons_cons.mpr
    exact ⟨payload_done suffix archive store, List.isChain_singleton _⟩
  | cons bit digits ih =>
    change (_ :: payloadTrace digits suffix (bit :: archive) (some bit)).IsChain _
    apply List.IsChain.cons (ih (bit :: archive) (some bit))
    intro after member
    rw [payloadTrace_head] at member
    have equal := Option.mem_some_iff.mp member
    subst after
    exact payload_bit bit (digits ++ suffix) (List.replicate digits.length true) archive store

end PDROC.BitVM.Log.Header
