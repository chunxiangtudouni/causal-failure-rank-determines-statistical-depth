module

public import Paid.PDROC_BitVM_Log_Capture_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Log.Capture

open Turing

def payloadTrace (other : Stack → List Bool) :
    List Bool → List Bool → List Bool → List Bool → Store → List State
  | [], suffix, archive, captured, store =>
      [state (some 1) store suffix [] archive captured other,
       state (some 2) (Query.setRecord store none) suffix [] archive captured other]
  | bit :: digits, suffix, archive, captured, store =>
      state (some 1) store ((bit :: digits) ++ suffix)
        (List.replicate (bit :: digits).length true) archive captured other ::
      payloadTrace other digits suffix (bit :: archive) (bit :: captured)
        (Query.setRecord store (some bit))

theorem payloadTrace_head (digits suffix archive captured : List Bool)
    (other : Stack → List Bool) (store : Store) :
    (payloadTrace other digits suffix archive captured store).head? =
      some (state (some 1) store (digits ++ suffix) (List.replicate digits.length true)
        archive captured other) := by
  cases digits <;> rfl

theorem payloadTrace_last (digits suffix archive captured : List Bool)
    (other : Stack → List Bool) (store : Store) :
    (payloadTrace other digits suffix archive captured store).getLast? =
      some (state (some 2) (Query.setRecord store none) suffix []
        (digits.reverse ++ archive) (digits.reverse ++ captured) other) := by
  induction digits generalizing archive captured store with
  | nil => rfl
  | cons bit digits ih =>
    rw [payloadTrace, List.getLast?_cons, ih]
    simp only [Option.getD_some, List.reverse_cons, List.append_assoc,
      List.singleton_append, record_replace]

theorem payloadTrace_length (digits suffix archive captured : List Bool)
    (other : Stack → List Bool) (store : Store) :
    (payloadTrace other digits suffix archive captured store).length = digits.length + 2 := by
  induction digits generalizing archive captured store with
  | nil => rfl
  | cons bit digits ih => simp only [payloadTrace, List.length_cons, ih]

theorem payloadTrace_chain (digits suffix archive captured : List Bool)
    (other : Stack → List Bool) (store : Store) :
    (payloadTrace other digits suffix archive captured store).IsChain
      (fun before after => TM2.step program before = some after) := by
  induction digits generalizing archive captured store with
  | nil =>
    apply List.isChain_cons_cons.mpr
    exact ⟨payload_done suffix archive captured other store, List.isChain_singleton _⟩
  | cons bit digits ih =>
    change (_ :: payloadTrace other digits suffix (bit :: archive) (bit :: captured)
      (Query.setRecord store (some bit))).IsChain _
    apply List.IsChain.cons (ih (bit :: archive) (bit :: captured) _)
    intro after member
    rw [payloadTrace_head] at member
    have equal := Option.mem_some_iff.mp member
    subst after
    exact payload_bit bit (digits ++ suffix) (List.replicate digits.length true) archive captured other store

end PDROC.BitVM.Log.Capture
