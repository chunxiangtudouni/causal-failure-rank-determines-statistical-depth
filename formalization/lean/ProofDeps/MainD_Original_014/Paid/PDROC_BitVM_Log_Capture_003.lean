module

public import Paid.PDROC_BitVM_Log_Capture_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Log.Capture

open Turing

theorem record_replace (store : Store) (first second : Option Bool) :
    Query.setRecord (Query.setRecord store first) second = Query.setRecord store second := rfl

def headerTrace (other : Stack → List Bool) :
    ℕ → List Bool → List Bool → List Bool → List Bool → Store → List State
  | 0, input, ticks, archive, captured, store =>
      [state (some 0) store (false :: input) ticks archive captured other,
       state (some 1) (Query.setRecord store (some false)) input ticks
         (false :: archive) (false :: captured) other]
  | width + 1, input, ticks, archive, captured, store =>
      state (some 0) store (true :: (List.replicate width true ++ false :: input))
        ticks archive captured other ::
      headerTrace other width input (true :: ticks) (true :: archive) (true :: captured)
        (Query.setRecord store (some true))

theorem headerTrace_head (width : ℕ) (input ticks archive captured : List Bool)
    (other : Stack → List Bool) (store : Store) :
    (headerTrace other width input ticks archive captured store).head? =
      some (state (some 0) store (List.replicate width true ++ false :: input)
        ticks archive captured other) := by
  cases width <;> rfl

theorem headerTrace_last (width : ℕ) (input ticks archive captured : List Bool)
    (other : Stack → List Bool) (store : Store) :
    (headerTrace other width input ticks archive captured store).getLast? =
      some (state (some 1) (Query.setRecord store (some false)) input
        (List.replicate width true ++ ticks)
        (false :: (List.replicate width true ++ archive))
        (false :: (List.replicate width true ++ captured)) other) := by
  induction width generalizing ticks archive captured store with
  | zero => rfl
  | succ width ih =>
    rw [headerTrace, List.getLast?_cons, ih]
    simp only [Option.getD_some, List.replicate_succ', List.append_assoc,
      List.singleton_append, record_replace]

theorem headerTrace_length (width : ℕ) (input ticks archive captured : List Bool)
    (other : Stack → List Bool) (store : Store) :
    (headerTrace other width input ticks archive captured store).length = width + 2 := by
  induction width generalizing ticks archive captured store with
  | zero => rfl
  | succ width ih => simp only [headerTrace, List.length_cons, ih]

theorem headerTrace_chain (width : ℕ) (input ticks archive captured : List Bool)
    (other : Stack → List Bool) (store : Store) :
    (headerTrace other width input ticks archive captured store).IsChain
      (fun before after => TM2.step program before = some after) := by
  induction width generalizing ticks archive captured store with
  | zero =>
    apply List.isChain_cons_cons.mpr
    exact ⟨header_false input ticks archive captured other store, List.isChain_singleton _⟩
  | succ width ih =>
    change (_ :: headerTrace other width input (true :: ticks) (true :: archive) (true :: captured)
      (Query.setRecord store (some true))).IsChain _
    apply List.IsChain.cons (ih (true :: ticks) (true :: archive) (true :: captured) _)
    intro after member
    rw [headerTrace_head] at member
    have equal := Option.mem_some_iff.mp member
    subst after
    exact header_true (List.replicate width true ++ false :: input) ticks archive captured other store

end PDROC.BitVM.Log.Capture
