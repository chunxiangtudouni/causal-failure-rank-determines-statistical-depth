module

public import Paid.PDROC_BitVM_Log_Header_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Log.Header

open Turing

/-- Width indexes this proof witness only; `program` has no width parameter. -/
def headerTrace : ℕ → List Bool → List Bool → List Bool → Store → List State
  | 0, input, ticks, archive, store =>
      [state (some 0) store (false :: input) ticks archive,
       state (some 1) (some false) input ticks (false :: archive)]
  | width + 1, input, ticks, archive, store =>
      state (some 0) store (true :: (List.replicate width true ++ false :: input)) ticks archive ::
        headerTrace width input (true :: ticks) (true :: archive) (some true)

theorem headerTrace_head (width : ℕ) (input ticks archive : List Bool) (store : Store) :
    (headerTrace width input ticks archive store).head? =
      some (state (some 0) store (List.replicate width true ++ false :: input) ticks archive) := by
  cases width <;> rfl

theorem headerTrace_last (width : ℕ) (input ticks archive : List Bool) (store : Store) :
    (headerTrace width input ticks archive store).getLast? =
      some (state (some 1) (some false) input
        (List.replicate width true ++ ticks) (false :: (List.replicate width true ++ archive))) := by
  induction width generalizing ticks archive store with
  | zero => rfl
  | succ width ih =>
    rw [headerTrace, List.getLast?_cons, ih]
    simp only [Option.getD_some, List.replicate_succ', List.append_assoc, List.singleton_append]

theorem headerTrace_length (width : ℕ) (input ticks archive : List Bool) (store : Store) :
    (headerTrace width input ticks archive store).length = width + 2 := by
  induction width generalizing ticks archive store with
  | zero => rfl
  | succ width ih => simp only [headerTrace, List.length_cons, ih]

theorem headerTrace_chain (width : ℕ) (input ticks archive : List Bool) (store : Store) :
    (headerTrace width input ticks archive store).IsChain
      (fun before after => TM2.step program before = some after) := by
  induction width generalizing ticks archive store with
  | zero =>
    apply List.isChain_cons_cons.mpr
    exact ⟨header_false input ticks archive store, List.isChain_singleton _⟩
  | succ width ih =>
    change (_ :: headerTrace width input (true :: ticks) (true :: archive) (some true)).IsChain _
    apply List.IsChain.cons (ih (true :: ticks) (true :: archive) (some true))
    intro after member
    rw [headerTrace_head] at member
    have equal := Option.mem_some_iff.mp member
    subst after
    exact header_true (List.replicate width true ++ false :: input) ticks archive store

end PDROC.BitVM.Log.Header
