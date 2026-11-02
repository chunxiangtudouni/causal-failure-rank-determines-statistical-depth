module

public import Paid.PDROC_BitVM_Common_Trace_001
public import Common.PSTR_WordBool_AuxWorkspace_020

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace PDROC.BitVM.Common

open Turing
open PaperProofs.Common.Native.PSTRWordBool

variable {K Λ σ : Type*} [DecidableEq K] [Inhabited Λ] [Inhabited σ]

abbrev BoolSourceState (K Λ σ : Type*) := TM2.Cfg (fun _ : K => Bool) Λ σ

/-- The allowance is fixed by code and closed finite label support before
all runtime input. Widths, addresses and counters remain Bool stack data. -/
def sourcePushCap (machine : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (support : Finset Λ) : ℕ :=
  support.sup (fun label => AuxWorkspace.pushes (machine label))

omit [Inhabited σ] in
theorem source_step_occupancy (machine : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (support : Finset Λ) (closed : TM2.Supports machine support)
    (before after : BoolSourceState K Λ σ) (bound : ℕ)
    (supported : before.l ∈ Finset.insertNone support)
    (bounded : ∀ k, (before.stk k).length ≤ bound)
    (actual : TM2.step machine before = some after) :
    after.l ∈ Finset.insertNone support ∧
      ∀ k, (after.stk k).length ≤ bound + sourcePushCap machine support := by
  refine ⟨TM2.step_supports machine closed actual supported, ?_⟩
  cases before with
  | mk label store slots =>
    cases label with
    | none => cases actual
    | some label =>
      have labelInside : label ∈ support := Finset.some_mem_insertNone.mp supported
      have endpoint : TM2.stepAux (machine label) store slots = after := Option.some.inj actual
      have fixed : AuxWorkspace.pushes (machine label) ≤ sourcePushCap machine support :=
        Finset.le_sup (f := fun q => AuxWorkspace.pushes (machine q)) labelInside
      intro k
      rw [← endpoint]
      exact (AuxWorkspace.endpoint_bound (machine label) store slots bound bounded k).trans
        (Nat.add_le_add_left fixed bound)

omit [Inhabited σ] in
/-- Coarse D27-only bound along the SAME actual source path. This is a
proof about stack lengths, not a clock, a finite compiler, or a new runtime
workspace input. The final finite compiler separately fixes finite σ. -/
theorem source_path_occupancy (machine : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (support : Finset Λ) (closed : TM2.Supports machine support)
    (start : BoolSourceState K Λ σ) (rest : List (BoolSourceState K Λ σ)) (bound : ℕ)
    (supported : start.l ∈ Finset.insertNone support)
    (bounded : ∀ k, (start.stk k).length ≤ bound)
    (chain : (start :: rest).IsChain (fun before after => TM2.step machine before = some after)) :
    ∀ state ∈ start :: rest, state.l ∈ Finset.insertNone support ∧
      ∀ k, (state.stk k).length ≤ bound + sourcePushCap machine support * rest.length := by
  induction rest generalizing start bound with
  | nil =>
    intro state member
    have same := List.mem_singleton.mp member
    subst state
    exact ⟨supported, by simpa only [List.length_nil, Nat.mul_zero, Nat.add_zero] using bounded⟩
  | cons next rest ih =>
    obtain ⟨edge, laterChain⟩ := List.isChain_cons_cons.mp chain
    have nextBound := source_step_occupancy machine support closed start next bound supported bounded edge
    have later := ih next (bound + sourcePushCap machine support) nextBound.1 nextBound.2 laterChain
    intro state member
    rcases List.mem_cons.mp member with same | remaining
    · subst state
      exact ⟨supported, fun k => (bounded k).trans (by omega)⟩
    · have info := later state remaining
      refine ⟨info.1, ?_⟩
      intro k
      simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using info.2 k

/-- A genuine source run automatically supplies a coarse occupied-stack
envelope I+C*T. C is the fixed source push cap; T is only the length of the
already established source trace, never an input/fuel/answer qualification. -/
theorem source_trace_occupancy (machine : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (support : Finset Λ) (closed : TM2.Supports machine support)
    (inputStack : K) (input : List Bool) (trace : List (BoolSourceState K Λ σ))
    (first : trace.head? = some (TM2.init inputStack input))
    (chain : trace.IsChain (fun before after => TM2.step machine before = some after)) :
    ∀ state ∈ trace, state.l ∈ Finset.insertNone support ∧
      ∀ k, (state.stk k).length ≤ input.length + sourcePushCap machine support * trace.length := by
  cases trace with
  | nil => simp
  | cons start rest =>
    have initial : start = TM2.init inputStack input := Option.some.inj first
    subst start
    have supported : (TM2.init (Γ := fun _ : K => Bool) (Λ := Λ) (σ := σ) inputStack input).l ∈
        Finset.insertNone support := Finset.some_mem_insertNone.mpr closed.1
    have bounded : ∀ k,
        ((TM2.init (Γ := fun _ : K => Bool) (Λ := Λ) (σ := σ) inputStack input).stk k).length ≤ input.length := by
      intro k
      by_cases same : k = inputStack
      · subst k
        simpa only [TM2.init, Function.update_self] using (Nat.le_refl input.length)
      · simp only [TM2.init, Function.update_of_ne same, List.length_nil, Nat.zero_le]
    have info := source_path_occupancy machine support closed (TM2.init inputStack input) rest
      input.length supported bounded chain
    intro state member
    have actual := info state member
    refine ⟨actual.1, ?_⟩
    intro k
    exact (actual.2 k).trans (Nat.add_le_add_left
      (Nat.mul_le_mul_left (sourcePushCap machine support) (by simp)) input.length)

end PDROC.BitVM.Common
