module

public import Paid.PDROC_BitVM_Codec_Output_List_002
public import Paid.PDROC_BitVM_Native_Frame_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Codec.OutputList

open Turing PDROC.BitVM.Log.TwoStack

variable {K : Type*} [DecidableEq K]

/-- Reuse the genuine reverse-copy on ANY fixed embedding of its three
data roles. Unselected caller stacks, including the actual unary count,
are preserved. The before state is a physical source configuration. -/
theorem copyReverse_work_runs (embed : Stack ↪ K)
    (before : TM2.Cfg (fun _ : K => Bool) Label Store) (word target : List Bool)
    (entry : PDROC.BitVM.Native.Lift.cfg embed before =
      copyState (some 0) none word target []) :
    ∃ (run : List (TM2.Cfg (fun _ : K => Bool) Label Store))
      (final : TM2.Cfg (fun _ : K => Bool) Label Store),
      run.head? = some before ∧
      run.IsChain (fun a b => TM2.step (PDROC.BitVM.Native.Lift.machine embed copyReverseProgram)
        a = some b) ∧
      run.getLast? = some final ∧
      TM2.step (PDROC.BitVM.Native.Lift.machine embed copyReverseProgram) final = none ∧
      PDROC.BitVM.Native.Lift.cfg embed final =
        copyState none none word (word.reverse ++ target) [] ∧
      run.length = 2 * word.length + 3 ∧
      ∀ other, (∀ role, other ≠ embed role) → final.stk other = before.stk other := by
  obtain ⟨source, first, chain, last, halt, size, _sourceWord, _output, _scratch⟩ :=
    copyReverse_runs word target
  cases source with
  | nil => simp only [List.head?_nil, reduceCtorEq] at first
  | cons start rest =>
    have same : start = copyState (some 0) none word target [] := Option.some.inj first
    subst start
    obtain ⟨posts, final, length, actual, finalLast, represented, frame⟩ :=
      PDROC.BitVM.Native.Lift.path embed copyReverseProgram before
        (copyState (some 0) none word target [])
        (copyState none none word (word.reverse ++ target) []) rest entry chain last
    refine ⟨before :: posts, final, rfl, actual, finalLast, ?_, represented, ?_, frame⟩
    · apply PDROC.BitVM.Native.Lift.halt_project embed copyReverseProgram final
      rw [represented]
      exact halt
    · simp only [List.length_cons, length] at size ⊢
      exact size

end PDROC.BitVM.Codec.OutputList
