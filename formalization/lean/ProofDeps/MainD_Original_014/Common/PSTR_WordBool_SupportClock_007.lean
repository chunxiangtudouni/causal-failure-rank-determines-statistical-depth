module

public import Common.PSTR_WordBool_NativeTrace_006
public import Mathlib.Data.Finset.Lattice.Fold

/-! A fixed finite source support supplies a fixed native clock constant.
The support and code are chosen before input; no runtime state/size oracle
is introduced. This compiler theorem still needs an actual source trace. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.SupportClock

open Turing

variable {Λ σ : Type*} [Inhabited Λ] [Inhabited σ]

def clock (machine : Λ → TM1.Stmt Bool Λ σ) (support : Finset Λ) : Nat :=
  support.sup (fun label => StatementClock.weight (machine label)) + 1

theorem trace_supported (machine : Λ → TM1.Stmt Bool Λ σ) (support : Finset Λ)
    (closed : TM1.Supports machine support) (input : List Bool)
    (trace : List (TM1.Cfg Bool Λ σ))
    (first : trace.head? = some (TM1.init input))
    (chain : trace.IsChain (fun before after => TM1.step machine before = some after)) :
    ∀ state ∈ trace, state.l ∈ Finset.insertNone support := by
  apply chain.induction (fun state => state.l ∈ Finset.insertNone support) trace
  · intro before after edge present
    exact TM1.step_supports machine closed edge present
  · intro nonempty
    have head : trace.head nonempty = TM1.init input := by
      exact Option.some.inj ((List.head?_eq_some_head nonempty).symm.trans first)
    rw [head]
    exact Finset.some_mem_insertNone.mpr closed.1

theorem trace_weights (machine : Λ → TM1.Stmt Bool Λ σ) (support : Finset Λ)
    (closed : TM1.Supports machine support) (input : List Bool)
    (trace : List (TM1.Cfg Bool Λ σ))
    (first : trace.head? = some (TM1.init input))
    (chain : trace.IsChain (fun before after => TM1.step machine before = some after)) :
    ∀ state ∈ trace, ∀ label, state.l = some label →
      StatementClock.weight (machine label) ≤ clock machine support := by
  intro state present label equal
  have supported := trace_supported machine support closed input trace first chain state present
  rw [equal] at supported
  exact (Finset.le_sup (f := fun label => StatementClock.weight (machine label))
    (Finset.some_mem_insertNone.mp supported)).trans (Nat.le_succ _)

theorem actual_native_trace (machine : Λ → TM1.Stmt Bool Λ σ) (support : Finset Λ)
    (closed : TM1.Supports machine support) (input : List Bool)
    (trace : List (TM1.Cfg Bool Λ σ)) (final : TM1.Cfg Bool Λ σ)
    (first : trace.head? = some (TM1.init input))
    (chain : trace.IsChain (fun before after => TM1.step machine before = some after))
    (last : trace.getLast? = some final) (halt : TM1.step machine final = none) :
    ∃ nativeTrace : List (TM0.Cfg Bool (TM1to0.Λ' machine)),
      nativeTrace.head? = some (TM0.init input) ∧
      nativeTrace.IsChain (fun before after => TM0.step (TM1to0.tr machine) before = some after) ∧
      nativeTrace.getLast? = some (TM1to0.trCfg machine final) ∧
      TM0.step (TM1to0.tr machine) (TM1to0.trCfg machine final) = none ∧
      nativeTrace.length ≤ clock machine support * trace.length + 1 := by
  have weights := trace_weights machine support closed input trace first chain
  cases trace with
  | nil => simp at first
  | cons start rest =>
    have initial : start = TM1.init input := Option.some.inj first
    obtain ⟨posts, bound, nativeChain, nativeLast⟩ :=
      NativeTrace.compile_path machine (clock machine support) start final rest chain last weights
    refine ⟨TM1to0.trCfg machine start :: posts, ?_, nativeChain, nativeLast, ?_, ?_⟩
    · rw [initial]
      rfl
    · cases final with
      | mk label store tape =>
        cases label with
        | none => rfl
        | some label => cases halt
    · simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

end PaperProofs.Common.Native.PSTRWordBool.SupportClock
