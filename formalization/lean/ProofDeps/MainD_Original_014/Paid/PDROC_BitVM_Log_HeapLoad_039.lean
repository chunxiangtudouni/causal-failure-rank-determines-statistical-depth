module

public import Paid.PDROC_BitVM_Log_HeapLoad_038

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2300000

@[expose] public section

namespace PDROC.BitVM.Log.HeapLoad

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal

/-! Real failed load routes. A wrong pointer type and a missing/tombstoned
address reach the actual invalid label; neither commits a destination Cell.
In particular pure heap Nat0 default is not returned as a live value. -/

def rationalResult (store : Store) := HeapPointer.setTyped (HeapPointer.saveTag (cleared store) (some true)) false

theorem source_rational_runs (pointer destination : Register) (value : ℚ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.rational value)) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (sourceProgram pointer destination) after = none ∧
      after.l = none ∧ after.var = (rationalResult store, ()) ∧ after.stk = (preCleared 6 contents) ∧
      run.length ≤ clearBudget contents + 5 := by
  obtain ⟨readyTrace, readyHead, readyChain, readyLast, readyLength⟩ := rational_ready pointer destination value contents store register
  let beforeBranch : SourceState := ⟨some typeBranch, (rationalResult store, ()), (preCleared 6 contents)⟩
  let invalid : SourceState := ⟨some invalidLabel, (rationalResult store, ()), (preCleared 6 contents)⟩
  let final : SourceState := ⟨none, (rationalResult store, ()), (preCleared 6 contents)⟩
  let tailTrace := [beforeBranch, invalid, final]
  have tailHead : tailTrace.head? = some beforeBranch := rfl
  have tailChain : tailTrace.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) := by
    apply List.isChain_cons_cons.mpr
    refine ⟨type_invalid pointer destination (rationalResult store, ()) ((preCleared 6 contents)) rfl, ?_⟩
    exact List.isChain_cons_cons.mpr ⟨invalid_halt pointer destination (rationalResult store, ()) ((preCleared 6 contents)), List.isChain_singleton _⟩
  let run := readyTrace ++ tailTrace.tail
  have head : run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [run, List.head?_append, readyHead, Option.some_or]
  have chain : run.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) :=
    TwoStack.join_chain readyTrace tailTrace beforeBranch readyChain tailChain readyLast tailHead
  have last : run.getLast? = some final := by
    simp only [run, tailTrace, List.tail_cons, List.getLast?_append, List.getLast?_cons_cons,
      List.getLast?_singleton, Option.some_or]
  refine ⟨run, final, head, chain, last, rfl, rfl, rfl, rfl, ?_⟩
  simp only [run, tailTrace, List.tail_cons, List.length_append, List.length_cons, List.length_nil]
  omega

theorem source_missing_runs (pointer destination : Register) (events : List HeapEvent) (query : ℕ)
    (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural query))
    (history : contents 21 = encodeHistory events) (missing : lookup events query = none) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (sourceProgram pointer destination) after = none ∧
      after.l = none ∧ Query.equality after.var.1.2.1 = false ∧
      after.stk = looked events query contents ∧ run.length ≤ queryBudget events query contents + 2 := by
  obtain ⟨readyTrace, vars, readyHead, readyChain, readyLast, saved, flag, readyLength⟩ :=
    queried_runs pointer destination events query contents store register history
  have actualMissing : (Query.equality vars.2.1 && Query.recordTag vars.2.1) = false := by
    simpa only [missing, Option.isSome_none] using flag
  let boundary : SourceState := ⟨some valueBranch, (vars, ()), looked events query contents⟩
  let invalid : SourceState := ⟨some invalidLabel, (vars, ()), looked events query contents⟩
  let final : SourceState := ⟨none, (HeapPointer.setTyped vars false, ()), looked events query contents⟩
  let tailTrace := [boundary, invalid, final]
  have tailHead : tailTrace.head? = some boundary := rfl
  have tailChain : tailTrace.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) := by
    apply List.isChain_cons_cons.mpr
    refine ⟨value_invalid pointer destination (vars, ()) (looked events query contents) actualMissing, ?_⟩
    exact List.isChain_cons_cons.mpr ⟨invalid_halt pointer destination (vars, ()) (looked events query contents),
      List.isChain_singleton _⟩
  let run := readyTrace ++ tailTrace.tail
  have head : run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [run, List.head?_append, readyHead, Option.some_or]
  have chain : run.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) :=
    TwoStack.join_chain readyTrace tailTrace boundary readyChain tailChain readyLast tailHead
  have last : run.getLast? = some final := by
    simp only [run, tailTrace, List.tail_cons, List.getLast?_append, List.getLast?_cons_cons,
      List.getLast?_singleton, Option.some_or]
  refine ⟨run, final, head, chain, last, rfl, rfl, rfl, rfl, ?_⟩
  simp only [run, tailTrace, List.tail_cons, List.length_append, List.length_cons, List.length_nil]
  omega

end PDROC.BitVM.Log.HeapLoad
