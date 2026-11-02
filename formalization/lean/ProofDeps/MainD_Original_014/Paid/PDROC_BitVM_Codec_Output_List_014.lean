module

public import Paid.PDROC_BitVM_Codec_Output_List_013
public import Paid.PDROC_BitVM_Common_Occupancy_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Codec.OutputList

open Turing PaperProofs.Common.Native.RationalControllerComputation

theorem finite_labels_support {Λ σ : Type*} [Fintype Λ] [Inhabited Λ]
    (machine : Λ → TM2.Stmt (fun _ : EmitStack => Bool) Λ σ) :
    TM2.Supports machine Finset.univ := by
  have every : ∀ code : TM2.Stmt (fun _ : EmitStack => Bool) Λ σ,
      TM2.SupportsStmt Finset.univ code := by
    intro code
    induction code with
    | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
    | branch _ _ _ yes no => exact ⟨yes, no⟩
    | goto _ => exact fun _ => Finset.mem_univ _
    | halt => trivial
  exact ⟨Finset.mem_univ _, fun label _ => every (machine label)⟩

def listInitialBudget (word bytes ticks initialLeft : List Bool) : ℕ :=
  word.length + bytes.length + ticks.length + initialLeft.length

def listCounterBudget (word ticks : List Bool) : ℕ := word.length + 2 + countCost 0 ticks.length

def listWorkBudget (word bytes ticks initialLeft : List Bool) : ℕ :=
  listInitialBudget word bytes ticks initialLeft +
    PDROC.BitVM.Common.sourcePushCap countProgram Finset.univ * listCounterBudget word ticks

/-- Polynomial only in existing physical-data lengths. Both push caps below
are constants of the fixed machines, before all original inputs. -/
def listFinalBudget (word bytes ticks initialLeft : List Bool) : ℕ :=
  initialLeft.length + 2 + listCounterBudget word ticks +
    2 * listWorkBudget word bytes ticks initialLeft + bytes.length +
    4 * (ticks.length + 1) + 20

def listSpaceBudget (word bytes ticks initialLeft : List Bool) : ℕ :=
  listInitialBudget word bytes ticks initialLeft +
    PDROC.BitVM.Common.sourcePushCap finalProgram Finset.univ *
      listFinalBudget word bytes ticks initialLeft

theorem count_initial_bound (word bytes ticks initialLeft : List Bool) (store : CountStore) :
    ∀ role, ((countInitState word bytes.reverse ticks store).stk role).length ≤
      listInitialBudget word bytes ticks initialLeft := by
  intro role
  fin_cases role <;> simp [countInitState, emitSlots, listInitialBudget] <;> omega

theorem final_initial_bound (word bytes ticks initialLeft : List Bool) (store : CountStore) :
    ∀ role, ((finalBefore word bytes ticks initialLeft store).stk role).length ≤
      listInitialBudget word bytes ticks initialLeft := by
  intro role
  fin_cases role <;> simp [finalBefore, PDROC.BitVM.Native.Inline.cfg,
    cleanBefore, emitSlots, listInitialBudget] <;> omega

/-- Complete true finalization, including genuine zero/count preparation,
every native increment, both physical cleanups, the official bare-Nat
scanner, footer, order restoration and actual HALT. Resource bounds are
derived from the SAME selected counter path and SAME complete path.
There is no workspace, count, numeric answer, fuel or padding oracle. -/
theorem final_complete (word bytes ticks initialLeft : List Bool) (store : CountStore) :
    ∃ (run : List FinalState) (after : FinalState),
      run.head? = some (finalBefore word bytes ticks initialLeft store) ∧
      run.IsChain (fun a b => TM2.step finalProgram a = some b) ∧
      run.getLast? = some after ∧ TM2.step finalProgram after = none ∧
      after.stk 0 = encodeNat ticks.length ++ bytes ++ [true] ∧
      after.stk 1 = [] ∧ after.stk 2 = [] ∧ after.stk 3 = [] ∧
      run.length ≤ listFinalBudget word bytes ticks initialLeft ∧
      ∀ state ∈ run, ∀ role, (state.stk role).length ≤ listSpaceBudget word bytes ticks initialLeft := by
  obtain ⟨counter, counted, padding, after, path, counterHead, counterChain, counterLast,
    physical, _counterOutput, _counterTicks, counterSize, halted, finalData, total⟩ :=
    final_build word bytes ticks initialLeft store
  have occupied : ∀ role, (counted.stk role).length ≤ listWorkBudget word bytes ticks initialLeft := by
    have member : counted ∈ counter := by
      have selected : counted ∈ counter.getLast? := by rw [counterLast]; rfl
      obtain ⟨nonempty, same⟩ := List.mem_getLast?_eq_getLast selected
      rw [same]
      exact List.getLast_mem nonempty
    cases counter with
    | nil => simp only [List.head?_nil, reduceCtorEq] at counterHead
    | cons start rest =>
      have same : start = countInitState word bytes.reverse ticks (store.1, none) := Option.some.inj counterHead
      subst start
      have actual := PDROC.BitVM.Common.source_path_occupancy countProgram Finset.univ
        (finite_labels_support countProgram) (countInitState word bytes.reverse ticks (store.1, none))
        rest (listInitialBudget word bytes ticks initialLeft)
        (Finset.some_mem_insertNone.mpr (Finset.mem_univ _))
        (count_initial_bound word bytes ticks initialLeft (store.1, none)) counterChain counted member
      intro role
      have shorter : rest.length ≤ listCounterBudget word ticks := by
        simp only [List.length_cons] at counterSize
        dsimp only [listCounterBudget]
        omega
      exact (actual.2 role).trans (Nat.add_le_add_left
        (Nat.mul_le_mul_left _ shorter) _)
  have leftSize := occupied 2
  have paddingSize : padding.length ≤ listWorkBudget word bytes ticks initialLeft := by
    have rightSize := occupied 0
    rw [physical, List.length_append] at rightSize
    omega
  have width : natBits ticks.length ≤ ticks.length + 1 := by
    unfold natBits
    have log := Nat.log2_le_self ticks.length
    omega
  have size : path.states.length ≤ listFinalBudget word bytes ticks initialLeft := by
    dsimp only [listFinalBudget, listCounterBudget]
    omega
  have stopped : TM2.step finalProgram after = none := by
    rcases after with ⟨label, finiteStore, contents⟩
    change label = none at halted
    subst label
    rfl
  refine ⟨path.states, after, path.first, path.actual, path.last, stopped,
    ?_, ?_, ?_, ?_, size, ?_⟩
  · rw [finalData]
    rfl
  · rw [finalData]
    rfl
  · rw [finalData]
    rfl
  · rw [finalData]
    rfl
  · cases states : path.states with
    | nil =>
      have impossible := path.first
      simp only [states, List.head?_nil, reduceCtorEq] at impossible
    | cons start rest =>
      have first : start = finalBefore word bytes ticks initialLeft store := by
        have first := path.first
        rw [states] at first
        exact Option.some.inj first
      have bounded : ∀ role, (start.stk role).length ≤ listInitialBudget word bytes ticks initialLeft := by
        subst start
        exact final_initial_bound word bytes ticks initialLeft store
      have chain : (start :: rest).IsChain (fun a b => TM2.step finalProgram a = some b) := by
        rw [← states]
        exact path.actual
      have supported : start.l ∈ Finset.insertNone (Finset.univ : Finset FinalLabel) := by
        rw [first]
        exact Finset.some_mem_insertNone.mpr (Finset.mem_univ _)
      have actual := PDROC.BitVM.Common.source_path_occupancy finalProgram Finset.univ
        (finite_labels_support finalProgram) start rest (listInitialBudget word bytes ticks initialLeft)
        supported bounded chain
      intro state member role
      have bound := (actual state member).2 role
      have shorter : rest.length ≤ listFinalBudget word bytes ticks initialLeft := by
        rw [states] at size
        simp only [List.length_cons] at size
        omega
      exact bound.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ shorter) _)

/-- Exact external list encoding, for an arbitrary number of emitted Cells.
The canonical bytes and one TRUE per Cell describe the already-produced
runtime stacks; they are not extra inputs to the original Bool VM. -/
theorem final_cells_runs (word : List Bool) (cells : List PaperProofs.Paid.Computation.Cell)
    (initialLeft : List Bool)
    (store : CountStore) :
    ∃ (run : List FinalState) (after : FinalState),
      run.head? = some (finalBefore word
        (cells.flatMap PaperProofs.Paid.Computation.encodeCellBits)
        (List.replicate cells.length true) initialLeft store) ∧
      run.IsChain (fun a b => TM2.step finalProgram a = some b) ∧
      run.getLast? = some after ∧ TM2.step finalProgram after = none ∧
      after.stk 0 = PaperProofs.Paid.Computation.encodeBits cells ∧
      after.stk 1 = [] ∧ after.stk 2 = [] ∧ after.stk 3 = [] ∧
      run.length ≤ listFinalBudget word
        (cells.flatMap PaperProofs.Paid.Computation.encodeCellBits) (List.replicate cells.length true) initialLeft ∧
      ∀ state ∈ run, ∀ role, (state.stk role).length ≤ listSpaceBudget word
        (cells.flatMap PaperProofs.Paid.Computation.encodeCellBits) (List.replicate cells.length true) initialLeft := by
  simpa only [List.length_replicate, PaperProofs.Paid.Computation.encodeBits,
    PDROC.BitVM.Link.CodecCandidate.encodeNatBits_eq_neutral, List.append_assoc] using
      final_complete word (cells.flatMap PaperProofs.Paid.Computation.encodeCellBits)
        (List.replicate cells.length true) initialLeft store

/-- The event/count invariant comes from the SAME actual emit trace.
Exactly one tick is pushed after the entire Cell copy, for every Cell,
including its zero bits. The number of emitted bytes is not the count. -/
theorem emit_cells_runs (cells : List PaperProofs.Paid.Computation.Cell)
    (cell : PaperProofs.Paid.Computation.Cell) :
    ∃ (run : List EmitState) (after : EmitState),
      run.head? = some (emitBefore (PaperProofs.Paid.Computation.encodeCellBits cell)
        (cells.flatMap PaperProofs.Paid.Computation.encodeCellBits).reverse
        (List.replicate cells.length true)) ∧
      run.IsChain (fun a b => TM2.step emitProgram a = some b) ∧
      run.getLast? = some after ∧ TM2.step emitProgram after = none ∧
      after.stk 0 = PaperProofs.Paid.Computation.encodeCellBits cell ∧
      after.stk 1 = ((cells ++ [cell]).flatMap PaperProofs.Paid.Computation.encodeCellBits).reverse ∧
      after.stk 2 = [] ∧ after.stk 3 = List.replicate (cells ++ [cell]).length true ∧
      run.length = 2 * (PaperProofs.Paid.Computation.encodeCellBits cell).length + 4 := by
  obtain ⟨run, head, actual, last, halt, size, source, output, scratch, ticks⟩ :=
    emit_runs (PaperProofs.Paid.Computation.encodeCellBits cell)
      (cells.flatMap PaperProofs.Paid.Computation.encodeCellBits).reverse
      (List.replicate cells.length true)
  refine ⟨run, _, head, actual, last, halt, source, ?_, scratch, ?_, size⟩
  · rw [output]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.reverse_append]
  · rw [ticks]
    simp [List.replicate_succ]

end PDROC.BitVM.Codec.OutputList
