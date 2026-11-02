module

public import Paid.PDROC_BitVM_Codec_OutputInstruction_001
public import Paid.PDROC_BitVM_Codec_Output_List_015

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Codec.Finalize

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Native

abbrev Stack := OutputInstruction.Stack
abbrev Alphabet := OutputInstruction.Alphabet
abbrev Label := OutputList.FinalLabel
abbrev SourceStore := OutputList.FinalStore
abbrev State := TM2.Cfg Alphabet Label SourceStore
abbrev embedding := OutputInstruction.emitEmbedding

/-- The original fixed18-label finalizer, with only its physical slots
renamed. All count, native increment, header, footer and cleanup code is
the original frozen code. No value, width or list length enters delta. -/
def program := Lift.machine embedding OutputList.finalProgram

/-- Label16 is the original genuine pre-clean entry. The old finalizer
accepts arbitrary CountStore; the extra Unit carries no initialization
condition. CallFamily022 can directly map this actual source entry. -/
def before (contents : Stack → List Bool) (store : SourceStore) : State := ⟨some 16, store, contents⟩

def inputSize (contents : Stack → List Bool) : ℕ :=
  (contents 0).length + (contents 22).length + (contents 23).length + (contents 24).length

def timeBudget (contents : Stack → List Bool) : ℕ :=
  OutputList.listTimeCoefficient * (inputSize contents + 1)^3

theorem supports : TM2.Supports program (Finset.univ : Finset Label) :=
  Lift.supports embedding OutputList.finalProgram Finset.univ (OutputList.finite_labels_support OutputList.finalProgram)

theorem initial_view (cells : List Cell) (contents : Stack → List Bool) (store : SourceStore)
    (outputWord : contents 22 = (cells.flatMap encodeCellBits).reverse)
    (outputTicks : contents 23 = List.replicate cells.length true) :
    Lift.cfg embedding (before contents store) =
      OutputList.finalBefore (contents 0) (cells.flatMap encodeCellBits)
        (List.replicate cells.length true) (contents 24) store.1 := by
  have data : Lift.slots embedding contents = OutputList.emitSlots (contents 0)
      (cells.flatMap encodeCellBits).reverse (contents 24) (List.replicate cells.length true) := by
    funext role
    fin_cases role
    · rfl
    · exact outputWord
    · rfl
    · exact outputTicks
  change (⟨some 16, store, Lift.slots embedding contents⟩ : OutputList.FinalState) = _
  rw [data]
  rfl

theorem initial_budget (cells : List Cell) (contents : Stack → List Bool)
    (outputWord : contents 22 = (cells.flatMap encodeCellBits).reverse)
    (outputTicks : contents 23 = List.replicate cells.length true) :
    OutputList.listInitialBudget (contents 0) (cells.flatMap encodeCellBits)
      (List.replicate cells.length true) (contents 24) = inputSize contents := by
  have bytes := congrArg List.length outputWord
  have ticks := congrArg List.length outputTicks
  simp only [List.length_reverse, List.length_replicate] at bytes ticks
  simp only [OutputList.listInitialBudget, inputSize, List.length_replicate]
  omega

/-- EVERY actual global edge projects to one actual old source edge,
including real HALT. There is no free stage dispatch or head reset. -/
theorem source_clock (a b : State) (actual : TM2.step program a = some b) :
    TM2.step OutputList.finalProgram (Lift.cfg embedding a) = some (Lift.cfg embedding b) := by
  have projected := Lift.step_project embedding OutputList.finalProgram a
  change (TM2.step program a).map (Lift.cfg embedding) =
    TM2.step OutputList.finalProgram (Lift.cfg embedding a) at projected
  rw [actual] at projected
  exact projected.symm

/-- ONE old final_cells_runs trace is selected, then genuinely lifted.
Arbitrary old right/left physical bytes and arbitrary finite source store
are caller carry; exactly the existing ticks determine the count. -/
theorem runs (cells : List Cell) (contents : Stack → List Bool) (store : SourceStore)
    (outputWord : contents 22 = (cells.flatMap encodeCellBits).reverse)
    (outputTicks : contents 23 = List.replicate cells.length true) :
    ∃ (run : List State) (after : State),
      run.head? = some (before contents store) ∧
      run.IsChain (fun a b => TM2.step program a = some b) ∧
      run.getLast? = some after ∧ TM2.step program after = none ∧ after.l = none ∧
      after.stk 0 = encodeBits cells ∧ after.stk 22 = [] ∧ after.stk 24 = [] ∧ after.stk 23 = [] ∧
      (∀ other, other ≠ 0 → other ≠ 22 → other ≠ 24 → other ≠ 23 → after.stk other = contents other) ∧
      run.length ≤ timeBudget contents ∧
      (run.map (Lift.cfg embedding)).IsChain (fun a b => TM2.step OutputList.finalProgram a = some b) := by
  obtain ⟨localRun, localAfter, head, chain, last, halt, encoded, output, scratch, ticks, time, _space⟩ :=
    OutputList.final_cells_runs (contents 0) cells (contents 24) store.1
  cases localRun with
  | nil => simp only [List.head?_nil, reduceCtorEq] at head
  | cons start rest =>
    have same : start = OutputList.finalBefore (contents 0) (cells.flatMap encodeCellBits)
        (List.replicate cells.length true) (contents 24) store.1 := Option.some.inj head
    subst start
    obtain ⟨posts, after, size, actual, actualLast, view, frame⟩ :=
      Lift.path embedding OutputList.finalProgram (before contents store)
        (OutputList.finalBefore (contents 0) (cells.flatMap encodeCellBits)
          (List.replicate cells.length true) (contents 24) store.1)
        localAfter rest (initial_view cells contents store outputWord outputTicks) chain last
    have stopped : TM2.step program after = none := by
      apply Lift.halt_project embedding OutputList.finalProgram after
      rw [view]
      exact halt
    have sourceHalt : localAfter.l = none := by
      rcases localAfter with ⟨label, finiteStore, data⟩
      cases label with
      | none => rfl
      | some label => cases halt
    have selected : ∀ role, after.stk (embedding role) = localAfter.stk role := by
      intro role
      exact congrArg (fun state : OutputList.FinalState => state.stk role) view
    have sourceBudget := OutputList.listFinalBudget_cubic (contents 0) (cells.flatMap encodeCellBits)
      (List.replicate cells.length true) (contents 24)
    rw [initial_budget cells contents outputWord outputTicks] at sourceBudget
    have finalTime : (before contents store :: posts).length ≤ timeBudget contents := by
      simp only [List.length_cons] at time ⊢
      unfold timeBudget
      omega
    refine ⟨before contents store :: posts, after, rfl, actual, actualLast, stopped, ?_,
      (selected 0).trans encoded, (selected 1).trans output, (selected 2).trans scratch,
      (selected 3).trans ticks, ?_, finalTime, ?_⟩
    · exact (congrArg TM2.Cfg.l view).trans sourceHalt
    · intro other not0 not22 not24 not23
      exact frame other (OutputInstruction.emit_outside other not0 not22 not24 not23)
    · exact List.isChain_map_of_isChain _ (fun a b edge => source_clock a b edge) actual

end PDROC.BitVM.Codec.Finalize
