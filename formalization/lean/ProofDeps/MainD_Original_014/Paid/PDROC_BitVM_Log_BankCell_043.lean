module

public import Paid.PDROC_BitVM_Log_HeapLoad_040

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

namespace PDROC.BitVM.Log.BankCell

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native

/-! First half of the physical readonly-bank reader. This is only the actual
Cell scanner lifted to fixed global roles, not a whole bank mount theorem.
Tick24/capture29 emptiness must be PRODUCED by the outer actual clear code.
Input values are specifications of Bool data; sigma contains only Query flags. -/

abbrev Stack := Fin 32
abbrev Alphabet (_ : Stack) := Bool
abbrev Label := CellCopy.Label
abbrev Store := Query.Store
abbrev State := TM2.Cfg Alphabet Label Store

def embedding : CellCopy.Stack ↪ Stack where
  toFun := fun index => if index = 0 then 0 else if index = 1 then 24
    else if index = 2 then 25 else if index = 3 then 26 else if index = 4 then 27
    else if index = 5 then 28 else 29
  inj' := by
    intro left right equal
    fin_cases left <;> fin_cases right <;> simp_all

def program := Lift.machine embedding CellCopy.program

theorem supports : TM2.Supports program (Finset.univ : Finset Label) :=
  Lift.supports embedding CellCopy.program (Finset.univ : Finset Label) CellCopy.supports

def captured (value : Cell) (suffix : List Bool) (contents : Stack → List Bool) :=
  Function.update (Function.update (Function.update contents 0 suffix) 25
    ((encodeCellBits value).reverse ++ contents 25)) 29 (encodeCellBits value).reverse

theorem representation (value : Cell) (suffix : List Bool) (before : State)
    (position : before.l = some CellCopy.startLabel)
    (input : before.stk 0 = encodeCellBits value ++ suffix)
    (ticks : before.stk 24 = []) (capture : before.stk 29 = []) :
    Lift.cfg embedding before = CellCopy.state (some CellCopy.startLabel) before.var
      (encodeCellBits value ++ suffix) [] (before.stk 25) [] (Lift.slots embedding before.stk) := by
  have slots : Lift.slots embedding before.stk = Capture.slots
      (encodeCellBits value ++ suffix) [] (before.stk 25) [] (Lift.slots embedding before.stk) := by
    funext index
    fin_cases index <;> simp [Lift.slots, embedding, Capture.slots, input, ticks, capture]
  change (⟨before.l, before.var, Lift.slots embedding before.stk⟩ : CellCopy.State) = _
  rw [position]
  exact congrArg (fun contents : CellCopy.Stack → List Bool =>
    (⟨some CellCopy.startLabel, before.var, contents⟩ : CellCopy.State)) slots

theorem captured_shape (value : Cell) (suffix : List Bool) (contents data : Stack → List Bool)
    (ticks : contents 24 = [])
    (projected : Lift.slots embedding data = Capture.slots suffix []
      ((encodeCellBits value).reverse ++ contents 25) (encodeCellBits value).reverse
      (Lift.slots embedding contents))
    (frame : ∀ index : Stack, (∀ localIndex, index ≠ embedding localIndex) → data index = contents index) :
    data = captured value suffix contents := by
  funext index
  by_cases mapped : ∃ localIndex, embedding localIndex = index
  · rcases mapped with ⟨localIndex, rfl⟩
    have fact := congrFun projected localIndex
    fin_cases localIndex <;>
      simpa [Lift.slots, embedding, Capture.slots, captured, ticks] using fact
  · have not0 : index ≠ 0 := by
      intro equal
      apply mapped
      refine ⟨0, ?_⟩
      simpa [embedding] using equal.symm
    have not25 : index ≠ 25 := by
      intro equal
      apply mapped
      refine ⟨2, ?_⟩
      simpa [embedding] using equal.symm
    have not29 : index ≠ 29 := by
      intro equal
      apply mapped
      refine ⟨6, ?_⟩
      simpa [embedding] using equal.symm
    rw [captured, Function.update_of_ne not29, Function.update_of_ne not25, Function.update_of_ne not0]
    exact frame index (fun localIndex equal => mapped ⟨localIndex, equal.symm⟩)

/-- ONE genuine CellCopy path, statically lifted to global32 roles. Both
reverse copies originate in actual tag/sign/field pops. No encoded Cell is
installed by a host update in the program; captured is only the proven result. -/
theorem runs (value : Cell) (suffix : List Bool) (before : State)
    (position : before.l = some CellCopy.startLabel)
    (input : before.stk 0 = encodeCellBits value ++ suffix)
    (ticks : before.stk 24 = []) (capture : before.stk 29 = []) :
    ∃ (run : List State) (after : State),
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step program a = some b) ∧
      run.getLast? = some after ∧ TM2.step program after = none ∧ after.l = none ∧
      after.var = (none, before.var.2) ∧ after.stk = captured value suffix before.stk ∧
      run.length ≤ (encodeCellBits value).length + 6 := by
  let other := Lift.slots embedding before.stk
  let sourceStart := CellCopy.state (some CellCopy.startLabel) before.var
    (encodeCellBits value ++ suffix) [] (before.stk 25) [] other
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ :=
    CellCopy.copy_runs value suffix (before.stk 25) [] other before.var
  cases source with
  | nil => simp only [List.head?_nil, reduceCtorEq] at sourceHead
  | cons first rest =>
    have firstEq : first = sourceStart := Option.some.inj sourceHead
    subst first
    obtain ⟨posts, after, length, chain, last, projected, frame⟩ :=
      Lift.path embedding CellCopy.program before sourceStart sourceFinal rest
        (representation value suffix before position input ticks capture) sourceChain sourceLast
    have halt : TM2.step program after = none := by
      apply Lift.halt_project embedding CellCopy.program after
      rw [projected]
      exact sourceHalt
    have done : after.l = none :=
      (congrArg (fun state : CellCopy.State => state.l) projected).trans sourceDone
    have vars : after.var = (none, before.var.2) :=
      (congrArg (fun state : CellCopy.State => state.var) projected).trans sourceVar
    have data : Lift.slots embedding after.stk = Capture.slots suffix []
        ((encodeCellBits value).reverse ++ before.stk 25) (encodeCellBits value).reverse other := by
      have actual := (congrArg (fun state : CellCopy.State => state.stk) projected).trans sourceData
      simpa only [Lift.cfg, List.append_nil] using actual
    refine ⟨before :: posts, after, rfl, chain, last, halt, done, vars,
      captured_shape value suffix before.stk after.stk ticks data frame, ?_⟩
    simp only [List.length_cons] at sourceLength ⊢
    omega

end PDROC.BitVM.Log.BankCell
