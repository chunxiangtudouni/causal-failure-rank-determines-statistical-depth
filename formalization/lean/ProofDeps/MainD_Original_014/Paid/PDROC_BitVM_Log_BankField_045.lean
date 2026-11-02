module

public import Paid.PDROC_BitVM_Log_BankCell_043
public import Paid.PDROC_BitVM_Log_BankDrain_044

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

@[expose] public section

namespace PDROC.BitVM.Log.BankField

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native

/-! One real field read into a compile-time selected bank1..13: actual Cell
scan followed by actual reverse drain. A whole mount must really clear old
bank/ticks/capture first; no such caller reset is hidden in this component. -/

abbrev Stack := Fin 32
abbrev Alphabet (_ : Stack) := Bool
abbrev Label := Unit ⊕ (BankCell.Label ⊕ BankDrain.Label)
abbrev Store := Query.Store
abbrev SourceStore := Store × Unit
abbrev SourceState := TM2.Cfg Alphabet Label SourceStore
abbrev State := TM2.Cfg Alphabet Label Store

def doneLabel : Label := .inl ()
def cellLabel (label : BankCell.Label) : Label := .inr (.inl label)
def drainLabel (label : BankDrain.Label) : Label := .inr (.inr label)
def startLabel := cellLabel CellCopy.startLabel

def sourceProgram (field : Fin 13) : Label → TM2.Stmt Alphabet Label SourceStore
  | .inl _ => .halt
  | .inr (.inl label) => Inline.statement (τ := Unit) cellLabel (drainLabel 0) (BankCell.program label)
  | .inr (.inr label) => Inline.statement (τ := Unit) drainLabel doneLabel (BankDrain.program field label)

def program (field : Fin 13) := StoreIso.machine CellCopy.peel (sourceProgram field)

theorem cell_agrees (field : Fin 13) : ∀ label,
    sourceProgram field (cellLabel label) =
      Inline.statement (τ := Unit) cellLabel (drainLabel 0) (BankCell.program label) := by intro label; rfl

theorem drain_agrees (field : Fin 13) : ∀ label,
    sourceProgram field (drainLabel label) =
      Inline.statement (τ := Unit) drainLabel doneLabel (BankDrain.program field label) := by intro label; rfl

theorem source_supports (field : Fin 13) : TM2.Supports (sourceProgram field) (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    rcases label with marker | (cell | drain)
    · cases marker; simp [sourceProgram, TM2.SupportsStmt]
    · apply Inline.supports_statement cellLabel (drainLabel 0)
        (Finset.univ : Finset BankCell.Label) (Finset.univ : Finset Label)
      · intro index _; exact Finset.mem_univ _
      · exact Finset.mem_univ _
      · exact BankCell.supports.2 cell (Finset.mem_univ _)
    · apply Inline.supports_statement drainLabel doneLabel
        (Finset.univ : Finset BankDrain.Label) (Finset.univ : Finset Label)
      · intro index _; exact Finset.mem_univ _
      · exact Finset.mem_univ _
      · exact (BankDrain.supports field).2 drain (Finset.mem_univ _)

theorem supports (field : Fin 13) : TM2.Supports (program field) (Finset.univ : Finset Label) :=
  StoreIso.supports CellCopy.peel (sourceProgram field) (Finset.univ : Finset Label) (source_supports field)

def result (field : Fin 13) (value : Cell) (suffix : List Bool) (contents : Stack → List Bool) :=
  BankDrain.drained field (BankCell.captured value suffix contents)

theorem result_bank (field : Fin 13) (value : Cell) (suffix : List Bool) (contents : Stack → List Bool) :
    result field value suffix contents (BankDrain.bankSlot field) =
      encodeCellBits value ++ contents (BankDrain.bankSlot field) := by
  have not0 := BankDrain.bankSlot_ne field 0 (by decide)
  have not25 := BankDrain.bankSlot_ne field 25 (by decide)
  have not29 := BankDrain.bankSlot_ne field 29 (by decide)
  simp only [result, BankDrain.drained, Function.update_self, BankCell.captured,
    Function.update_of_ne not29, Function.update_of_ne not25, Function.update_of_ne not0,
    List.reverse_reverse]

theorem result_input (field : Fin 13) (value : Cell) (suffix : List Bool) (contents : Stack → List Bool) :
    result field value suffix contents 0 = suffix := by
  have notBank := (BankDrain.bankSlot_ne field 0 (by decide)).symm
  simp only [result, BankDrain.drained, Function.update_of_ne notBank,
    BankCell.captured, Function.update_of_ne (by decide : (0 : Stack) ≠ 29),
    Function.update_of_ne (by decide : (0 : Stack) ≠ 25), Function.update_self]

theorem source_runs (field : Fin 13) (value : Cell) (suffix : List Bool)
    (contents : Stack → List Bool) (store : Store)
    (input : contents 0 = encodeCellBits value ++ suffix) (ticks : contents 24 = []) (capture : contents 29 = []) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram field) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (sourceProgram field) after = none ∧ after.l = none ∧
      after.var = ((none, store.2), ()) ∧ after.stk = result field value suffix contents ∧
      run.length ≤ 2 * (encodeCellBits value).length + 10 := by
  let beforeCell : BankCell.State := ⟨some CellCopy.startLabel, store, contents⟩
  obtain ⟨cellSource, cellFinal, cellHead, cellChain, cellLast, cellHalt, cellDone, cellVars, cellData, cellLength⟩ :=
    BankCell.runs value suffix beforeCell rfl input ticks capture
  obtain ⟨left, leftFinal, leftHead, leftChain, leftLast, leftLabel, leftData, leftVars, leftLength⟩ :=
    Inline.actual_return_trace cellLabel (drainLabel 0) BankCell.program (sourceProgram field)
      (cell_agrees field) cellSource beforeCell cellFinal () cellHead cellChain cellLast cellHalt
  have leftDataExact : leftFinal.stk = BankCell.captured value suffix contents := leftData.trans cellData
  have leftVarExact : leftFinal.var = ((none, store.2), ()) := by rw [leftVars, cellVars]
  have leftFinalEq : leftFinal = (⟨some (drainLabel 0), ((none, store.2), ()),
      BankCell.captured value suffix contents⟩ : SourceState) := by
    rcases leftFinal with ⟨label, vars, data⟩
    change label = some (drainLabel 0) at leftLabel
    change vars = ((none, store.2), ()) at leftVarExact
    change data = BankCell.captured value suffix contents at leftDataExact
    subst label; subst vars; subst data
    rfl
  let beforeDrain : BankDrain.State := ⟨some 0, (none, store.2), BankCell.captured value suffix contents⟩
  obtain ⟨drainSource, drainFinal, drainHead, drainChain, drainLast, drainHalt, drainDone, drainVars, drainData, drainLength⟩ :=
    BankDrain.runs field beforeDrain rfl
  obtain ⟨right, rightFinal, rightHead, rightChain, rightLast, rightLabel, rightData, rightVars, rightLength⟩ :=
    Inline.actual_return_trace drainLabel doneLabel (BankDrain.program field) (sourceProgram field)
      (drain_agrees field) drainSource beforeDrain drainFinal () drainHead drainChain drainLast drainHalt
  have rightDataExact : rightFinal.stk = result field value suffix contents := rightData.trans drainData
  have rightVarExact : rightFinal.var = ((none, store.2), ()) := by rw [rightVars, drainVars]
  have rightFinalEq : rightFinal = (⟨some doneLabel, ((none, store.2), ()),
      result field value suffix contents⟩ : SourceState) := by
    rcases rightFinal with ⟨label, vars, data⟩
    change label = some doneLabel at rightLabel
    change vars = ((none, store.2), ()) at rightVarExact
    change data = result field value suffix contents at rightDataExact
    subst label; subst vars; subst data
    rfl
  let final : SourceState := ⟨none, ((none, store.2), ()), result field value suffix contents⟩
  let body := right ++ [final]
  have bodyHead : body.head? = some (⟨some (drainLabel 0), ((none, store.2), ()),
      BankCell.captured value suffix contents⟩ : SourceState) := by
    simp only [body, List.head?_append, rightHead, Option.some_or]
    rfl
  have bodyChain : body.IsChain (fun a b => TM2.step (sourceProgram field) a = some b) := by
    apply rightChain.append (List.isChain_singleton _)
    intro old ho next hn
    simp only [rightLast, Option.mem_some_iff] at ho
    simp only [List.head?_cons, Option.mem_some_iff] at hn
    subst old; subst next
    rw [rightFinalEq]
    rfl
  have bodyLast : body.getLast? = some final := List.getLast?_append_cons right final []
  have rightPositive : 0 < right.length := by
    rw [rightLength, drainLength]
    omega
  have bodyNotOne : body.length ≠ 1 := by
    simp only [body, List.length_append, List.length_cons, List.length_nil]
    omega
  let run := left ++ body.tail
  have head : run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [run, List.head?_append, leftHead, Option.some_or, Inline.cfg, beforeCell,
      Option.map_some, Option.getD_some, startLabel]
  have chain : run.IsChain (fun a b => TM2.step (sourceProgram field) a = some b) := by
    apply TwoStack.join_chain left body leftFinal leftChain bodyChain leftLast
    simpa only [leftFinalEq] using bodyHead
  have last : run.getLast? = some final := by
    simp only [run, List.getLast?_append, List.getLast?_tail, bodyNotOne, ↓reduceIte, bodyLast, Option.some_or]
  refine ⟨run, final, head, chain, last, rfl, rfl, rfl, rfl, ?_⟩
  have leftBound : left.length ≤ (encodeCellBits value).length + 6 := by rw [leftLength]; exact cellLength
  have rightBound : right.length = (encodeCellBits value).length + 3 := by
    rw [rightLength, drainLength]
    simp only [beforeDrain, BankCell.captured, Function.update_self, List.length_reverse]
  simp only [run, body, List.length_append, List.length_tail, List.length_cons, List.length_nil]
  omega

theorem runs (field : Fin 13) (value : Cell) (suffix : List Bool)
    (contents : Stack → List Bool) (store : Store)
    (input : contents 0 = encodeCellBits value ++ suffix) (ticks : contents 24 = []) (capture : contents 29 = []) :
    ∃ (run : List State) (after : State),
      run.head? = some (⟨some startLabel, store, contents⟩ : State) ∧
      run.IsChain (fun a b => TM2.step (program field) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program field) after = none ∧ after.l = none ∧
      after.var = (none, store.2) ∧ after.stk = result field value suffix contents ∧
      run.length ≤ 2 * (encodeCellBits value).length + 10 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt, sourceDone, sourceVar, sourceData, sourceLength⟩ :=
    source_runs field value suffix contents store input ticks capture
  obtain ⟨run, after, head, chain, last, halt, label, saved, data, length⟩ :=
    StoreIso.actual_trace CellCopy.peel (sourceProgram field) source
      (⟨some startLabel, (store, ()), contents⟩ : SourceState) sourceFinal sourceHead sourceChain sourceLast sourceHalt
  refine ⟨run, after, head, chain, last, halt, label.trans sourceDone, ?_, data.trans sourceData, ?_⟩
  · rw [saved, sourceVar]; rfl
  · rw [length]; exact sourceLength

end PDROC.BitVM.Log.BankField
