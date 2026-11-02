module

public import Paid.PDROC_BitVM_Log_BankMount_051

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

@[expose] public section

namespace PDROC.BitVM.Log.BankMount

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters

/-! Actual old-bank clears, actual encoded count scan and the complete real
field loop, joined ONCE. The final endpoint is BEFORE the actual footer pop;
it is not advertised as a completed mount/HALT. -/

def readyBudget (core : Bool) (cells : List Cell) (contents : Stack → List Bool) :=
  clearBudget contents + (2 * natBits (fieldCount core) + 5) +
    2 * (cells.flatMap encodeCellBits).length + 11 * cells.length + 1

theorem ready_runs (core : Bool) (cells : List Cell) (suffix : List Bool)
    (contents : Stack → List Bool) (store : Store)
    (size : cells.length = fieldCount core) (input : contents 0 = encodeBits cells ++ suffix) :
    ∃ (run : List SourceState) (vars : Store) (data : Stack → List Bool),
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core) a = some b) ∧
      run.getLast? = some (⟨some footerLabel, (vars, ()), data⟩ : SourceState) ∧
      vars.1 = (HeapLoad.cleared store).1 ∧ vars.2.1.2 = store.2.1.2 ∧
      FieldData core contents cells [] suffix data ∧ run.length ≤ readyBudget core cells contents := by
  obtain ⟨clearTrace, clearHead, clearChain, clearLast, clearLength⟩ := clear_prefix_runs core contents store
  let bodyBytes := cells.flatMap encodeCellBits ++ true :: suffix
  have headerInput : preCleared 16 contents 0 = encodeNatBits (fieldCount core) ++ bodyBytes := by
    rw [preCleared_input, input]
    simp only [encodeBits, size, bodyBytes, List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨headerTrace, headerHead, headerChain, headerLast, headerLength⟩ :=
    header_return core (fieldCount core) bodyBytes (preCleared 16 contents) (HeapLoad.cleared store)
      headerInput (preCleared_work contents).1
  have headerLastExact : headerTrace.getLast? = some (⟨some (fieldLabel 0 BankFieldRoot.startLabel),
      (HeapLoad.cleared store, ()), headerReady core cells suffix contents⟩ : SourceState) := by
    simpa only [headerReady, bodyBytes, BankHeader.finished, HeapLoad.cleared] using headerLast
  let headerBoundary : SourceState := ⟨some (headerLabel BankHeader.startLabel),
    (HeapLoad.cleared store, ()), preCleared 16 contents⟩
  let prefixTrace := clearTrace ++ headerTrace.tail
  have prefixHead : prefixTrace.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [prefixTrace, List.head?_append, clearHead, Option.some_or]
  have prefixChain : prefixTrace.IsChain (fun a b => TM2.step (sourceProgram core) a = some b) :=
    TwoStack.join_chain clearTrace headerTrace headerBoundary clearChain headerChain clearLast headerHead
  have headerNotOne : headerTrace.length ≠ 1 := by omega
  have prefixLast : prefixTrace.getLast? = some (⟨some (fieldLabel 0 BankFieldRoot.startLabel),
      (HeapLoad.cleared store, ()), headerReady core cells suffix contents⟩ : SourceState) := by
    simp only [prefixTrace, List.getLast?_append, List.getLast?_tail, headerNotOne, ↓reduceIte,
      headerLastExact, Option.some_or]
  obtain ⟨fieldTrace, vars, data, fieldHead, fieldChain, fieldLast, savedNat, savedExtra, finalData, fieldLength⟩ :=
    fields_runs core contents [] cells suffix (headerReady core cells suffix contents) (HeapLoad.cleared store)
      (FieldData.initial core cells suffix contents size)
  let fieldBoundary : SourceState := ⟨some (fieldLabel 0 BankFieldRoot.startLabel),
    (HeapLoad.cleared store, ()), headerReady core cells suffix contents⟩
  have fieldHeadExact : fieldTrace.head? = some fieldBoundary := by
    simpa only [fieldBoundary, List.length_nil, fieldEntry, fieldCount_pos core, ↓reduceDIte, Fin.mk_zero] using fieldHead
  have fieldNotOne : fieldTrace.length ≠ 1 := by
    intro one
    obtain ⟨single, singleton⟩ := List.length_eq_one_iff.mp one
    have headEqual : single = fieldBoundary :=
      Option.some.inj (by simpa only [singleton, List.head?_cons] using fieldHeadExact)
    have lastEqual : single = (⟨some footerLabel, (vars, ()), data⟩ : SourceState) :=
      Option.some.inj (by simpa only [singleton, List.getLast?_singleton] using fieldLast)
    have labels := congrArg (fun state : SourceState => state.l) (headEqual.symm.trans lastEqual)
    simp only [fieldBoundary, fieldLabel, footerLabel] at labels
    have impossible := Option.some.inj labels
    cases impossible
  let run := prefixTrace ++ fieldTrace.tail
  have head : run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [run, List.head?_append, prefixHead, Option.some_or]
  have chain : run.IsChain (fun a b => TM2.step (sourceProgram core) a = some b) :=
    TwoStack.join_chain prefixTrace fieldTrace fieldBoundary prefixChain fieldChain prefixLast fieldHeadExact
  have last : run.getLast? = some (⟨some footerLabel, (vars, ()), data⟩ : SourceState) := by
    simp only [run, List.getLast?_append, List.getLast?_tail, fieldNotOne, ↓reduceIte, fieldLast, Option.some_or]
  refine ⟨run, vars, data, head, chain, last, savedNat, savedExtra, ?_, ?_⟩
  · simpa only [List.nil_append] using finalData
  · have prefixLength : prefixTrace.length ≤ clearBudget contents + (2 * natBits (fieldCount core) + 5) := by
      simp only [prefixTrace, List.length_append, List.length_tail]
      omega
    simp only [run, List.length_append, List.length_tail, readyBudget]
    omega

end PDROC.BitVM.Log.BankMount
