module

public import Paid.PDROC_BitVM_Log_InputLoad_062

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

@[expose] public section

namespace PDROC.BitVM.Log.InputLoad

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters

/-! Real finite candidate search. Nat equalities below specify the actual
Bool flag already proved by literal/comparison runs. They do not occur in
the machine transition, whose sole decision is Query.equality. -/

def Ready (query : ℕ) (contents : Stack → List Bool) : Prop :=
  contents 24 = [] ∧ contents 26 = encodeNatBits query ∧ contents 27 = [] ∧ contents 28 = []

theorem candidate_bits (field : Fin 13) : natBits field.val ≤ 4 := by fin_cases field <;> decide

theorem candidate_found_runs (core : Bool) (pointer destination : Register) (field : Fin 13) (query : ℕ)
    (contents : Stack → List Bool) (store : Store) (ready : Ready query contents) (same : field.val = query) :
    ∃ (run : List SourceState) (vars : Store),
      run.head? = some (⟨some (literalLabel field InputLiteral.startLabel), (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) ∧
      run.getLast? = some (⟨some (copyLabel field 0), (vars, ()), contents⟩ : SourceState) ∧
      Query.equality vars.2.1 = true ∧ run.length ≤ 30 := by
  obtain ⟨source, vars, head, chain, last, saved, flag, length⟩ :=
    candidate_compare_return core pointer destination field query contents store ready.1 ready.2.1 ready.2.2.1 ready.2.2.2
  have matched : Query.equality vars.2.1 = true := by simpa only [same, decide_true] using flag
  let final : SourceState := ⟨some (copyLabel field 0), (vars, ()), contents⟩
  let run := source ++ [final]
  have actual : run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) := by
    apply chain.append (List.isChain_singleton _)
    intro old ho next hn
    simp only [last, Option.mem_some_iff] at ho
    simp only [List.head?_cons, Option.mem_some_iff] at hn
    subst old; subst next
    exact matched_step core pointer destination field (vars, ()) contents matched
  refine ⟨run, vars, ?_, actual, List.getLast?_append_cons source final [], matched, ?_⟩
  · simp only [run, List.head?_append, head, Option.some_or]
  · have bits := candidate_bits field
    simp only [run, List.length_append, List.length_cons, List.length_nil]
    omega

theorem candidate_miss_runs (core : Bool) (pointer destination : Register) (field : Fin 13) (query : ℕ)
    (contents : Stack → List Bool) (store : Store) (ready : Ready query contents) (different : field.val ≠ query) :
    ∃ (run : List SourceState) (vars : Store),
      run.head? = some (⟨some (literalLabel field InputLiteral.startLabel), (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) ∧
      run.getLast? = some (⟨some (nextCandidate core field), (vars, ()), contents⟩ : SourceState) ∧
      Query.equality vars.2.1 = false ∧ run.length ≤ 30 := by
  obtain ⟨source, vars, head, chain, last, saved, flag, length⟩ :=
    candidate_compare_return core pointer destination field query contents store ready.1 ready.2.1 ready.2.2.1 ready.2.2.2
  have unmatched : Query.equality vars.2.1 = false := by simpa only [different, decide_false] using flag
  let final : SourceState := ⟨some (nextCandidate core field), (vars, ()), contents⟩
  let run := source ++ [final]
  have actual : run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) := by
    apply chain.append (List.isChain_singleton _)
    intro old ho next hn
    simp only [last, Option.mem_some_iff] at ho
    simp only [List.head?_cons, Option.mem_some_iff] at hn
    subst old; subst next
    exact unmatched_step core pointer destination field (vars, ()) contents unmatched
  refine ⟨run, vars, ?_, actual, List.getLast?_append_cons source final [], unmatched, ?_⟩
  · simp only [run, List.head?_append, head, Option.some_or]
  · have bits := candidate_bits field
    simp only [run, List.length_append, List.length_cons, List.length_nil]
    omega

theorem selected_runs (core : Bool) (pointer destination : Register) (query cursor : ℕ)
    (range : query < BankMount.fieldCount core) (beforeQuery : cursor ≤ query)
    (contents : Stack → List Bool) (store : Store) (ready : Ready query contents) :
    ∃ (run : List SourceState) (vars : Store),
      run.head? = some (⟨some (literalLabel ⟨cursor, by have bound := BankMount.fieldCount_le core; omega⟩ InputLiteral.startLabel),
        (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) ∧
      run.getLast? = some (⟨some (copyLabel ⟨query, by have bound := BankMount.fieldCount_le core; omega⟩ 0),
        (vars, ()), contents⟩ : SourceState) ∧
      Query.equality vars.2.1 = true ∧ run.length ≤ 50 * (query - cursor + 1) := by
  have queryBound : query < 13 := by have bound := BankMount.fieldCount_le core; omega
  have build : ∀ distance cursor : ℕ, ∀ (equal : cursor + distance = query) (store : Store),
      ∃ (run : List SourceState) (vars : Store),
        run.head? = some (⟨some (literalLabel ⟨cursor, by omega⟩ InputLiteral.startLabel), (store, ()), contents⟩ : SourceState) ∧
        run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) ∧
        run.getLast? = some (⟨some (copyLabel ⟨query, queryBound⟩ 0), (vars, ()), contents⟩ : SourceState) ∧
        Query.equality vars.2.1 = true ∧ run.length ≤ 50 * (distance + 1) := by
    intro distance
    induction distance with
    | zero =>
      intro cursor equal store
      have current : cursor = query := by omega
      subst cursor
      obtain ⟨run, vars, head, chain, last, flag, length⟩ :=
        candidate_found_runs core pointer destination ⟨query, queryBound⟩ query contents store ready rfl
      exact ⟨run, vars, head, chain, last, flag, by omega⟩
    | succ distance ih =>
      intro cursor equal store
      have cursorBound : cursor < 13 := by omega
      let field : Fin 13 := ⟨cursor, cursorBound⟩
      have different : field.val ≠ query := by change cursor ≠ query; omega
      obtain ⟨left, middleVars, leftHead, leftChain, leftLast, notFound, leftLength⟩ :=
        candidate_miss_runs core pointer destination field query contents store ready different
      obtain ⟨right, vars, rightHead, rightChain, rightLast, flag, rightLength⟩ := ih (cursor + 1) (by omega) middleVars
      have nextBound : cursor + 1 < BankMount.fieldCount core := by omega
      let middle : SourceState := ⟨some (nextCandidate core field), (middleVars, ()), contents⟩
      have rightHeadExact : right.head? = some middle := by
        simpa only [middle, nextCandidate, field, nextBound, ↓reduceDIte] using rightHead
      let run := left ++ right.tail
      have head : run.head? = some (⟨some (literalLabel field InputLiteral.startLabel), (store, ()), contents⟩ : SourceState) := by
        simp only [run, List.head?_append, leftHead, Option.some_or]
      have chain : run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) :=
        TwoStack.join_chain left right middle leftChain rightChain leftLast rightHeadExact
      have notOne : right.length ≠ 1 := by
        intro one
        obtain ⟨single, singleton⟩ := List.length_eq_one_iff.mp one
        have firstEqual : single = middle := Option.some.inj (by simpa only [singleton, List.head?_cons] using rightHeadExact)
        have lastEqual : single = (⟨some (copyLabel ⟨query, queryBound⟩ 0), (vars, ()), contents⟩ : SourceState) :=
          Option.some.inj (by simpa only [singleton, List.getLast?_singleton] using rightLast)
        have labels := congrArg (fun state : SourceState => state.l) (firstEqual.symm.trans lastEqual)
        simp only [middle, nextCandidate, field, nextBound, ↓reduceDIte, literalLabel, copyLabel] at labels
        have impossible := Option.some.inj labels
        cases impossible
      have last : run.getLast? = some (⟨some (copyLabel ⟨query, queryBound⟩ 0), (vars, ()), contents⟩ : SourceState) := by
        simp only [run, List.getLast?_append, List.getLast?_tail, notOne, ↓reduceIte, rightLast, Option.some_or]
      refine ⟨run, vars, head, chain, last, flag, ?_⟩
      simp only [run, List.length_append, List.length_tail]
      omega
  obtain ⟨run, vars, head, chain, last, flag, length⟩ := build (query - cursor) cursor (by omega) store
  exact ⟨run, vars, head, chain, last, flag, length⟩

def candidateEntry (core : Bool) (cursor : ℕ) : Label :=
  if inside : cursor < BankMount.fieldCount core then
    literalLabel ⟨cursor, by have bound := BankMount.fieldCount_le core; omega⟩ InputLiteral.startLabel
  else invalidLabel

theorem nextCandidate_entry (core : Bool) (field : Fin 13) :
    nextCandidate core field = candidateEntry core (field.val + 1) := rfl

private theorem append_tail_last {α : Type} (left right : List α) (middle final : α)
    (leftLast : left.getLast? = some middle) (rightHead : right.head? = some middle)
    (rightLast : right.getLast? = some final) : (left ++ right.tail).getLast? = some final := by
  by_cases one : right.length = 1
  · obtain ⟨single, singleton⟩ := List.length_eq_one_iff.mp one
    have headEqual : single = middle := Option.some.inj (by simpa only [singleton, List.head?_cons] using rightHead)
    have lastEqual : single = final := Option.some.inj (by simpa only [singleton, List.getLast?_singleton] using rightLast)
    have equal : middle = final := headEqual.symm.trans lastEqual
    simpa only [singleton, List.tail_cons, List.tail_nil, List.append_nil, equal] using leftLast
  · simp only [List.getLast?_append, List.getLast?_tail, one, ↓reduceIte, rightLast, Option.some_or]

theorem exhausted_runs (core : Bool) (pointer destination : Register) (query cursor : ℕ)
    (range : BankMount.fieldCount core ≤ query) (cursorBound : cursor ≤ BankMount.fieldCount core)
    (contents : Stack → List Bool) (store : Store) (ready : Ready query contents) :
    ∃ (run : List SourceState) (vars : Store),
      run.head? = some (⟨some (candidateEntry core cursor), (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) ∧
      run.getLast? = some (⟨some invalidLabel, (vars, ()), contents⟩ : SourceState) ∧
      run.length ≤ 50 * (BankMount.fieldCount core - cursor) + 1 := by
  have countBound := BankMount.fieldCount_le core
  have build : ∀ remaining cursor : ℕ, cursor + remaining = BankMount.fieldCount core → ∀ store : Store,
      ∃ (run : List SourceState) (vars : Store),
        run.head? = some (⟨some (candidateEntry core cursor), (store, ()), contents⟩ : SourceState) ∧
        run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) ∧
        run.getLast? = some (⟨some invalidLabel, (vars, ()), contents⟩ : SourceState) ∧
        run.length ≤ 50 * remaining + 1 := by
    intro remaining
    induction remaining with
    | zero =>
      intro cursor equal store
      have current : cursor = BankMount.fieldCount core := by omega
      let before : SourceState := ⟨some invalidLabel, (store, ()), contents⟩
      refine ⟨[before], store, ?_, List.isChain_singleton _, rfl, by simp⟩
      simp only [List.head?_cons, candidateEntry, current, lt_self_iff_false, ↓reduceDIte]
      rfl
    | succ remaining ih =>
      intro cursor equal store
      have inside : cursor < BankMount.fieldCount core := by omega
      have cursorInside : cursor < 13 := by omega
      let field : Fin 13 := ⟨cursor, cursorInside⟩
      have different : field.val ≠ query := by change cursor ≠ query; omega
      obtain ⟨left, middleVars, leftHead, leftChain, leftLast, notFound, leftLength⟩ :=
        candidate_miss_runs core pointer destination field query contents store ready different
      obtain ⟨right, vars, rightHead, rightChain, rightLast, rightLength⟩ := ih (cursor + 1) (by omega) middleVars
      let middle : SourceState := ⟨some (nextCandidate core field), (middleVars, ()), contents⟩
      have rightHeadExact : right.head? = some middle := by
        simpa only [middle, nextCandidate_entry, field] using rightHead
      let run := left ++ right.tail
      have head : run.head? = some (⟨some (candidateEntry core cursor), (store, ()), contents⟩ : SourceState) := by
        simp only [run, List.head?_append, leftHead, Option.some_or, candidateEntry, inside, ↓reduceDIte, field]
      have chain : run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) :=
        TwoStack.join_chain left right middle leftChain rightChain leftLast rightHeadExact
      have last : run.getLast? = some (⟨some invalidLabel, (vars, ()), contents⟩ : SourceState) :=
        append_tail_last left right middle _ leftLast rightHeadExact rightLast
      refine ⟨run, vars, head, chain, last, ?_⟩
      have tailBound : right.length - 1 ≤ 50 * remaining := by omega
      simp only [run, List.length_append, List.length_tail]
      omega
  obtain ⟨run, vars, head, chain, last, length⟩ :=
    build (BankMount.fieldCount core - cursor) cursor (by omega) store
  exact ⟨run, vars, head, chain, last, length⟩

end PDROC.BitVM.Log.InputLoad
