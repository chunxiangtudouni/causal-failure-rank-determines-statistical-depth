module

public import Paid.PDROC_BitVM_Codec_NatWriter_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Codec.NatWriter

open Turing PaperProofs.Common.Native.RationalControllerComputation

abbrev HeaderState := TM2.Cfg Alphabet PDROC.BitVM.Log.Header.Label (Option Bool)

def headerBefore (value : ℕ) (suffix : List Bool) : HeaderState :=
  ⟨some 0, none, PDROC.BitVM.Log.TwoStack.threeStacks (encodeNat value ++ suffix) [] []⟩

def headerAfter (value : ℕ) (suffix : List Bool) : HeaderState :=
  ⟨none, none, PDROC.BitVM.Log.TwoStack.threeStacks suffix (encodeNat value).reverse []⟩

/-- Reuse the already checked actual scanner with target2 as its width
ticks and LEFT1 as its archive. No new decoder or host width is introduced. -/
theorem header_runs (value : ℕ) (suffix : List Bool) :
    ∃ run : List HeaderState,
      run.head? = some (headerBefore value suffix) ∧
      run.IsChain (fun a b => TM2.step
        (PDROC.BitVM.Native.Lift.machine headerRoles PDROC.BitVM.Log.Header.program) a = some b) ∧
      run.getLast? = some (headerAfter value suffix) ∧
      TM2.step (PDROC.BitVM.Native.Lift.machine headerRoles PDROC.BitVM.Log.Header.program)
        (headerAfter value suffix) = none ∧
      run.length = 2 * natBits value + 4 := by
  obtain ⟨source, sourceHead, sourceChain, sourceLast, _sourceHalt, sourceSize,
    _input, _ticks, _archive⟩ := PDROC.BitVM.Log.Header.officialNat_runs value suffix [] none
  simp only [PDROC.BitVM.Link.CodecCandidate.encodeNatBits_eq_neutral] at sourceHead sourceLast
  let originalFinal := PDROC.BitVM.Log.Header.state none none suffix [] (encodeNat value).reverse
  have sourceLast' : source.getLast? = some originalFinal := by
    simpa only [List.append_nil, originalFinal] using sourceLast
  have entry : PDROC.BitVM.Native.Lift.cfg headerRoles (headerBefore value suffix) =
      PDROC.BitVM.Log.Header.state (some 0) none (encodeNat value ++ suffix) [] [] := by
    have same : PDROC.BitVM.Native.Lift.slots headerRoles
        (PDROC.BitVM.Log.TwoStack.threeStacks (encodeNat value ++ suffix) [] []) =
          PDROC.BitVM.Log.Header.slots (encodeNat value ++ suffix) [] [] := by
      funext role
      fin_cases role <;> rfl
    change (⟨some 0, none, PDROC.BitVM.Native.Lift.slots headerRoles
      (PDROC.BitVM.Log.TwoStack.threeStacks (encodeNat value ++ suffix) [] [])⟩ :
        PDROC.BitVM.Log.Header.State) = _
    rw [same]
    rfl
  cases source with
  | nil => simp only [List.head?_nil, reduceCtorEq] at sourceHead
  | cons first rest =>
    have firstEq := Option.some.inj sourceHead
    subst first
    obtain ⟨posts, final, length, actual, last, represented, _frame⟩ :=
      PDROC.BitVM.Native.Lift.path headerRoles PDROC.BitVM.Log.Header.program
        (headerBefore value suffix)
        (PDROC.BitVM.Log.Header.state (some 0) none (encodeNat value ++ suffix) [] [])
        originalFinal rest entry sourceChain sourceLast'
    have same : final = headerAfter value suffix := by
      rcases final with ⟨label, store, contents⟩
      have sameLabel := congrArg (fun state : PDROC.BitVM.Log.Header.State => state.l) represented
      have sameStore := congrArg (fun state : PDROC.BitVM.Log.Header.State => state.var) represented
      change label = none at sameLabel
      change store = none at sameStore
      subst label
      subst store
      have sameData : contents = PDROC.BitVM.Log.TwoStack.threeStacks suffix (encodeNat value).reverse [] := by
        funext role
        fin_cases role
        · exact congrArg (fun state : PDROC.BitVM.Log.Header.State => state.stk 0) represented
        · exact congrArg (fun state : PDROC.BitVM.Log.Header.State => state.stk 2) represented
        · exact congrArg (fun state : PDROC.BitVM.Log.Header.State => state.stk 1) represented
      rw [sameData]
      rfl
    rw [same] at last
    refine ⟨headerBefore value suffix :: posts, rfl, actual, last, rfl, ?_⟩
    change rest.length + 1 = 2 * natBits value + 4 at sourceSize
    simp only [List.length_cons, length]
    exact sourceSize

structure Path (before after : State) where
  states : List State
  first : states.head? = some before
  actual : states.IsChain (fun a b => TM2.step program a = some b)
  last : states.getLast? = some after

theorem joined_last (left right : List State) (middle after : State)
    (leftLast : left.getLast? = some middle) (rightHead : right.head? = some middle)
    (rightLast : right.getLast? = some after) : (left ++ right.tail).getLast? = some after := by
  cases right with
  | nil => simp only [List.head?_nil, reduceCtorEq] at rightHead
  | cons head tail =>
    cases tail with
    | nil =>
      have start : head = middle := Option.some.inj rightHead
      have finish : head = after := Option.some.inj rightLast
      simp only [List.tail_cons, List.append_nil]
      exact leftLast.trans (congrArg some (start.symm.trans finish))
    | cons next rest =>
      have notOne : (head :: next :: rest).length ≠ 1 := by
        simp only [List.length_cons]
        omega
      simp only [List.getLast?_append, List.getLast?_tail, notOne, ↓reduceIte,
        rightLast, Option.some_or]

def Path.append {before middle after : State} (left : Path before middle) (right : Path middle after) :
    Path before after where
  states := left.states ++ right.states.tail
  first := by simp only [List.head?_append, left.first, Option.some_or]
  actual := PDROC.BitVM.Log.TwoStack.join_chain left.states right.states middle
    left.actual right.actual left.last right.first
  last := joined_last left.states right.states middle after left.last right.first right.last

theorem Path.append_length {before middle after : State} (left : Path before middle) (right : Path middle after) :
    (left.append right).states.length ≤ left.states.length + right.states.length := by
  simp only [Path.append, List.length_append, List.length_tail]
  omega

theorem state_eq (left right : State) (label : left.l = right.l) (store : left.var = right.var)
    (data : left.stk = right.stk) : left = right := by
  rcases left with ⟨leftLabel, leftStore, leftData⟩
  rcases right with ⟨rightLabel, rightStore, rightData⟩
  change leftLabel = rightLabel at label
  change leftStore = rightStore at store
  change leftData = rightData at data
  subst rightLabel
  subst rightStore
  subst rightData
  rfl

end PDROC.BitVM.Codec.NatWriter
