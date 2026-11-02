module

public import Paid.PDROC_BitVM_Log_CellField_001
public import Paid.PDROC_BitVM_Native_Frame_003
public import Paid.PDROC_BitVM_Native_Return_006
public import Paid.PDROC_BitVM_Log_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Log.CellSkip

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters

/-- One genuine ordinary Nat scanner call on the fixed Cell work stacks.
The agreement premise is equality to the actual four local code blocks,
not a whole-run success or numerical bound assumption. -/
theorem header_return_run (labels : Header.Label → Label) (returnLabel : Label)
    (agrees : ∀ label, program (labels label) = headerCode labels returnLabel label)
    (value : ℕ) (suffix archive : List Bool) (other : Stack → List Bool) (store : Store) :
    ∃ run : List State,
      run.head? = some (state (some (labels 0)) store (encodeNatBits value ++ suffix) [] archive other) ∧
      run.IsChain (fun before after => TM2.step program before = some after) ∧
      run.getLast? = some (state (some returnLabel) (none, store.2) suffix []
        ((encodeNatBits value).reverse ++ archive) other) ∧
      run.length = 2 * natBits value + 4 := by
  let before : TM2.Cfg (fun _ : Stack => Bool) Header.Label (Option Bool) :=
    ⟨some 0, store.1, slots (encodeNatBits value ++ suffix) [] archive other⟩
  let oldStart : Header.State := Header.state (some 0) store.1 (encodeNatBits value ++ suffix) [] archive
  let oldFinal : Header.State := Header.state none none suffix [] ((encodeNatBits value).reverse ++ archive)
  have representation : Native.Lift.cfg headerEmbed before = oldStart := by
    have content : Native.Lift.slots headerEmbed before.stk =
        Header.slots (encodeNatBits value ++ suffix) [] archive := by
      funext index
      fin_cases index <;> simp [Native.Lift.slots, before, headerEmbed, slots,
        Header.slots, TwoStack.stackContents]
    exact congrArg (fun contents : Header.Stack → List Bool =>
      (⟨some 0, store.1, contents⟩ : Header.State)) content
  obtain ⟨source, sourceHead, sourceChain, sourceLast, sourceHalt, sourceLength, _, _, _⟩ :=
    Header.officialNat_runs value suffix archive store.1
  cases source with
  | nil => simp only [List.head?_nil, reduceCtorEq] at sourceHead
  | cons start rest =>
    have same : start = oldStart := Option.some.inj sourceHead
    subst start
    obtain ⟨posts, liftedFinal, liftedLength, liftedChain, liftedLast, finalRep, frame⟩ :=
      Native.Lift.path headerEmbed Header.program before oldStart oldFinal rest
        representation sourceChain sourceLast
    have liftedHalt : TM2.step (Native.Lift.machine headerEmbed Header.program) liftedFinal = none := by
      apply Native.Lift.halt_project
      rw [finalRep]
      exact sourceHalt
    obtain ⟨run, after, head, chain, last, returned, data, localStoreEq, length⟩ :=
      Native.Inline.actual_return_trace labels returnLabel
        (Native.Lift.machine headerEmbed Header.program) program agrees
        (before :: posts) before liftedFinal store.2 rfl liftedChain liftedLast liftedHalt
    have primary : liftedFinal.var = none := by
      exact congrArg (fun current : Header.State => current.var) finalRep
    have callerStoreEq : after.var = (none, store.2) := by rw [localStoreEq, primary]
    have contentsEq : after.stk = slots suffix [] ((encodeNatBits value).reverse ++ archive) other := by
      rw [data]
      funext index
      fin_cases index
      · have equal := congrArg (fun current : Header.State => current.stk 0) finalRep
        simpa [Native.Lift.cfg, Native.Lift.slots, headerEmbed, oldFinal,
          Header.state, Header.slots, TwoStack.stackContents, slots] using equal
      · have equal := congrArg (fun current : Header.State => current.stk 1) finalRep
        simpa [Native.Lift.cfg, Native.Lift.slots, headerEmbed, oldFinal,
          Header.state, Header.slots, TwoStack.stackContents, slots] using equal
      · have equal := congrArg (fun current : Header.State => current.stk 2) finalRep
        simpa [Native.Lift.cfg, Native.Lift.slots, headerEmbed, oldFinal,
          Header.state, Header.slots, TwoStack.stackContents, slots] using equal
      · simpa [before, slots] using frame 3 (by intro index; fin_cases index <;> decide)
      · simpa [before, slots] using frame 4 (by intro index; fin_cases index <;> decide)
      · simpa [before, slots] using frame 5 (by intro index; fin_cases index <;> decide)
      · simpa [before, slots] using frame 6 (by intro index; fin_cases index <;> decide)
    have afterEq : after = state (some returnLabel) (none, store.2) suffix []
        ((encodeNatBits value).reverse ++ archive) other := by
      rcases after with ⟨label, vars, currentSlots⟩
      change label = some returnLabel at returned
      change vars = (none, store.2) at callerStoreEq
      change currentSlots = slots suffix [] ((encodeNatBits value).reverse ++ archive) other at contentsEq
      subst label
      subst vars
      subst currentSlots
      rfl
    refine ⟨run, ?_, chain, ?_, ?_⟩
    · exact head
    · simpa only [afterEq] using last
    · simp only [List.length_cons] at length sourceLength
      omega

/-- Close this concrete Cell-skip program at its actual done/halt block. -/
theorem close_run (source : List State) (before : State) (suffix archive : List Bool)
    (other : Stack → List Bool) (store : Store) (limit : ℕ)
    (head : source.head? = some before)
    (chain : source.IsChain (fun a b => TM2.step program a = some b))
    (last : source.getLast? = some (state (some doneLabel) store suffix [] archive other))
    (length : source.length ≤ limit) :
    ∃ (run : List State) (after : State),
      run.head? = some before ∧
      run.IsChain (fun a b => TM2.step program a = some b) ∧
      run.getLast? = some after ∧ TM2.step program after = none ∧
      after.l = none ∧ after.var = store ∧ after.stk = slots suffix [] archive other ∧
      run.length ≤ limit + 1 := by
  let after := state none store suffix [] archive other
  let run := source ++ [after]
  have actual : run.IsChain (fun a b => TM2.step program a = some b) := by
    apply chain.append (List.isChain_singleton _)
    intro old ho next hn
    simp only [last, Option.mem_some_iff] at ho
    simp only [List.head?_cons, Option.mem_some_iff] at hn
    subst old
    subst next
    exact done_halt suffix [] archive other store
  refine ⟨run, after, ?_, actual, ?_, halted suffix [] archive other store,
    rfl, rfl, rfl, ?_⟩
  · change (source ++ [after]).head? = some before
    simp only [List.head?_append, head, Option.some_or]
  · exact List.getLast?_append_cons source after []
  · simp only [run, List.length_append, List.length_cons, List.length_nil]
    omega

theorem natural_skip_runs (value : ℕ) (suffix archive : List Bool) (other : Stack → List Bool) (store : Store) :
    ∃ (run : List State) (after : State),
      run.head? = some (state (some startLabel) store
        (encodeCellBits (.natural value) ++ suffix) [] archive other) ∧
      run.IsChain (fun a b => TM2.step program a = some b) ∧
      run.getLast? = some after ∧ TM2.step program after = none ∧
      after.l = none ∧ after.var = (none, store.2) ∧
      after.stk = slots suffix [] ((encodeCellBits (.natural value)).reverse ++ archive) other ∧
      run.length ≤ (encodeCellBits (.natural value)).length + 6 := by
  let innerStore := Query.setRecord store (some false)
  obtain ⟨part, partHead, partChain, partLast, partLength⟩ :=
    header_return_run naturalLabel doneLabel (by intro label; rfl)
      value suffix (false :: archive) other innerStore
  let before := state (some startLabel) store (encodeCellBits (.natural value) ++ suffix) [] archive other
  let source := before :: part
  have sourceHead : source.head? = some before := rfl
  have sourceChain : source.IsChain (fun a b => TM2.step program a = some b) := by
    apply List.IsChain.cons partChain
    intro next hn
    rw [partHead] at hn
    have equal := Option.mem_some_iff.mp hn
    subst next
    exact tag_false (encodeNatBits value ++ suffix) [] archive other store
  have archiveEq : (encodeNatBits value).reverse ++ false :: archive =
      (encodeCellBits (.natural value)).reverse ++ archive := by
    simp [encodeCellBits, List.reverse_cons, List.append_assoc]
  have sourceLast : source.getLast? = some (state (some doneLabel) (none, store.2)
      suffix [] ((encodeCellBits (.natural value)).reverse ++ archive) other) := by
    simp only [source, List.getLast?_cons, partLast, Option.getD_some, archiveEq]
    rfl
  have sourceLength : source.length ≤ (encodeCellBits (.natural value)).length + 5 := by
    simp only [source, List.length_cons, partLength, encodeCellBits, List.length_cons, Log.nat_word_length]
    omega
  exact close_run source before suffix ((encodeCellBits (.natural value)).reverse ++ archive)
    other (none, store.2) ((encodeCellBits (.natural value)).length + 5)
    sourceHead sourceChain sourceLast sourceLength

end PDROC.BitVM.Log.CellSkip

namespace PDROC.BitVM.Log.CellSkip

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters

theorem rational_skip_runs (value : ℚ) (suffix archive : List Bool) (other : Stack → List Bool) (store : Store) :
    ∃ (run : List State) (after : State),
      run.head? = some (state (some startLabel) store
        (encodeCellBits (.rational value) ++ suffix) [] archive other) ∧
      run.IsChain (fun a b => TM2.step program a = some b) ∧
      run.getLast? = some after ∧ TM2.step program after = none ∧
      after.l = none ∧ after.var = (none, store.2) ∧
      after.stk = slots suffix [] ((encodeCellBits (.rational value)).reverse ++ archive) other ∧
      run.length ≤ (encodeCellBits (.rational value)).length + 6 := by
  let sign : Bool := decide (value < 0)
  let tagStore := Query.setRecord store (some true)
  let signStore := Query.setRecord tagStore (some sign)
  let numWord := encodeNatBits value.num.natAbs
  let denWord := encodeNatBits value.den
  let numArchive := numWord.reverse ++ sign :: true :: archive
  obtain ⟨numTrace, numHead, numChain, numLast, numLength⟩ :=
    header_return_run numeratorLabel (denominatorLabel 0) (by intro label; rfl)
      value.num.natAbs (denWord ++ suffix) (sign :: true :: archive) other signStore
  obtain ⟨denTrace, denHead, denChain, denLast, denLength⟩ :=
    header_return_run denominatorLabel doneLabel (by intro label; rfl)
      value.den suffix numArchive other (none, store.2)
  let before := state (some startLabel) store (encodeCellBits (.rational value) ++ suffix) [] archive other
  let beforeSign := state (some signLabel) tagStore (sign :: (numWord ++ (denWord ++ suffix)))
    [] (true :: archive) other
  let leadTrace := before :: beforeSign :: numTrace
  have leadHead : leadTrace.head? = some before := rfl
  have leadChain : leadTrace.IsChain (fun a b => TM2.step program a = some b) := by
    apply List.isChain_cons_cons.mpr
    constructor
    · simpa only [before, beforeSign, encodeCellBits, sign, numWord, denWord,
        List.cons_append, List.nil_append, List.append_assoc] using
        tag_true (sign :: (numWord ++ (denWord ++ suffix))) [] archive other store
    · apply List.IsChain.cons numChain
      intro next hn
      rw [numHead] at hn
      have equal := Option.mem_some_iff.mp hn
      subst next
      exact sign_bit sign (numWord ++ (denWord ++ suffix)) [] (true :: archive) other tagStore
  let middle := state (some (denominatorLabel 0)) (none, store.2) (denWord ++ suffix) [] numArchive other
  have leadLast : leadTrace.getLast? = some middle := by
    simp only [leadTrace, List.getLast?_cons, numLast, Option.getD_some]
    rfl
  have leadLength : leadTrace.length = 2 + numTrace.length := by
    simp only [leadTrace, List.length_cons]; omega
  let joined := leadTrace ++ denTrace.tail
  have joinedHead : joined.head? = some before := by
    simp only [joined, List.head?_append, leadHead, Option.some_or]
  have joinedChain : joined.IsChain (fun a b => TM2.step program a = some b) :=
    TwoStack.join_chain leadTrace denTrace middle leadChain denChain leadLast denHead
  have denNotOne : denTrace.length ≠ 1 := by omega
  have archiveEq : (encodeNatBits value.den).reverse ++ numArchive =
      (encodeCellBits (.rational value)).reverse ++ archive := by
    simp [numArchive, numWord, sign, encodeCellBits, List.reverse_append, List.append_assoc]
  have joinedLast : joined.getLast? = some (state (some doneLabel) (none, store.2)
      suffix [] ((encodeCellBits (.rational value)).reverse ++ archive) other) := by
    simp only [joined, List.getLast?_append, List.getLast?_tail, denNotOne, ↓reduceIte,
      denLast, archiveEq, Option.some_or]
  have joinedLength : joined.length ≤ (encodeCellBits (.rational value)).length + 5 := by
    simp only [joined, List.length_append, List.length_tail, leadLength, numLength]
    simp only [encodeCellBits, List.length_append, List.length_cons, List.length_nil, Log.nat_word_length]
    omega
  exact close_run joined before suffix ((encodeCellBits (.rational value)).reverse ++ archive)
    other (none, store.2) ((encodeCellBits (.rational value)).length + 5)
    joinedHead joinedChain joinedLast joinedLength

/-- All Cell fields are skipped by real tag/sign reads and one/two actual
canonical Nat scans. No Cell decoder or heap answer is a transition oracle. -/
theorem skip_runs (value : Cell) (suffix archive : List Bool) (other : Stack → List Bool) (store : Store) :
    ∃ (run : List State) (after : State),
      run.head? = some (state (some startLabel) store (encodeCellBits value ++ suffix) [] archive other) ∧
      run.IsChain (fun a b => TM2.step program a = some b) ∧
      run.getLast? = some after ∧ TM2.step program after = none ∧
      after.l = none ∧ after.var = (none, store.2) ∧
      after.stk = slots suffix [] ((encodeCellBits value).reverse ++ archive) other ∧
      run.length ≤ (encodeCellBits value).length + 6 := by
  cases value with
  | natural value => exact natural_skip_runs value suffix archive other store
  | rational value => exact rational_skip_runs value suffix archive other store

end PDROC.BitVM.Log.CellSkip
