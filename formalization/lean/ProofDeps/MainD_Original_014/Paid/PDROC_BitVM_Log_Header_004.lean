module

public import Paid.PDROC_BitVM_Log_Header_003
public import Paid.PDROC_BitVM_Log_TM2_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Log.Header

open Turing

def natWord (digits : List Bool) : List Bool :=
  List.replicate digits.length true ++ false :: digits

def scanTrace (digits suffix archive : List Bool) (store : Store) : List State :=
  headerTrace digits.length (digits ++ suffix) [] archive store ++
    (payloadTrace digits suffix (false :: (List.replicate digits.length true ++ archive))
      (some false)).tail

theorem archive_word (digits archive : List Bool) :
    digits.reverse ++ false :: (List.replicate digits.length true ++ archive) =
      (natWord digits).reverse ++ archive := by
  simp [natWord, List.reverse_append, List.append_assoc]

theorem scan_trace_head (digits suffix archive : List Bool) (store : Store) :
    (scanTrace digits suffix archive store).head? =
      some (state (some 0) store (natWord digits ++ suffix) [] archive) := by
  simp only [scanTrace, List.head?_append, headerTrace_head, Option.some_or,
    natWord, List.append_assoc, List.cons_append]

theorem scan_trace_last (digits suffix archive : List Bool) (store : Store) :
    (scanTrace digits suffix archive store).getLast? =
      some (state (some 2) none suffix [] ((natWord digits).reverse ++ archive)) := by
  have notOne : (payloadTrace digits suffix
      (false :: (List.replicate digits.length true ++ archive)) (some false)).length ≠ 1 := by
    rw [payloadTrace_length]; omega
  simp only [scanTrace, List.getLast?_append, List.getLast?_tail, notOne,
    ↓reduceIte, payloadTrace_last, archive_word, Option.some_or]

theorem scan_trace_chain (digits suffix archive : List Bool) (store : Store) :
    (scanTrace digits suffix archive store).IsChain
      (fun before after => TM2.step program before = some after) := by
  apply TwoStack.join_chain _ _
    (state (some 1) (some false) (digits ++ suffix) (List.replicate digits.length true)
      (false :: (List.replicate digits.length true ++ archive)))
  · exact headerTrace_chain digits.length (digits ++ suffix) [] archive store
  · exact payloadTrace_chain digits suffix
      (false :: (List.replicate digits.length true ++ archive)) (some false)
  · simp only [headerTrace_last, List.append_nil]
  · exact payloadTrace_head digits suffix
      (false :: (List.replicate digits.length true ++ archive)) (some false)

theorem scan_trace_length (digits suffix archive : List Bool) (store : Store) :
    (scanTrace digits suffix archive store).length = 2 * digits.length + 3 := by
  simp only [scanTrace, List.length_append, List.length_tail, headerTrace_length,
    payloadTrace_length]
  omega

def final (digits suffix archive : List Bool) : State :=
  state none none suffix [] ((natWord digits).reverse ++ archive)

def fullTrace (digits suffix archive : List Bool) (store : Store) : List State :=
  scanTrace digits suffix archive store ++ [final digits suffix archive]

theorem full_trace_head (digits suffix archive : List Bool) (store : Store) :
    (fullTrace digits suffix archive store).head? =
      some (state (some 0) store (natWord digits ++ suffix) [] archive) := by
  simp only [fullTrace, List.head?_append, scan_trace_head, Option.some_or]

theorem full_trace_last (digits suffix archive : List Bool) (store : Store) :
    (fullTrace digits suffix archive store).getLast? = some (final digits suffix archive) := by
  simp [fullTrace]

theorem full_trace_chain (digits suffix archive : List Bool) (store : Store) :
    (fullTrace digits suffix archive store).IsChain
      (fun before after => TM2.step program before = some after) := by
  apply (scan_trace_chain digits suffix archive store).append (List.isChain_singleton _)
  intro before hb after ha
  simp only [scan_trace_last, Option.mem_some_iff] at hb
  simp only [List.head?_cons, Option.mem_some_iff] at ha
  subst before
  subst after
  exact return_halt suffix ((natWord digits).reverse ++ archive)

theorem full_trace_length (digits suffix archive : List Bool) (store : Store) :
    (fullTrace digits suffix archive store).length = 2 * digits.length + 4 := by
  simp [fullTrace, scan_trace_length, Nat.add_assoc]

/-- One selected real trace, including the literal final halt instruction. -/
theorem scan_runs (digits suffix archive : List Bool) (store : Store) :
    ∃ run : List State,
      run.head? = some (state (some 0) store (natWord digits ++ suffix) [] archive) ∧
      run.IsChain (fun before after => TM2.step program before = some after) ∧
      run.getLast? = some (final digits suffix archive) ∧
      TM2.step program (final digits suffix archive) = none ∧
      run.length = 2 * digits.length + 4 ∧
      (final digits suffix archive).stk 0 = suffix ∧
      (final digits suffix archive).stk 1 = [] ∧
      (final digits suffix archive).stk 2 = (natWord digits).reverse ++ archive := by
  exact ⟨fullTrace digits suffix archive store, full_trace_head digits suffix archive store,
    full_trace_chain digits suffix archive store, full_trace_last digits suffix archive store,
    halted suffix ((natWord digits).reverse ++ archive), full_trace_length digits suffix archive store,
    by simp [final, state, slots, TwoStack.stackContents],
    by simp [final, state, slots, TwoStack.stackContents],
    by simp [final, state, slots, TwoStack.stackContents]⟩

end PDROC.BitVM.Log.Header
