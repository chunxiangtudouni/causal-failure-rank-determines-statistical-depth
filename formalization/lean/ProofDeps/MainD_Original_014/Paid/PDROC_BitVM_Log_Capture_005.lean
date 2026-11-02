module

public import Paid.PDROC_BitVM_Log_Capture_004
public import Paid.PDROC_BitVM_Log_Header_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Log.Capture

open Turing

def scanTrace (digits suffix archive captured : List Bool) (other : Stack → List Bool) (store : Store) : List State :=
  headerTrace other digits.length (digits ++ suffix) [] archive captured store ++
    (payloadTrace other digits suffix
      (false :: (List.replicate digits.length true ++ archive))
      (false :: (List.replicate digits.length true ++ captured))
      (Query.setRecord store (some false))).tail

theorem scan_trace_head (digits suffix archive captured : List Bool)
    (other : Stack → List Bool) (store : Store) :
    (scanTrace digits suffix archive captured other store).head? =
      some (state (some 0) store (Header.natWord digits ++ suffix) [] archive captured other) := by
  simp only [scanTrace, List.head?_append, headerTrace_head, Option.some_or,
    Header.natWord, List.append_assoc, List.cons_append]

theorem scan_trace_last (digits suffix archive captured : List Bool)
    (other : Stack → List Bool) (store : Store) :
    (scanTrace digits suffix archive captured other store).getLast? =
      some (state (some 2) (Query.setRecord store none) suffix []
        ((Header.natWord digits).reverse ++ archive)
        ((Header.natWord digits).reverse ++ captured) other) := by
  have notOne : (payloadTrace other digits suffix
      (false :: (List.replicate digits.length true ++ archive))
      (false :: (List.replicate digits.length true ++ captured))
      (Query.setRecord store (some false))).length ≠ 1 := by
    rw [payloadTrace_length]; omega
  simp only [scanTrace, List.getLast?_append, List.getLast?_tail, notOne, ↓reduceIte,
    payloadTrace_last, Header.archive_word, record_replace, Option.some_or]

theorem scan_trace_chain (digits suffix archive captured : List Bool)
    (other : Stack → List Bool) (store : Store) :
    (scanTrace digits suffix archive captured other store).IsChain
      (fun before after => TM2.step program before = some after) := by
  apply TwoStack.join_chain _ _
    (state (some 1) (Query.setRecord store (some false)) (digits ++ suffix)
      (List.replicate digits.length true)
      (false :: (List.replicate digits.length true ++ archive))
      (false :: (List.replicate digits.length true ++ captured)) other)
  · exact headerTrace_chain digits.length (digits ++ suffix) [] archive captured other store
  · exact payloadTrace_chain digits suffix
      (false :: (List.replicate digits.length true ++ archive))
      (false :: (List.replicate digits.length true ++ captured)) other
      (Query.setRecord store (some false))
  · simp only [headerTrace_last, List.append_nil]
  · exact payloadTrace_head digits suffix
      (false :: (List.replicate digits.length true ++ archive))
      (false :: (List.replicate digits.length true ++ captured)) other
      (Query.setRecord store (some false))

theorem scan_trace_length (digits suffix archive captured : List Bool)
    (other : Stack → List Bool) (store : Store) :
    (scanTrace digits suffix archive captured other store).length = 2 * digits.length + 3 := by
  simp only [scanTrace, List.length_append, List.length_tail, headerTrace_length, payloadTrace_length]
  omega

end PDROC.BitVM.Log.Capture
