module

public import Paid.RootD27Core_InputCopyTrace_021
public import Paid.RootD27Core_HeapOutput_014

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

/-- The original prepared-ROM core really produces its live heap before
the shared heap-reading engine. All39 copy instructions are charged. -/
def preparedHeapEndpointProgram (continuation : List Instruction) : Program :=
  (inputCopyCode 13++(endpointHeapOutputCode 39 48 96 302++continuation)).toArray

theorem prepared_heap_endpoint_budget (m : ℕ) : 795+7700*(m+1)≤8500*(m+1) := by omega

theorem original_prepared_heap_endpoint_output (continuation : List Instruction)
    (P : Parameters) (fee : ℚ) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some initial ∧ trace.getLast?=some after ∧
      trace.IsChain (fun before later =>
        step (preparedHeapEndpointProgram continuation) (preparedInput P fee) before=some later) ∧
      time (preparedHeapEndpointProgram continuation) trace≤8500*(P.certificate.M+1) ∧
      after.pc=302 ∧ HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) ∧
      HeapList after 0 (preparedInput P fee) ∧ after.output=encodeList encodeEndpoint P.endpointCache.toList := by
  let program:=preparedHeapEndpointProgram continuation
  have literal:=arrayLiteral_fetch (inputCopyCode 13++(endpointHeapOutputCode 39 48 96 302++continuation))
  have copyFetch : FetchesCode program initial.pc (inputCopyCode 13) := literal.append_left
  obtain ⟨copied,ch,cl,cc,ct,_⟩:=inputCopy_actual program (preparedInput P fee) initial 13
    (by change 13≤13;decide) copyFetch
  let middle:=inputCopyResult (preparedInput P fee) initial 13
  have middlePC : middle.pc=39 := by rw [inputCopy_pc];rfl
  have prepared : HeapList middle 0 (preparedInput P fee) := by
    have full : (preparedInput P fee).take 13=preparedInput P fee := by
      apply List.take_of_length_le
      change 13≤13
      decide
    simpa only [full] using inputCopy_heapList (preparedInput P fee) initial 13
  have endpointFetch : FetchesCode program middle.pc (endpointHeapOutputCode middle.pc 48 96 302) := by
    rw [middlePC]
    simpa only [program,preparedHeapEndpointProgram,inputCopy_length,Nat.zero_add,
      show 3*13=39 from rfl] using literal.append_right.append_left
  obtain ⟨endpointTrace,after,eh,el,ec,et,position,cache,retained,output⟩:=
    endpoint_heap_output_actual P fee (preparedInput P fee) program middle 48 96 302
      prepared (by decide) (by decide) endpointFetch
  have copyCost : time program copied≤795 := ct
  have joined:=joinTrace_spec program (preparedInput P fee) copied endpointTrace initial middle after
    795 (7700*(P.certificate.M+1)) ch cl eh el cc ec copyCost et
  refine ⟨joinTrace copied endpointTrace,after,joined.1,joined.2.1,joined.2.2.1,
    joined.2.2.2.trans (prepared_heap_endpoint_budget P.certificate.M),position,cache,retained,?_⟩
  have empty : middle.output=[] := inputCopy_output (preparedInput P fee) initial 13
  simpa only [empty,List.nil_append] using output

end RootD27.Core
