module
public import Paid.PDCompute_Pack_CounterTrace_014

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

/-- Six actual instructions copy a header counter for each new row. -/
theorem copy_trace (program : Program) (input : List Cell) (before : State)
    (base source target : ℕ) (values : ℕ → Cell) (header : Header before base values)
    (sourceInside : source<headerWords) (targetInside : target<headerWords)
    (hbase : before.register .fresh=.natural base)
    (fetched : FetchesCode program before.pc (copySlot source target)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (copySlotResult before base source target) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 105 ∧
      Header (copySlotResult before base source target) base (Function.update values target (values source)) ∧
      (copySlotResult before base source target).register .fresh=.natural base ∧
      (copySlotResult before base source target).pc=before.pc+6 ∧
      (copySlotResult before base source target).output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base := by
  have valid : (HeaderCommand.copy source target).Valid:=⟨sourceInside,targetInside⟩
  have eval : (HeaderCommand.copy source target).eval values=some (Function.update values target (values source)):=rfl
  obtain ⟨trace,hh,hl,hchain,ht,memory⟩:=linearExecute_trace_memory program input (copySlot source target)
    (copySlot_straight source target) before _ base fetched
    (copySlot_execute input before base source target hbase (header.live source sourceInside))
    (fun count bound state run=>(HeaderCommand.copy source target).prefix_memory input before state base values _
      valid header hbase eval count bound run)
  have fields:=copySlotResult_fields before base source target
  exact ⟨trace,hh,hl,hchain,ht,header.copySlot source target sourceInside,
    fields.2.2.1.trans hbase,fields.2.2.2.1,fields.2.2.2.2,memory⟩

end PDCompute.Pack
