module
public import Paid.PDCompute_Pack_SmallBits_060
public import Paid.PDCompute_Pack_CopyTrace_039

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDCompute.Solver PDMenu.ComputeFrame

theorem copy_trace_safe (program : Program) (input : List Cell) (before : State)
    (base source target budget : ℕ) (values : ℕ → Cell) (header : Header before base values)
    (sourceInside : source<headerWords) (targetInside : target<headerWords)
    (fresh : before.register .fresh=.natural base) (safe : SafeBits before budget)
    (sourceBits : 1+natBits (base+source) ≤ budget) (targetBits : 1+natBits (base+target) ≤ budget)
    (counter : natBits (before.pc+6) ≤ budget) (fetched : FetchesCode program before.pc (copySlot source target)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (copySlotResult before base source target) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 105 ∧
      Header (copySlotResult before base source target) base (Function.update values target (values source)) ∧
      (copySlotResult before base source target).register .fresh=.natural base ∧
      (copySlotResult before base source target).pc=before.pc+6 ∧
      (copySlotResult before base source target).output=before.output ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,SafeBits state budget) := by
  have valid : (HeaderCommand.copy source target).Valid:=⟨sourceInside,targetInside⟩
  have eval : (HeaderCommand.copy source target).eval values=some (Function.update values target (values source)):=rfl
  have run:=copySlot_execute input before base source target fresh (header.live source sourceInside)
  obtain ⟨trace,hh,hl,hchain,ht,invariant⟩:=linearExecute_trace_invariant program input (copySlot source target)
    (copySlot_straight source target) before _ fetched run (fun state=>HeaderMemory before state base ∧ SafeBits state budget) (by
      intro count bound state executed
      have countBound : count ≤ 6:=by simpa only [copySlot_length] using bound
      exact ⟨(HeaderCommand.copy source target).prefix_memory input before state base values _ valid header fresh eval count bound executed,
        copy_prefix_safe input before state base source target budget count safe fresh (header.live source sourceInside)
          sourceBits targetBits counter countBound executed⟩)
  have fields:=copySlotResult_fields before base source target
  refine ⟨trace,hh,hl,hchain,?_,header.copySlot source target sourceInside,fields.2.2.1.trans fresh,
    fields.2.2.2.1,fields.2.2.2.2,fun state member=>(invariant state member).1,fun state member=>(invariant state member).2⟩
  simpa only [copySlot_length] using ht

end PDCompute.Pack
