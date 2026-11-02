module

public import PSTR_WordBool_WordOutput_Paths_001

/-! The SAME actual packet copy/restore, Bool-tail pushes, formatter run,
constant-prefix replacement, and unexecuted final caller port. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.WordOutput

open Turing PSTRWordVM RationalControllerComputation PA17TMRatArithmeticParse002

variable {C : Type*}

structure Path (caller : Statement C) (before final : State C) (budget : Nat) where
  trace : List (State C)
  head : trace.head?=some before
  chain : trace.IsChain (fun a b=>TM2.step (program caller) a=some b)
  last : trace.getLast?=some final
  count : trace.length≤budget

def Path.append {caller : Statement C} {before middle final : State C} {frontBudget backBudget : Nat}
    (front : Path caller before middle frontBudget) (back : Path caller middle final backBudget) :
    Path caller before final (frontBudget+backBudget-1) := by
  have shape : middle::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp back.head
    rw [same];rfl
  have size:=congrArg List.length shape
  simp only [List.length_cons] at size
  refine ⟨front.trace++back.trace.tail,?_,?_,?_,?_⟩
  · rw [List.head?_append,front.head];rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)
  · have first:=front.count;have second:=back.count
    simp only [List.length_append]
    omega

theorem actual_fields (caller : Statement C) (background : Stack → List Bool) (context : C) (hit map : Bool)
    (memory : RatInput.Store) (formatter : WordNatIO.Store) (negative : Bool)
    (num den source scratch : List Bool) :
    ∃ trace : List (State C),
      trace.head?=some ⟨some (.collect (.collect 0)),(((context,hit,map),memory),formatter),
        RatInput.Encoder.bank background (PSTRSymbolicRatExport.packet negative num den source) scratch [] [] [] [] [] [] []⟩ ∧
      trace.IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
      trace.getLast?=some ⟨some .done,
        (((context,hit,map),(PSTRSymbolicNaturalExport.finalBit (RatOutput.outputLeft negative num den) false,true,negative)),(false,false)),
        RatInput.Encoder.bank background (PSTRSymbolicRatExport.packet negative num den source) scratch [] [] [] []
          (output negative num den hit map) [] []⟩ ∧
      trace.length≤8*(num.length+den.length)+40 := by
  let packet:=PSTRSymbolicRatExport.packet negative num den source
  let rat:RatInput.Store:=(PSTRSymbolicNaturalExport.finalBit (RatOutput.outputLeft negative num den) false,true,negative)
  let b0:=RatInput.Encoder.bank background packet scratch [] [] [] [] [] [] []
  let b1:=RatInput.Encoder.bank background packet scratch num.reverse den.reverse [] [] [true] [] []
  let b2:=RatInput.Encoder.bank background packet scratch num.reverse den.reverse [] [] (boolTail hit map) [] []
  let raw:=true::negative::(encodeNat (PSTRTMIncrement009.valueDigits num)++
    encodeNat (PSTRTMIncrement009.valueDigits den)++boolTail hit map)
  let b3:=RatInput.Encoder.bank background packet scratch [] [] [] [] (RatInput.Encoder.prefixBits++raw) [] []
  let b4:=RatInput.Encoder.bank background packet scratch [] [] [] [] (output negative num den hit map) [] []
  let s0:State C:=⟨some (.collect (.collect 0)),(((context,hit,map),memory),formatter),b0⟩
  let s1:State C:=⟨some .prepare,(((context,hit,map),rat),formatter),b1⟩
  let s2:State C:=⟨some (.suffix .reverseNum),(((context,hit,map),rat),formatter),b2⟩
  let s3:State C:=⟨some .trim,(((context,hit,map),rat),(false,false)),b3⟩
  let s4:State C:=⟨some .done,(((context,hit,map),rat),(false,false)),b4⟩
  obtain ⟨t0,h0,c0,l0,n0⟩:=actual_collect caller background context hit map memory formatter negative num den source scratch
  let p0:Path caller s0 s1 (3*(num.length+den.length)+11):=⟨t0,h0,c0,l0,n0⟩
  have prep : TM2.step (program caller) s1=some s2:=
    prepare_step caller background context hit map rat formatter packet scratch num.reverse den.reverse
  let p1:Path caller s1 s2 2:=⟨[s1,s2],rfl,List.isChain_cons_cons.mpr ⟨prep,List.isChain_singleton _⟩,rfl,Nat.le_refl _⟩
  obtain ⟨t2,h2,c2,l2,n2⟩:=actual_suffix caller background context hit map rat.1 rat.2.1 negative formatter
    num den packet scratch (boolTail hit map)
  let p2:Path caller s2 s3 (5*(num.length+den.length)+24):=⟨t2,h2,c2,l2,n2⟩
  have trim : TM2.step (program caller) s3=some s4 := by
    have equal : b3=Function.update b3 13 (RatInput.Encoder.prefixBits++raw):=by
      rw [RatInput.Encoder.bank_update_raw]
    rw [show s3=⟨some .trim,(((context,hit,map),rat),(false,false)),Function.update b3 13 (RatInput.Encoder.prefixBits++raw)⟩ from
      congrArg (fun contents=>(⟨some .trim,(((context,hit,map),rat),(false,false)),contents⟩:State C)) equal]
    rw [trim_step,RatInput.Encoder.bank_update_raw]
    rfl
  let p3:Path caller s3 s4 2:=⟨[s3,s4],rfl,List.isChain_cons_cons.mpr ⟨trim,List.isChain_singleton _⟩,rfl,Nat.le_refl _⟩
  let whole:=((p0.append p1).append p2).append p3
  refine ⟨whole.trace,whole.head,whole.chain,whole.last,?_⟩
  have count:=whole.count
  omega

theorem output_original (r : Rat) (hit map : Bool) :
    output (sign r) (numeratorDigits r) (denominatorDigits r) hit map=
      encode [.rational r,boolDatum hit,boolDatum map] := by
  unfold output
  rw [numeratorDigits_value,denominatorDigits_value]
  simp only [encode,encodeDatum,boolTail,List.length_cons,List.length_nil,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.append_assoc,List.cons_append,List.nil_append,sign]

end PaperProofs.Common.Native.PSTRWordBool.WordOutput
