module

public import Common.PSTR_WordBool_RatInputBank_089

/-! One actual encoder run, starting from the existing finite rational
packet and ending at the exact original pair-codec input on physical13. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatInput.Encoder

open Turing PSTRWordVM RationalControllerComputation

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

theorem actual_encode_fields (caller : Statement C) (background : RatInput.Stack→List Bool)
    (context : C) (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (negative : Bool) (num den source scratch : List Bool) :
    ∃ trace : List (State C),
      trace.head?=some ⟨some (.collect 0),((context,memory),formatter),
        bank background (PSTRSymbolicRatExport.packet negative num den source) scratch [] [] [] [] [] [] []⟩ ∧
      trace.IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
      trace.getLast?=some ⟨some .done,
        ((context,(PSTRSymbolicNaturalExport.finalBit (RatOutput.outputLeft negative num den) false,true,negative)),(false,false)),
        bank background (PSTRSymbolicRatExport.packet negative num den source) scratch [] [] [] []
          (prefixBits++true::negative::(encodeNat (PSTRTMIncrement009.valueDigits num)++
            encodeNat (PSTRTMIncrement009.valueDigits den)++[true])) [] []⟩ ∧
      trace.length≤8*(num.length+den.length)+34 := by
  let packet:=PSTRSymbolicRatExport.packet negative num den source
  let rat:RatInput.Store:=(PSTRSymbolicNaturalExport.finalBit (RatOutput.outputLeft negative num den) false,true,negative)
  let encN:=encodeNat (PSTRTMIncrement009.valueDigits num)
  let encD:=encodeNat (PSTRTMIncrement009.valueDigits den)
  let b0:=bank background packet scratch [] [] [] [] [] [] []
  let b1:=bank background packet scratch num.reverse den.reverse [] [] [true] [] []
  let b2:=bank background packet scratch [] den.reverse num [] [true] [] []
  let b3:=bank background packet scratch [] [] num den [true] [] []
  let b4:=bank background packet scratch [] [] num [] (encD++[true]) [] []
  let b5:=bank background packet scratch [] [] [] [] (encN++encD++[true]) [] []
  let b6:=bank background packet scratch [] [] [] [] (prefixBits++true::negative::(encN++encD++[true])) [] []
  let s0:State C:=⟨some (.collect 0),((context,memory),formatter),b0⟩
  let s1:State C:=⟨some .reverseNum,((context,rat),formatter),b1⟩
  let s2:State C:=⟨some .reverseDen,((context,rat),(false,false)),b2⟩
  let s3:State C:=⟨some (.den 0),((context,rat),(false,false)),b3⟩
  let s4:State C:=⟨some (.num 0),((context,rat),(false,false)),b4⟩
  let s5:State C:=⟨some .finish,((context,rat),(false,false)),b5⟩
  let s6:State C:=⟨some .done,((context,rat),(false,false)),b6⟩
  obtain ⟨t0,h0,c0,l0,n0⟩:=actual_collect_bank caller background context memory formatter negative num den source scratch [] [] [] [] []
  let p0:Path caller s0 s1 (3*(num.length+den.length)+11):=⟨t0,h0,c0,l0,n0⟩
  obtain ⟨t1,h1,c1,l1,n1⟩:=actual_reverse caller false b1 ((context,rat),formatter)
  have last1 : t1.getLast?=some s2 := by
    simpa [b1,s2,b2,reverse_num_bank,reverseSource,reverseTarget,reverseReturn,bank,
      List.reverse_reverse,List.append_nil] using l1
  let p1:Path caller s1 s2 (num.length+2):=⟨t1,h1,c1,last1,by simpa [b1,reverseSource,bank] using n1.le⟩
  obtain ⟨t2,h2,c2,l2,n2⟩:=actual_reverse caller true b2 ((context,rat),(false,false))
  have last2 : t2.getLast?=some s3 := by
    simpa [b2,s3,b3,reverse_den_bank,reverseSource,reverseTarget,reverseReturn,bank,
      List.reverse_reverse,List.append_nil] using l2
  let p2:Path caller s2 s3 (den.length+2):=⟨t2,h2,c2,last2,by simpa [b2,reverseSource,bank] using n2.le⟩
  obtain ⟨t3,h3,c3,l3,n3⟩:=actual_format caller true b3 ((context,rat),(false,false)) rfl rfl
  have last3 : t3.getLast?=some s4 := by
    simpa [b3,s4,b4,encD,format_den_bank,reverseTarget,formatReturn,bank] using l3
  let p3:Path caller s3 s4 (4*den.length+11):=⟨t3,h3,c3,last3,by simpa [b3,reverseTarget,bank] using n3⟩
  obtain ⟨t4,h4,c4,l4,n4⟩:=actual_format caller false b4 ((context,rat),(false,false)) rfl rfl
  have last4 : t4.getLast?=some s5 := by
    simpa [b4,s5,b5,encN,format_num_bank,reverseTarget,formatReturn,bank,List.append_assoc] using l4
  let p4:Path caller s4 s5 (4*num.length+11):=⟨t4,h4,c4,last4,by simpa [b4,reverseTarget,bank] using n4⟩
  have finish : TM2.step (program caller) s5=some s6 := by
    simpa [s5,s6,b5,b6,bank_update_raw,bank,PSTRSymbolicNaturalExport.positive,rat] using
      finish_step caller ((context,rat),(false,false)) b5
  let p5:Path caller s5 s6 2:=⟨[s5,s6],rfl,List.isChain_cons_cons.mpr ⟨finish,List.isChain_singleton _⟩,rfl,Nat.le_refl _⟩
  let whole:=((((p0.append p1).append p2).append p3).append p4).append p5
  refine ⟨whole.trace,whole.head,whole.chain,whole.last,?_⟩
  have count:=whole.count
  omega

theorem actual_encode_pair (caller : Statement C) (background : RatInput.Stack→List Bool)
    (context : C) (memory : RatInput.Store) (formatter : WordNatIO.Store) (p : Rat) (source scratch : List Bool) :
    ∃ trace : List (State C),
      trace.head?=some ⟨some (.collect 0),((context,memory),formatter),
        bank background (PSTRSymbolicRatExport.packet (PA17TMRatArithmeticParse002.sign p)
          (PA17TMRatArithmeticParse002.numeratorDigits p) (PA17TMRatArithmeticParse002.denominatorDigits p) source)
          scratch [] [] [] [] [] [] []⟩ ∧
      trace.IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
      ∃ final,
        trace.getLast?=some final ∧ final.l=some .done ∧ final.var.1.1=context ∧
        final.stk=bank background (PSTRSymbolicRatExport.packet (PA17TMRatArithmeticParse002.sign p)
          (PA17TMRatArithmeticParse002.numeratorDigits p) (PA17TMRatArithmeticParse002.denominatorDigits p) source)
          scratch [] [] [] [] (encode [.rational 1,.rational p]) [] [] ∧
        trace.length≤8*((PA17TMRatArithmeticParse002.numeratorDigits p).length+
          (PA17TMRatArithmeticParse002.denominatorDigits p).length)+34 := by
  obtain ⟨trace,first,chain,last,count⟩:=actual_encode_fields caller background context memory formatter
    (PA17TMRatArithmeticParse002.sign p) (PA17TMRatArithmeticParse002.numeratorDigits p)
    (PA17TMRatArithmeticParse002.denominatorDigits p) source scratch
  refine ⟨trace,first,chain,_,last,rfl,rfl,?_,count⟩
  have encoded : prefixBits++true::PA17TMRatArithmeticParse002.sign p::
      (encodeNat (PSTRTMIncrement009.valueDigits (PA17TMRatArithmeticParse002.numeratorDigits p))++
        encodeNat (PSTRTMIncrement009.valueDigits (PA17TMRatArithmeticParse002.denominatorDigits p))++[true])=
      encode [.rational 1,.rational p] := by
    rw [PA17TMRatArithmeticParse002.numeratorDigits_value,PA17TMRatArithmeticParse002.denominatorDigits_value]
    simp only [prefixBits,encode,encodeDatum,List.length_cons,List.length_nil,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.append_assoc,PA17TMRatArithmeticParse002.sign]
    rfl
  rw [encoded]

end PaperProofs.Common.Native.PSTRWordBool.RatInput.Encoder

