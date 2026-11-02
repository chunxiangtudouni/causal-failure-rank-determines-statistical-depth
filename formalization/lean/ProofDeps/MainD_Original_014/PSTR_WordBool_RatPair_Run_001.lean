module

public import PSTR_WordBool_RatPair_Link_001

/-! Same actual trace from the two existing packets to original-codec
fields, preserving the whole source and old7 through the paid join. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatPair.Link

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

theorem actual_fields (caller : Statement C) (background : Stack → List Bool) (context : C)
    (oldX oldY : Bool) (memory : RatInput.Store) (formatter : WordNatIO.Store) (sx sy : Bool)
    (xn xd yn yd tail scratch : List Bool) :
    ∃ (trace : List (State C)) (final : State C),
      trace.head?=some (entry background context oldX oldY memory formatter sx sy xn xd yn yd tail scratch) ∧
      trace.IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some done ∧ final.var.1.1=(context,sx,sy) ∧
      final.stk=finalContents background (Collector.packets sx sy xn xd yn yd tail) scratch
        (Serializer.output2 sx sy xn xd yn yd) ∧
      trace.length≤8*Collector.fieldSize xn xd yn yd+80 := by
  let source:=Collector.packets sx sy xn xd yn yd tail
  obtain ⟨collect,bit,cFirst,cChain,cLast,cCount⟩:=Collector.actual_collect .halt (clean background)
    context oldX oldY memory formatter sx sy xn xd yn yd tail scratch
  let cFinal:=Collector.state (clean background) 7 context sx sy (bit,true,sy) formatter
    source scratch xn.reverse xd.reverse yn.reverse yd.reverse
  have cPath:=collect_path caller collect _ cFinal cFirst cChain cLast rfl
  let next:=Serializer.entry (initial background source scratch) context sx sy (bit,true,sy) formatter xn xd yn yd
  obtain ⟨serial,sFirst,sChain,sLast,sCount⟩:=Serializer.actual_fields2 .halt (initial background source scratch)
    context sx sy (bit,true,sy) formatter xn xd yn yd
  let sFinal : Serializer.State C:=⟨some .done,
    (((context,sx,sy),(bit,true,sx)),(false,false)),
    Serializer.bank (initial background source scratch) [] [] [] [] [] []
      (Serializer.output2 sx sy xn xd yn yd) [] []⟩
  have sPath:=serialize_path caller serial next sFinal sFirst sChain sLast rfl
  have shared : serializeConfiguration next=collectConfiguration cFinal :=
    (shared_configuration background context sx sy (bit,true,sy) formatter source scratch xn xd yn yd).symm
  have shape : collectConfiguration cFinal::(serial.map serializeConfiguration).tail=serial.map serializeConfiguration := by
    have head : (serial.map serializeConfiguration).head?=some (collectConfiguration cFinal):=
      sPath.1.trans (congrArg some shared)
    obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp head
    rw [same];rfl
  let trace:=collect.map collectConfiguration++(serial.map serializeConfiguration).tail
  let final:=serializeConfiguration sFinal
  have actual : trace.IsChain (fun a b=>TM2.step (program caller) a=some b):=
    NativeTrace.join_chain _ _ _ cPath.2.2 cPath.2.1 (shape.symm ▸ sPath.2.1)
  have last : trace.getLast?=some final:=
    (NativeTrace.join_last _ _ _ cPath.2.2).trans (shape.symm ▸ sPath.2.2)
  refine ⟨trace,final,?_,actual,last,rfl,rfl,rfl,?_⟩
  · rw [List.head?_append,cPath.1]
    rfl
  · have tailLength : (serial.map serializeConfiguration).tail.length≤serial.length := by
      simp only [List.length_tail,List.length_map]
      omega
    change trace.length≤8*(xn.length+xd.length+yn.length+yd.length)+80
    dsimp only [trace]
    simp only [List.length_append,List.length_map]
    change collect.length≤3*(xn.length+xd.length+yn.length+yd.length)+20 at cCount
    omega

end PaperProofs.Common.Native.PSTRWordBool.RatPair.Link
