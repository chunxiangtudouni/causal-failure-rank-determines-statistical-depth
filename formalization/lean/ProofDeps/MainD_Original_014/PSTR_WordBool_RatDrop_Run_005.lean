module

public import PSTR_WordBool_RatDrop_Packet_004

/-! One actual bounded-space binary-result consumer. It keeps the result
and arbitrary tail while physically disposing the two old operand packets. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatDrop

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

theorem packet_append (negative : Bool) (num den tail : List Bool) :
    PSTRSymbolicRatExport.packet negative num den tail=
      PSTRSymbolicRatExport.packet negative num den []++tail := by
  simp [PSTRSymbolicRatExport.packet,List.append_assoc]

theorem actual_drop_fields (background : Stack→List Bool) (context : C) (memory : RatOutput.Store)
    (rs xs ys : Bool) (rn rd xn xd yn yd tail : List Bool) :
    let source:=PSTRSymbolicRatExport.packet rs rn rd (PSTRSymbolicRatExport.packet xs xn xd
      (PSTRSymbolicRatExport.packet ys yn yd tail))
    ∃ trace : List (State C),
      trace.head?=some (state background 0 context memory source []) ∧
      trace.IsChain (fun a b=>TM2.step (program .halt) a=some b) ∧
      trace.getLast?=some (state background 10 context (false,false) (PSTRSymbolicRatExport.packet rs rn rd tail) []) ∧
      trace.length≤3*(rn.length+rd.length)+(xn.length+xd.length)+(yn.length+yd.length)+17 ∧
      (∀ current∈trace,Safe background context (outside background+source.length) current) ∧
      ∀ current∈trace.dropLast,current.l≠some 10 := by
  dsimp only
  let lastArg:=PSTRSymbolicRatExport.packet ys yn yd tail
  let args:=PSTRSymbolicRatExport.packet xs xn xd lastArg
  let original:=PSTRSymbolicRatExport.packet rs rn rd args
  let parked:=(PSTRSymbolicRatExport.packet rs rn rd []).reverse
  let K:=outside background+original.length
  have originalLength : original.length=2*(rn.length+rd.length)+6+args.length:=packet_length rs rn rd args
  have argsLength : args.length=2*(xn.length+xd.length)+6+lastArg.length:=packet_length xs xn xd lastArg
  have lastLength : lastArg.length=2*(yn.length+yd.length)+6+tail.length:=packet_length ys yn yd tail
  have parkedLength : parked.length=2*(rn.length+rd.length)+6:=by
    dsimp only [parked]
    rw [List.length_reverse,packet_length]
    simp only [List.length_nil,Nat.add_zero]
  let s0:=state background 0 context memory original []
  let s1:=state background 3 context (true,false) args parked
  let s2:=state background 6 context (true,false) lastArg parked
  let s3:=state background 9 context (true,false) tail parked
  let s4:=state background 10 context (false,false) (PSTRSymbolicRatExport.packet rs rn rd tail) []
  obtain ⟨t0,h0,c0,l0,n0,b0⟩:=actual_packet (.halt:Statement C) true background context 0 1 2 3 rfl rfl rfl memory rs rn rd args []
  have last0 : t0.getLast?=some s1:=by simpa only [List.append_nil,ite_true] using l0
  let p0:Segment .halt background context K s0 s1 (rn.length+rd.length+4):=
    ⟨t0,h0,c0,last0,n0,by intro current member;simpa only [List.length_nil,Nat.add_zero] using b0 current member⟩
  obtain ⟨t1,h1,c1,l1,n1,b1⟩:=actual_packet (.halt:Statement C) false background context 3 4 5 6 rfl rfl rfl
    (true,false) xs xn xd lastArg parked
  let p1:Segment .halt background context K s1 s2 (xn.length+xd.length+4):=
    ⟨t1,h1,c1,l1,n1,by
      intro current member
      apply safe_mono (b1 current member)
      change outside background+args.length+parked.length≤K
      dsimp only [K]
      omega⟩
  obtain ⟨t2,h2,c2,l2,n2,b2⟩:=actual_packet (.halt:Statement C) false background context 6 7 8 9 rfl rfl rfl
    (true,false) ys yn yd tail parked
  let p2:Segment .halt background context K s2 s3 (yn.length+yd.length+4):=
    ⟨t2,h2,c2,l2,n2,by
      intro current member
      apply safe_mono (b2 current member)
      change outside background+lastArg.length+parked.length≤K
      dsimp only [K]
      omega⟩
  have reverseLast : (reverseTrace background context parked (true,false) tail).getLast?=some s4 := by
    rw [reverse_last]
    dsimp only [parked]
    rw [List.reverse_reverse,←packet_append]
  let p3:Segment .halt background context K s3 s4 (parked.length+2):={
    trace:=reverseTrace background context parked (true,false) tail
    head:=reverse_head background context parked (true,false) tail
    chain:=reverse_chain .halt background context parked (true,false) tail
    last:=reverseLast
    count:=(reverse_length background context parked (true,false) tail).le
    safe:=by
      intro current member
      apply safe_mono (reverse_safe background context parked (true,false) tail current member)
      dsimp only [K]
      omega }
  let whole:=((p0.append p1).append p2).append p3
  refine ⟨whole.trace,whole.head,whole.chain,whole.last,?_,whole.safe,?_⟩
  · have count:=whole.count
    omega
  · exact NativeMulLink.no_early_halt_port (program .halt) 10 rfl whole.trace s4 whole.chain whole.last rfl

end PaperProofs.Common.Native.PSTRWordBool.RatDrop
