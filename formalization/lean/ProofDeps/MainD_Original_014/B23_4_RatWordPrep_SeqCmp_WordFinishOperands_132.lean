module

public import B23_4_RatWordPrep_SeqCmp_WordFinishBootstrap_131

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

def operandData (target odds : Rat) (table : List Rat) : Data :=
  fun slot => if slot=0 then [target/(1-target),1-target] else
    if slot=1 then [odds,target] else if slot=2 then ((1-target)/target)::table else
    if slot=15 then [odds,target/(1-target),(1-target)/target,odds,1,odds,odds] else []

/-- One actual fixed source computes complement and both thresholds,
then physically builds seven original comparison operands. Only the
fixed constant1 is pushed; every input-dependent packet is transported
or produced by the existing native normalized arithmetic machine. -/
theorem actual_operands (caller : Statement C) (before : State C)
    (frame : RatInput.Stack → List Bool) (target odds : Rat) (table : List Rat)
    (active : before.l=some (.packet .targetForSub 0))
    (shape : before.stk=layout frame (initialData target odds table)) :
    ∃ (final : State C) (_run : Segment caller before final),
      final.l=some (.word default) ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk=layout frame (operandData target odds table) := by
  let d0 := initialData target odds table
  let d1 : Data := packetData .targetForSub d0 (target) ([])
  obtain ⟨s1,p1,a1,v1,b1,_t1⟩ := actual_packet_data caller .targetForSub before frame d0 (target) ([]) active shape (by rfl)
  let d2 : Data := Function.update d1 15 (1::d1 15)
  obtain ⟨s2,p2,a2,v2,b2,_t2⟩ := actual_one_data caller .complement s1 frame d1 a1 b1
  let d3 : Data := Function.update d2 15 (((1)-(target))::[odds])
  obtain ⟨s3,p3,a3,v3,b3,_t3⟩ := actual_subtraction_data caller s2 frame d2 (1) (target) ([odds]) a2 b2 (by rfl)
  let d4 : Data := packetData .parkComplement d3 (1-target) ([odds])
  obtain ⟨s4,p4,a4,v4,b4,_t4⟩ := actual_packet_data caller .parkComplement s3 frame d3 (1-target) ([odds]) a3 b3 (by rfl)
  let d5 : Data := packetData .targetForHigh d4 (target) ([])
  obtain ⟨s5,p5,a5,v5,b5,_t5⟩ := actual_packet_data caller .targetForHigh s4 frame d4 (target) ([]) a4 b4 (by rfl)
  let d6 : Data := packetData .complementForHigh d5 (1-target) ([])
  obtain ⟨s6,p6,a6,v6,b6,_t6⟩ := actual_packet_data caller .complementForHigh s5 frame d5 (1-target) ([]) a5 b5 (by rfl)
  let d7 : Data := Function.update d6 15 (((1-target)/(target))::[odds])
  obtain ⟨s7,p7,a7,v7,b7,_t7⟩ := actual_division_data caller true s6 frame d6 (1-target) (target) ([odds]) a6 b6 (by rfl)
  let d8 : Data := packetData .parkHigh d7 ((1-target)/target) ([odds])
  obtain ⟨s8,p8,a8,v8,b8,_t8⟩ := actual_packet_data caller .parkHigh s7 frame d7 ((1-target)/target) ([odds]) a7 b7 (by rfl)
  let d9 : Data := packetData .complementForLow d8 (1-target) ([])
  obtain ⟨s9,p9,a9,v9,b9,_t9⟩ := actual_packet_data caller .complementForLow s8 frame d8 (1-target) ([]) a8 b8 (by rfl)
  let d10 : Data := packetData .targetForLow d9 (target) ([])
  obtain ⟨s10,p10,a10,v10,b10,_t10⟩ := actual_packet_data caller .targetForLow s9 frame d9 (target) ([]) a9 b9 (by rfl)
  let d11 : Data := Function.update d10 15 (((target)/(1-target))::[odds])
  obtain ⟨s11,p11,a11,v11,b11,_t11⟩ := actual_division_data caller false s10 frame d10 (target) (1-target) ([odds]) a10 b10 (by rfl)
  let d12 : Data := packetData .parkLow d11 (target/(1-target)) ([odds])
  obtain ⟨s12,p12,a12,v12,b12,_t12⟩ := actual_packet_data caller .parkLow s11 frame d11 (target/(1-target)) ([odds]) a11 b11 (by rfl)
  let d13 : Data := packetData .cacheOdds d12 (odds) ([])
  obtain ⟨s13,p13,a13,v13,b13,_t13⟩ := actual_packet_data caller .cacheOdds s12 frame d12 (odds) ([]) a12 b12 (by rfl)
  let d14 : Data := packetData .oddsFirst d13 (odds) ([target])
  obtain ⟨s14,p14,a14,v14,b14,_t14⟩ := actual_packet_data caller .oddsFirst s13 frame d13 (odds) ([target]) a13 b13 (by rfl)
  let d15 : Data := Function.update d14 15 (1::d14 15)
  obtain ⟨s15,p15,a15,v15,b15,_t15⟩ := actual_one_data caller .map s14 frame d14 a14 b14
  let d16 : Data := packetData .oddsMiddle d15 (odds) ([target])
  obtain ⟨s16,p16,a16,v16,b16,_t16⟩ := actual_packet_data caller .oddsMiddle s15 frame d15 (odds) ([target]) a15 b15 (by rfl)
  let d17 : Data := packetData .high d16 ((1-target)/target) (table)
  obtain ⟨s17,p17,a17,v17,b17,_t17⟩ := actual_packet_data caller .high s16 frame d16 ((1-target)/target) (table) a16 b16 (by rfl)
  let d18 : Data := packetData .low d17 (target/(1-target)) ([1-target])
  obtain ⟨s18,p18,a18,v18,b18,_t18⟩ := actual_packet_data caller .low s17 frame d17 (target/(1-target)) ([1-target]) a17 b17 (by rfl)
  let d19 : Data := packetData .oddsLast d18 (odds) ([target])
  obtain ⟨s19,p19,a19,v19,b19,_t19⟩ := actual_packet_data caller .oddsLast s18 frame d18 (odds) ([target]) a18 b18 (by rfl)
  let whole := ((((((((((((((((((p1.append p2).append p3).append p4).append p5).append p6).append p7).append p8).append p9).append p10).append p11).append p12).append p13).append p14).append p15).append p16).append p17).append p18).append p19)
  refine ⟨s19,whole,a19,v19.trans (v18.trans (v17.trans (v16.trans (v15.trans (v14.trans (v13.trans (v12.trans (v11.trans (v10.trans (v9.trans (v8.trans (v7.trans (v6.trans (v5.trans (v4.trans (v3.trans (v2.trans (v1)))))))))))))))))),?_⟩
  rw [b19]
  apply congrArg (layout frame)
  funext slot
  fin_cases slot <;> rfl

theorem operand_packet (frame : RatInput.Stack → List Bool) (target odds : Rat) (table : List Rat) :
    layout frame (operandData target odds table) 15=
      SeqCmp.Word.input odds (target/(1-target)) ((1-target)/target) [] := by
  change RatInput.Encoder.packet odds (RatInput.Encoder.packet (target/(1-target))
    (RatInput.Encoder.packet ((1-target)/target) (RatInput.Encoder.packet odds
      (RatInput.Encoder.packet 1 (RatInput.Encoder.packet odds (RatInput.Encoder.packet odds []))))))=_
  rw [SeqCmp.Word.input]
  have pair (x y : Rat) (tail : List Bool) :
      RatInput.Encoder.packet x (RatInput.Encoder.packet y tail)=RatPair.input x y tail :=
    RatPair.two_packet_format x y tail
  rw [pair 1 odds (RatInput.Encoder.packet odds [])]
  rw [pair ((1-target)/target) odds]
  exact pair odds (target/(1-target)) _

end B23_4_RatWordPrep.WordFinish
