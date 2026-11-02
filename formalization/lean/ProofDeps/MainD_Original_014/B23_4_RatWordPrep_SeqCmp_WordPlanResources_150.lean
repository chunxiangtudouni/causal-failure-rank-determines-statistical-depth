module

public import B23_4_RatWordPrep_SeqCmp_WordPlanModel_149

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Resources

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

theorem append_uniform {caller : Statement C} {before middle final : State C}
    {front : Segment caller before middle} {back : Segment caller middle final} {count budget : Nat}
    (a : RunBounds caller front (count*budget) budget budget) (b : RunBounds caller back budget budget budget) :
    RunBounds caller (front.append back) ((count+1)*budget) budget budget := by
  have joined := a.append b
  have time : count*budget+budget=(count+1)*budget := by ring
  simpa only [time,Nat.max_self] using joined

/-- Same actual nineteen-macro witness, all canonical entry masses
rebounded to one original-input scale at each call. No quartic envelope
is fed into the next call. Time/space/internal/clock/Sigma/charge are
derived together from the real physical plan. -/
theorem actual_operands_resources (caller : Statement C) (before : State C)
    (frame : RatInput.Stack → List Bool) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord)
    (active : before.l=some (.packet .targetForSub 0))
    (shape : before.stk=layout frame (initialData target (E.rationalWordOdds word) (Channels.channelValues E))) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.word default) ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk=layout frame (operandData target (E.rationalWordOdds word) (Channels.channelValues E)) ∧
      RunBounds caller run (19*planBudget frame E target word) (planBudget frame E target word) (planBudget frame E target word) ∧
      traceClockSum (program caller) run.trace≤19*(planBudget frame E target word)^2 ∧
      run.trace.length+traceClockSum (program caller) run.trace≤
        (19*planBudget frame E target word)*(planBudget frame E target word+1) := by
  let budget := planBudget frame E target word
  obtain ⟨s1,p1,a1,v1,raw1,r1⟩ := actual_packet_data_bounds caller .targetForSub before frame (stageData0 E target word) (target) ([]) active shape (by rfl)
  have b1 : s1.stk=layout frame (stageData1 E target word) := raw1
  have u1 : RunBounds caller p1 budget budget budget := packet_plan_bounds frame E target word (stageData0 E target word) (stageCapacity0 E target word) shape (target) (by simp [operands]) r1
  have j1 : RunBounds caller p1 (1*budget) budget budget := by simpa only [Nat.one_mul] using u1
  obtain ⟨s2,p2,a2,v2,raw2,r2⟩ := actual_one_data_bounds caller .complement s1 frame (stageData1 E target word) a1 b1
  have b2 : s2.stk=layout frame (stageData2 E target word) := raw2
  have u2 : RunBounds caller p2 budget budget budget := one_plan_bounds frame E target word (stageData1 E target word) (stageCapacity1 E target word) b1 r2
  have j2 := append_uniform j1 u2
  obtain ⟨s3,p3,a3,v3,raw3,r3⟩ := actual_subtraction_data_bounds caller s2 frame (stageData2 E target word) (1) (target) ([(E.rationalWordOdds word)]) a2 b2 (by rfl)
  have b3 : s3.stk=layout frame (stageData3 E target word) := raw3
  have u3 : RunBounds caller p3 budget budget budget := native_plan_bounds frame E target word (stageData2 E target word) (stageCapacity2 E target word) b2 RatAddSub.addSubCoefficient (Or.inr rfl) r3
  have j3 := append_uniform j2 u3
  obtain ⟨s4,p4,a4,v4,raw4,r4⟩ := actual_packet_data_bounds caller .parkComplement s3 frame (stageData3 E target word) (1-target) ([(E.rationalWordOdds word)]) a3 b3 (by rfl)
  have b4 : s4.stk=layout frame (stageData4 E target word) := raw4
  have u4 : RunBounds caller p4 budget budget budget := packet_plan_bounds frame E target word (stageData3 E target word) (stageCapacity3 E target word) b3 (1-target) (by simp [operands]) r4
  have j4 := append_uniform j3 u4
  obtain ⟨s5,p5,a5,v5,raw5,r5⟩ := actual_packet_data_bounds caller .targetForHigh s4 frame (stageData4 E target word) (target) ([]) a4 b4 (by rfl)
  have b5 : s5.stk=layout frame (stageData5 E target word) := raw5
  have u5 : RunBounds caller p5 budget budget budget := packet_plan_bounds frame E target word (stageData4 E target word) (stageCapacity4 E target word) b4 (target) (by simp [operands]) r5
  have j5 := append_uniform j4 u5
  obtain ⟨s6,p6,a6,v6,raw6,r6⟩ := actual_packet_data_bounds caller .complementForHigh s5 frame (stageData5 E target word) (1-target) ([]) a5 b5 (by rfl)
  have b6 : s6.stk=layout frame (stageData6 E target word) := raw6
  have u6 : RunBounds caller p6 budget budget budget := packet_plan_bounds frame E target word (stageData5 E target word) (stageCapacity5 E target word) b5 (1-target) (by simp [operands]) r6
  have j6 := append_uniform j5 u6
  obtain ⟨s7,p7,a7,v7,raw7,r7⟩ := actual_division_data_bounds caller true s6 frame (stageData6 E target word) (1-target) (target) ([(E.rationalWordOdds word)]) a6 b6 (by rfl)
  have b7 : s7.stk=layout frame (stageData7 E target word) := raw7
  have u7 : RunBounds caller p7 budget budget budget := native_plan_bounds frame E target word (stageData6 E target word) (stageCapacity6 E target word) b6 RatMulDiv.divCoefficient (Or.inl rfl) r7
  have j7 := append_uniform j6 u7
  obtain ⟨s8,p8,a8,v8,raw8,r8⟩ := actual_packet_data_bounds caller .parkHigh s7 frame (stageData7 E target word) ((1-target)/target) ([(E.rationalWordOdds word)]) a7 b7 (by rfl)
  have b8 : s8.stk=layout frame (stageData8 E target word) := raw8
  have u8 : RunBounds caller p8 budget budget budget := packet_plan_bounds frame E target word (stageData7 E target word) (stageCapacity7 E target word) b7 ((1-target)/target) (by simp [operands]) r8
  have j8 := append_uniform j7 u8
  obtain ⟨s9,p9,a9,v9,raw9,r9⟩ := actual_packet_data_bounds caller .complementForLow s8 frame (stageData8 E target word) (1-target) ([]) a8 b8 (by rfl)
  have b9 : s9.stk=layout frame (stageData9 E target word) := raw9
  have u9 : RunBounds caller p9 budget budget budget := packet_plan_bounds frame E target word (stageData8 E target word) (stageCapacity8 E target word) b8 (1-target) (by simp [operands]) r9
  have j9 := append_uniform j8 u9
  obtain ⟨s10,p10,a10,v10,raw10,r10⟩ := actual_packet_data_bounds caller .targetForLow s9 frame (stageData9 E target word) (target) ([]) a9 b9 (by rfl)
  have b10 : s10.stk=layout frame (stageData10 E target word) := raw10
  have u10 : RunBounds caller p10 budget budget budget := packet_plan_bounds frame E target word (stageData9 E target word) (stageCapacity9 E target word) b9 (target) (by simp [operands]) r10
  have j10 := append_uniform j9 u10
  obtain ⟨s11,p11,a11,v11,raw11,r11⟩ := actual_division_data_bounds caller false s10 frame (stageData10 E target word) (target) (1-target) ([(E.rationalWordOdds word)]) a10 b10 (by rfl)
  have b11 : s11.stk=layout frame (stageData11 E target word) := raw11
  have u11 : RunBounds caller p11 budget budget budget := native_plan_bounds frame E target word (stageData10 E target word) (stageCapacity10 E target word) b10 RatMulDiv.divCoefficient (Or.inl rfl) r11
  have j11 := append_uniform j10 u11
  obtain ⟨s12,p12,a12,v12,raw12,r12⟩ := actual_packet_data_bounds caller .parkLow s11 frame (stageData11 E target word) (target/(1-target)) ([(E.rationalWordOdds word)]) a11 b11 (by rfl)
  have b12 : s12.stk=layout frame (stageData12 E target word) := raw12
  have u12 : RunBounds caller p12 budget budget budget := packet_plan_bounds frame E target word (stageData11 E target word) (stageCapacity11 E target word) b11 (target/(1-target)) (by simp [operands]) r12
  have j12 := append_uniform j11 u12
  obtain ⟨s13,p13,a13,v13,raw13,r13⟩ := actual_packet_data_bounds caller .cacheOdds s12 frame (stageData12 E target word) ((E.rationalWordOdds word)) ([]) a12 b12 (by rfl)
  have b13 : s13.stk=layout frame (stageData13 E target word) := raw13
  have u13 : RunBounds caller p13 budget budget budget := packet_plan_bounds frame E target word (stageData12 E target word) (stageCapacity12 E target word) b12 ((E.rationalWordOdds word)) (by simp [operands]) r13
  have j13 := append_uniform j12 u13
  obtain ⟨s14,p14,a14,v14,raw14,r14⟩ := actual_packet_data_bounds caller .oddsFirst s13 frame (stageData13 E target word) ((E.rationalWordOdds word)) ([target]) a13 b13 (by rfl)
  have b14 : s14.stk=layout frame (stageData14 E target word) := raw14
  have u14 : RunBounds caller p14 budget budget budget := packet_plan_bounds frame E target word (stageData13 E target word) (stageCapacity13 E target word) b13 ((E.rationalWordOdds word)) (by simp [operands]) r14
  have j14 := append_uniform j13 u14
  obtain ⟨s15,p15,a15,v15,raw15,r15⟩ := actual_one_data_bounds caller .map s14 frame (stageData14 E target word) a14 b14
  have b15 : s15.stk=layout frame (stageData15 E target word) := raw15
  have u15 : RunBounds caller p15 budget budget budget := one_plan_bounds frame E target word (stageData14 E target word) (stageCapacity14 E target word) b14 r15
  have j15 := append_uniform j14 u15
  obtain ⟨s16,p16,a16,v16,raw16,r16⟩ := actual_packet_data_bounds caller .oddsMiddle s15 frame (stageData15 E target word) ((E.rationalWordOdds word)) ([target]) a15 b15 (by rfl)
  have b16 : s16.stk=layout frame (stageData16 E target word) := raw16
  have u16 : RunBounds caller p16 budget budget budget := packet_plan_bounds frame E target word (stageData15 E target word) (stageCapacity15 E target word) b15 ((E.rationalWordOdds word)) (by simp [operands]) r16
  have j16 := append_uniform j15 u16
  obtain ⟨s17,p17,a17,v17,raw17,r17⟩ := actual_packet_data_bounds caller .high s16 frame (stageData16 E target word) ((1-target)/target) (Channels.channelValues E) a16 b16 (by rfl)
  have b17 : s17.stk=layout frame (stageData17 E target word) := raw17
  have u17 : RunBounds caller p17 budget budget budget := packet_plan_bounds frame E target word (stageData16 E target word) (stageCapacity16 E target word) b16 ((1-target)/target) (by simp [operands]) r17
  have j17 := append_uniform j16 u17
  obtain ⟨s18,p18,a18,v18,raw18,r18⟩ := actual_packet_data_bounds caller .low s17 frame (stageData17 E target word) (target/(1-target)) ([1-target]) a17 b17 (by rfl)
  have b18 : s18.stk=layout frame (stageData18 E target word) := raw18
  have u18 : RunBounds caller p18 budget budget budget := packet_plan_bounds frame E target word (stageData17 E target word) (stageCapacity17 E target word) b17 (target/(1-target)) (by simp [operands]) r18
  have j18 := append_uniform j17 u18
  obtain ⟨s19,p19,a19,v19,raw19,r19⟩ := actual_packet_data_bounds caller .oddsLast s18 frame (stageData18 E target word) ((E.rationalWordOdds word)) ([target]) a18 b18 (by rfl)
  have b19 : s19.stk=layout frame (stageData19 E target word) := raw19
  have u19 : RunBounds caller p19 budget budget budget := packet_plan_bounds frame E target word (stageData18 E target word) (stageCapacity18 E target word) b18 ((E.rationalWordOdds word)) (by simp [operands]) r19
  have j19 := append_uniform j18 u19
  let whole := ((((((((((((((((((p1.append p2).append p3).append p4).append p5).append p6).append p7).append p8).append p9).append p10).append p11).append p12).append p13).append p14).append p15).append p16).append p17).append p18).append p19)
  refine ⟨s19,whole,a19,v19.trans (v18.trans (v17.trans (v16.trans (v15.trans (v14.trans (v13.trans (v12.trans (v11.trans (v10.trans (v9.trans (v8.trans (v7.trans (v6.trans (v5.trans (v4.trans (v3.trans (v2.trans (v1)))))))))))))))))),?_,j19,?_,?_⟩
  · rw [b19,stageData19_eq]
  · exact j19.clockSum.trans_eq (by ring)
  · exact j19.charge

end B23_4_RatWordPrep.WordFinish.Resources
