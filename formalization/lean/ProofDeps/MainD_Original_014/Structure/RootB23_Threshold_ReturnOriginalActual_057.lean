module
public import Structure.RootB23_Threshold_ReturnOriginalPacket_056

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnOriginalPacket
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)

private theorem time_group (a b p : ℕ) : a*p+b*p=(a+b)*p := (Nat.add_mul _ _ _).symm

private theorem prefix_space (space charged count coefficient power : ℕ)
    (bound : space≤charged+2*count+1) (time : count≤coefficient*power) :
    space≤charged+2*(coefficient*power)+1 := by omega

private theorem original_space (space input count coefficient power : ℕ)
    (bound : space ≤ input+2*count+1) (time : count≤coefficient*power) (charged : input+1≤power) :
    space≤(2*coefficient+2)*power := by nlinarith only [bound,time,charged]

theorem final_right (risk : Rat) (depth left : ℕ) :
    (finalTape risk depth left).right₀=ListBlank.mk (thresholdOutput risk depth) := by
  simp only [finalTape,Tape.mk₂,Tape.mk'_right₀]
  exact PSTRTMPackFinish039.blank_false_suffix _ 16

/-- ONE fixed code from the complete original two-Datum input to all
five original output fields, with a genuine trace and actual HALT. Its
first three observed bits are read from tape, never passed as an answer;
all WEST scratch remains charged by the original visitedSpace measure. -/
theorem actual (risk : Rat) (depth : ℕ) (hr : 0<risk) (hd : 1≤depth) :
    ∃ (left : ℕ) (trace : List (MachineState cap)),
      Runs code (encode [.rational risk,.natural depth]) trace ⟨finalPort,finalTape risk depth left⟩ ∧
      trace.length≤timeCoefficient*OriginalBridge.scale risk depth^10 ∧
      (∀ chargedLength clock, visitedSpace code chargedLength (trace.take clock)≤
        chargedLength+2*(timeCoefficient*OriginalBridge.scale risk depth^10)+1) ∧
      (∀ clock, visitedSpace code (encode [.rational risk,.natural depth]).length (trace.take clock)≤
        spaceCoefficient*OriginalBridge.scale risk depth^10) := by
  obtain ⟨left,before,beforeRun,beforeTime,_,_⟩:=ReturnOriginal.actual risk depth hr hd
  have beforeFrom : PSTRTMSeq005.RunsFrom ReturnOriginal.code
      ⟨0,Tape.mk₁ (encode [.rational risk,.natural depth])⟩ before
      ⟨ReturnOriginal.finalPort (OriginalBridge.branch risk depth),ReturnPairReady.finalTape risk depth risk left⟩ :=
    ⟨beforeRun.1,beforeRun.2.1,beforeRun.2.2.1,beforeRun.2.2.2.1⟩
  have first : BoundedRun ReturnOriginal.code (Tape.mk₁ (encode [.rational risk,.natural depth]))
      (ReturnOriginal.finalPort (OriginalBridge.branch risk depth)) (ReturnPairReady.finalTape risk depth risk left)
      (ReturnOriginal.timeCoefficient*OriginalBridge.scale risk depth^10) := ⟨before,beforeFrom,beforeTime⟩
  have second:=(tail_bounded risk depth left hr).mono (tail_fee_le risk depth hr hd)
  have joined:=first.seq second
  have grouped : ReturnOriginal.timeCoefficient*OriginalBridge.scale risk depth^10+
      tailCoefficient*OriginalBridge.scale risk depth^10=timeCoefficient*OriginalBridge.scale risk depth^10 := time_group _ _ _
  rw [grouped] at joined
  have whole : BoundedRun code (Tape.mk₁ (encode [.rational risk,.natural depth])) finalPort
      (finalTape risk depth left) (timeCoefficient*OriginalBridge.scale risk depth^10) := by
    simpa only [code,cap,finalPort] using joined
  obtain ⟨trace,run,time⟩:=whole
  have genuine : Runs code (encode [.rational risk,.natural depth]) trace ⟨finalPort,finalTape risk depth left⟩ :=
    PSTRTMTrace002.runs_of_chain _ _ _ _ run.1 run.2.1 run.2.2.1 run.2.2.2
  refine ⟨left,trace,genuine,time,?_,?_⟩
  · intro chargedLength clock
    have space:=PSTRTMTrace002.visitedSpace_le code chargedLength (trace.take clock)
    have taken : (trace.take clock).length≤trace.length := by rw [List.length_take];exact Nat.min_le_right _ _
    exact prefix_space _ _ _ _ _ space (taken.trans time)
  · intro clock
    have space:=PSTRTMTrace002.visitedSpace_le code (encode [.rational risk,.natural depth]).length (trace.take clock)
    have taken : (trace.take clock).length≤trace.length := by rw [List.length_take];exact Nat.min_le_right _ _
    have input : (encode [.rational risk,.natural depth]).length+1≤OriginalBridge.scale risk depth := by
      unfold OriginalBridge.scale
      omega
    have power : OriginalBridge.scale risk depth≤OriginalBridge.scale risk depth^10 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (OriginalBridge.scale_positive risk depth) (by decide : 1≤10)
    exact original_space _ _ _ _ _ space (taken.trans time) (input.trans power)

/-- The exact frozen computes definition: the right tape is the full
original encode5, and the same real run pays both time and visited space.
No blank-WEST or caller-supplied width/room premise is needed. -/
theorem computes_uniform (risk : Rat) (depth : ℕ) (hr : 0<risk) (hd : 1≤depth) :
    computes code (encode [.rational risk,.natural depth]) (thresholdOutput risk depth)
      (timeCoefficient*OriginalBridge.scale risk depth^10) (spaceCoefficient*OriginalBridge.scale risk depth^10) := by
  obtain ⟨left,trace,run,time,_,space⟩:=actual risk depth hr hd
  refine ⟨trace,⟨finalPort,finalTape risk depth left⟩,run,final_right risk depth left,time,?_⟩
  simpa only [List.take_length] using space trace.length

end RootB23.Threshold.ReturnOriginalPacket
