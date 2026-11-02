module
public import Common.ROOT_TM_GCD_Restore_032
public import Common.ROOT_TM_GCD_LoopBound_033

set_option autoImplicit false
set_option warningAsError true
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDCodec034
open PaperProofs.Common.Native.RationalControllerComputation
open PA17TMDivisionCompose006 ROOTTMGCDDispatch018 ROOTTMGCDLift020 ROOTTMGCDLeg021 ROOTTMGCDPairStep019
local notation "cols" => PSTRTMBinaryAdd024.operandColumns

theorem empty_counter_tape (pairs : List Pair) :
    Turing.Tape.mk₂ [false] (cols pairs++[false,false])=Turing.Tape.mk₁ (cols pairs) := by
  rw [PSTRTMMulLoopIteration092.tape_trailing_zeros]
  simp only [Turing.Tape.mk₁,Turing.Tape.mk₂,PSTRTMRawNat010.blank_single_false]

def codecTrace (pairs : List Pair) : List (MachineState 3219) :=
  (PA17TMDivisionCodec003.isolatedOutputTrace pairs).map (lift (by decide : 103 ≤ 139) 22)
def codecFinal (pairs : List Pair) : MachineState 3219 :=
  lift (by decide : 103 ≤ 139) 22 (PA17TMDivisionCodec003.isolatedOutputFinal pairs)

theorem codec_runsFrom (pairs : List Pair) :
    PSTRTMSeq005.RunsFrom residentGcdMachine (cfgAt 22 0 pairs []) (codecTrace pairs) (codecFinal pairs) := by
  have run:=PA17TMDivisionCodec003.isolatedOutput_runsFrom pairs
  have hf : family 22=padMachine (by decide : 103 ≤ 139) PA17TMDivisionCodec003.isolatedOutputMachine := rfl
  have hs:=phase_segment (by decide : 103 ≤ 139) 22 PA17TMDivisionCodec003.isolatedOutputMachine hf _ _ _ run
  have hh:=phase_halt (by decide : 103 ≤ 139) 22 PA17TMDivisionCodec003.isolatedOutputMachine hf _ run.2.2.2 rfl
  have hfirst : lift (by decide : 103 ≤ 139) 22
      (⟨0,Turing.Tape.mk₁ (cols pairs)⟩ : MachineState 103)=cfgAt 22 0 pairs [] := by
    change blockCfg (s:=139) (22 : Fin 23) ⟨0,Turing.Tape.mk₁ (cols pairs)⟩=
      blockCfg (s:=139) (22 : Fin 23) ⟨0,Turing.Tape.mk₂ [false] (cols pairs++[false,false])⟩
    rw [empty_counter_tape]
  have h:=segment_runsFrom residentGcdMachine _ _ _ hs hh
  simpa only [codecTrace,codecFinal,hfirst] using h

theorem codec_final_tape (pairs : List Pair) :
    (codecFinal pairs).Tape=Turing.Tape.mk₁ (encodeNat (PSTRTMBinaryAdd024.firstValue pairs)) :=
  PA17TMDivisionCodec003.isolatedOutput_final_tape pairs

theorem codecTrace_length_le (pairs : List Pair) :
    (codecTrace pairs).length ≤ 256*(pairs.length+1)^2 := by
  have h:=PA17TMDivisionCodec003.resultCodecTrace_length_le (PA17TMDivisionCodec003.firstBits pairs)
  rw [PA17TMDivisionCodec003.firstBits_length] at h
  simp only [codecTrace,PA17TMDivisionCodec003.isolatedOutputTrace,List.length_map,List.length_append,
    PA17TMDivisionCodec003.projectATrace_length]
  nlinarith

theorem finish_leg (first middle last : MachineState 3219)
    (xs ys : List (MachineState 3219)) (hx : Leg first xs middle)
    (hy : PSTRTMSeq005.RunsFrom residentGcdMachine middle ys last) :
    PSTRTMSeq005.RunsFrom residentGcdMachine first (xs++ys) last := by
  obtain ⟨finalLeft,hs,ht⟩:=hx
  exact segment_runsFrom residentGcdMachine _ _ _
    (segment_append residentGcdMachine first finalLeft middle last xs ys hs ⟨hy.1,hy.2.1,hy.2.2.1⟩ ht) hy.2.2.2

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDCodec034
