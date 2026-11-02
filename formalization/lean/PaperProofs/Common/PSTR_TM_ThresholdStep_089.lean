module
public import PaperProofs.Common.PSTR_TM_NativeB1_078
public import PaperProofs.Common.PSTR_TM_Prepend_022

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdStep089
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMNatValue017

/-- Two actual original-codec increments, a fixed literal numerator ONE,
then the actual B1 machine. All593 labels are fixed independently of data.
This computes the exponent successor required by controllerB; the original
Rat/list/depth threshold wrapper and its five-Datum output remain owed. -/
def twiceMachine : Machine 103 := PSTRTMSeq005.seqMachine
  PSTRTMNativeIncrement021.nativeIncrementMachine PSTRTMNativeIncrement021.nativeIncrementMachine
def literalMachine : Machine 9 := PSTRTMPrepend022.prefixMachine [true,false,true]
def pairMachine : Machine 113 := PSTRTMSeq005.seqMachine twiceMachine literalMachine
def thresholdStepMachine : Machine 592 := PSTRTMSeq005.seqMachine pairMachine PSTRTMNativeB1078.nativeB1Machine

def literalTrace (value : Nat) : List (MachineState 9) :=
  PSTRTMPrepend022.prefixTrace [true,false,true] (encodeNat (value+2))
def literalFinal (value : Nat) : MachineState 9 :=
  PSTRTMPrepend022.prefixFinal [true,false,true] (encodeNat (value+2))

def twiceTrace (value : Nat) : List (MachineState 103) :=
  (PSTRTMNativeIncrement021.nativeTrace (rawPayload value)).map (PSTRTMSeq005.leftCfg (b:=51)) ++
    (PSTRTMNativeIncrement021.nativeTrace (rawPayload (value+1))).map (PSTRTMSeq005.rightCfg (a:=51))
def twiceFinal (value : Nat) : MachineState 103 :=
  PSTRTMSeq005.rightCfg (a:=51) (PSTRTMNativeIncrement021.nativeFinal (rawPayload (value+1)))
def pairTrace (value : Nat) : List (MachineState 113) :=
  (twiceTrace value).map (PSTRTMSeq005.leftCfg (b:=9)) ++
    (literalTrace value).map (PSTRTMSeq005.rightCfg (a:=103))
def pairFinal (value : Nat) : MachineState 113 := PSTRTMSeq005.rightCfg (a:=103)
  (literalFinal value)
def nativeTrace (value : Nat) : List (MachineState 592) :=
  (pairTrace value).map (PSTRTMSeq005.leftCfg (b:=478)) ++
    (PSTRTMNativeB1078.nativeTrace 1 (value+2)).map (PSTRTMSeq005.rightCfg (a:=113))
def nativeFinal (value : Nat) : MachineState 592 :=
  PSTRTMSeq005.rightCfg (a:=113) (PSTRTMNativeB1078.nativeFinal 1 (value+2))

theorem increment_runs (value : Nat) :
    Runs PSTRTMNativeIncrement021.nativeIncrementMachine (encodeNat value)
      (PSTRTMNativeIncrement021.nativeTrace (rawPayload value))
      (PSTRTMNativeIncrement021.nativeFinal (rawPayload value)) := by
  simpa only [PSTRTMUnblockTrace019.rawWord,rawPayload,List.length_ofFn,encodeNat,List.append_assoc,List.singleton_append] using
    PSTRTMNativeIncrement021.native_runs (rawPayload value)

theorem increment_final_tape (value : Nat) :
    (PSTRTMNativeIncrement021.nativeFinal (rawPayload value)).Tape=Turing.Tape.mk₁ (encodeNat (value+1)) := by
  have ht : (PSTRTMNativeIncrement021.nativeFinal (rawPayload value)).Tape=Turing.Tape.mk₁
      (PSTRTMUnblockTrace019.rawWord (PSTRTMIncrement009.bumpDigits (rawPayload value))) := by
    simp only [PSTRTMNativeIncrement021.nativeFinal,PSTRTMSeq005.rightCfg,PSTRTMUnblock018.state,
      Turing.Tape.mk₁,Turing.Tape.mk₂]
    rw [PSTRTMRawNat010.blank_single_false]
  rw [ht,PSTRTMCanonical020.rawWord_bump]

theorem twice_runs (value : Nat) : Runs twiceMachine (encodeNat value) (twiceTrace value) (twiceFinal value) := by
  apply PSTRTMSeq005.seq_runs PSTRTMNativeIncrement021.nativeIncrementMachine PSTRTMNativeIncrement021.nativeIncrementMachine
    (encodeNat value) (PSTRTMNativeIncrement021.nativeFinal (rawPayload value))
    (PSTRTMNativeIncrement021.nativeFinal (rawPayload (value+1)))
    (PSTRTMNativeIncrement021.nativeTrace (rawPayload value))
    (PSTRTMNativeIncrement021.nativeTrace (rawPayload (value+1))) (increment_runs value)
  have hr := increment_runs (value+1)
  rw [increment_final_tape]
  exact ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1⟩

theorem twice_final_tape (value : Nat) : (twiceFinal value).Tape=Turing.Tape.mk₁ (encodeNat (value+2)) := by
  simpa only [twiceFinal,PSTRTMSeq005.rightCfg,Nat.add_assoc] using increment_final_tape (value+1)

theorem literal_one : ([true,false,true] : List Bool)=encodeNat 1 := rfl

theorem pair_runs (value : Nat) : Runs pairMachine (encodeNat value) (pairTrace value) (pairFinal value) := by
  apply PSTRTMSeq005.seq_runs twiceMachine literalMachine (encodeNat value) (twiceFinal value)
    (literalFinal value) (twiceTrace value) (literalTrace value) (twice_runs value)
  have hr := PSTRTMPrepend022.prefix_runs [true,false,true] (encodeNat (value+2))
  rw [twice_final_tape]
  exact ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1⟩

theorem pair_final_tape (value : Nat) :
    (pairFinal value).Tape=Turing.Tape.mk₁ (encodeNat 1++encodeNat (value+2)) := by
  simpa only [pairFinal,PSTRTMSeq005.rightCfg,literalFinal,literal_one] using
    PSTRTMPrepend022.prefix_final_tape [true,false,true] (encodeNat (value+2))

theorem native_runs (value : Nat) :
    Runs thresholdStepMachine (encodeNat value) (nativeTrace value) (nativeFinal value) := by
  apply PSTRTMSeq005.seq_runs pairMachine PSTRTMNativeB1078.nativeB1Machine
    (encodeNat value) (pairFinal value) (PSTRTMNativeB1078.nativeFinal 1 (value+2))
    (pairTrace value) (PSTRTMNativeB1078.nativeTrace 1 (value+2)) (pair_runs value)
  have hr := PSTRTMNativeB1078.native_runs 1 (value+2) (by decide)
  rw [pair_final_tape]
  exact ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1⟩

theorem exponent_one (value : Nat) : PSTRTMB1Value068.exponent 1 value=Nat.clog 2 value := by
  simp [PSTRTMB1Value068.exponent]

theorem native_final_tape (value : Nat) :
    (nativeFinal value).Tape=Turing.Tape.mk₁ (encodeNat (Nat.clog 2 (value+2))) := by
  simpa only [nativeFinal,PSTRTMSeq005.rightCfg,exponent_one] using
    PSTRTMNativeB1078.native_final_tape_canonical 1 (value+2)

private theorem payload_length (value : Nat) : (rawPayload value).length=natBits value := by
  simp only [rawPayload,List.length_ofFn]

theorem literal_length (value : Nat) : (literalTrace value).length=10 :=
  PSTRTMPrepend022.prefix_length [true,false,true] (encodeNat (value+2))

theorem twice_length (value : Nat) : (twiceTrace value).length=
    (PSTRTMNativeIncrement021.nativeTrace (rawPayload value)).length+
      (PSTRTMNativeIncrement021.nativeTrace (rawPayload (value+1))).length := by
  simp only [twiceTrace,List.length_append,List.length_map]

theorem pair_length (value : Nat) : (pairTrace value).length=(twiceTrace value).length+10 := by
  simp only [pairTrace,List.length_append,List.length_map,literal_length]

theorem native_length (value : Nat) : (nativeTrace value).length=
    (PSTRTMNativeIncrement021.nativeTrace (rawPayload value)).length+
      (PSTRTMNativeIncrement021.nativeTrace (rawPayload (value+1))).length+10+
      (PSTRTMNativeB1078.nativeTrace 1 (value+2)).length := by
  simp only [nativeTrace,List.length_append,List.length_map,pair_length,twice_length]

theorem native_length_le (value : Nat) :
    (nativeTrace value).length ≤ 262144*(natBits value+1)^2 := by
  have h1 := PSTRTMArithmetic008.natBits_add_le value 1
  have h2 := PSTRTMArithmetic008.natBits_add_le value 2
  have hone : natBits 1=1 := rfl
  have htwo : natBits 2=2 := rfl
  rw [hone] at h1
  rw [htwo] at h2
  have hp := PSTRTMNativeIncrement021.native_length_le (rawPayload value)
  have hq := PSTRTMNativeIncrement021.native_length_le (rawPayload (value+1))
  simp only [payload_length] at hp hq
  have hb := PSTRTMNativeB1078.native_length_le 1 (value+2) (by decide)
  rw [hone] at hb
  have hsq1 := Nat.pow_le_pow_left h1 2
  have hsum : 1+natBits (value+2)+1 ≤ 4*(natBits value+1) := by omega
  have hsq2 := Nat.pow_le_pow_left hsum 2
  rw [native_length]
  nlinarith

theorem native_visitedSpace_le (value : Nat) :
    visitedSpace thresholdStepMachine (encodeNat value).length (nativeTrace value) ≤
      1048576*(natBits value+1)^2 := by
  have hs := PSTRTMTrace002.visitedSpace_le thresholdStepMachine (encodeNat value).length (nativeTrace value)
  have ht := native_length_le value
  rw [PSTRTMLength004.encodeNat_length] at hs ⊢
  nlinarith

/-- Original single-Nat input/output, zero included; exact canonical result.
All expansion, increments, literal writes, B1 real loop and contraction are
charged in this SAME original Runs trace and original visitedSpace. -/
theorem encodeNat_thresholdStep_computes (value : Nat) :
    computes thresholdStepMachine (encodeNat value) (encodeNat (Nat.clog 2 (value+2)))
      (262144*(natBits value+1)^2) (1048576*(natBits value+1)^2) := by
  refine ⟨nativeTrace value,nativeFinal value,native_runs value,?_,native_length_le value,native_visitedSpace_le value⟩
  rw [native_final_tape]
  simp [Turing.Tape.mk₁,Turing.Tape.mk₂]

/-- Exact original recurrence consumer on a previously ACTUALLY computed
exponent. This is an internal scalar call, not a replacement for the
original threshold input by an externally supplied controllerB value. -/
theorem encodeNat_controllerB_succ_computes (risk : Rat) (j : Nat) (hj : 1 ≤ j) :
    computes thresholdStepMachine (encodeNat (PaperProofs.Statistics.controllerB risk j))
      (encodeNat (PaperProofs.Statistics.controllerB risk (j+1)))
      (262144*(natBits (PaperProofs.Statistics.controllerB risk j)+1)^2)
      (1048576*(natBits (PaperProofs.Statistics.controllerB risk j)+1)^2) := by
  rw [PaperProofs.Statistics.controllerB_succ risk j hj,Nat.add_comm 2]
  exact encodeNat_thresholdStep_computes _

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdStep089
