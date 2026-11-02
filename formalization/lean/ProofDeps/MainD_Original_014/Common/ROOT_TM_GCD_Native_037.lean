module
public import Common.ROOT_TM_GCD_ResidentBound_036
public import Common.PSTR_TM_NativeAdd_053

set_option autoImplicit false
set_option warningAsError true
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDNative037
open PaperProofs.Common.Native.RationalControllerComputation
open ROOTTMGCDDispatch018 ROOTTMGCDLeg021 ROOTTMGCDPairStep019 ROOTTMGCDResident035 ROOTTMGCDResidentBound036
local notation "cols" => PSTRTMBinaryAdd024.operandColumns

def pairs (a b : Nat) : List Pair:=PSTRTMNativeAdd053.pairs a b
def nativeTrace (a b : Nat) : List (MachineState 3564) :=
  (PSTRTMRawPack045.rawPackTrace (PSTRTMNatValue017.rawPayload a) (PSTRTMNatValue017.rawPayload b)).map
    (PSTRTMSeq005.leftCfg (b:=3219))++(residentTrace (pairs a b)).map (PSTRTMSeq005.rightCfg (a:=344))
def nativeFinal (a b : Nat) : MachineState 3564:=PSTRTMSeq005.rightCfg (a:=344) (residentFinal (pairs a b))

theorem pairs_values (a b : Nat) : PSTRTMBinaryAdd024.firstValue (pairs a b)=a ∧
    PSTRTMBinaryAdd024.secondValue (pairs a b)=b := by
  have h:=PSTRTMAddCanonical052.digitPairs_values (PSTRTMNatValue017.rawPayload a) (PSTRTMNatValue017.rawPayload b)
  rw [PSTRTMNatValue017.valueDigits_rawPayload,PSTRTMNatValue017.valueDigits_rawPayload] at h
  exact h

theorem resident_initial (a b : Nat) : cfgAt 0 0 (pairs a b) []=
    (⟨0,Turing.Tape.mk₁ (cols (pairs a b))⟩ : MachineState 3219) := by
  change (⟨0,Turing.Tape.mk₂ [false] (cols (pairs a b)++[false,false])⟩ : MachineState 3219)=_
  rw [ROOTTMGCDCodec034.empty_counter_tape]

theorem native_runs (a b : Nat) : Runs nativeGcdMachine (encodeNat a++encodeNat b) (nativeTrace a b) (nativeFinal a b) := by
  apply PSTRTMSeq005.seq_runs PSTRTMRawPack045.rawPackMachine residentGcdMachine
    (encodeNat a++encodeNat b) (PSTRTMRawPack045.rawPackFinal (PSTRTMNatValue017.rawPayload a) (PSTRTMNatValue017.rawPayload b))
    (residentFinal (pairs a b))
    (PSTRTMRawPack045.rawPackTrace (PSTRTMNatValue017.rawPayload a) (PSTRTMNatValue017.rawPayload b))
    (residentTrace (pairs a b)) (PSTRTMNativeAdd053.raw_runs a b)
  rw [PSTRTMRawPack045.rawPack_final_tape]
  change PSTRTMSeq005.RunsFrom residentGcdMachine ⟨0,Turing.Tape.mk₁ (cols (pairs a b))⟩ _ _
  rw [←resident_initial]
  exact resident_runsFrom (pairs a b)

theorem native_final_tape (a b : Nat) : (nativeFinal a b).Tape=Turing.Tape.mk₁ (encodeNat (Nat.gcd a b)) := by
  change (residentFinal (pairs a b)).Tape=_
  rw [resident_final_tape,(pairs_values a b).1,(pairs_values a b).2]

theorem native_length_le (a b : Nat) :
    (nativeTrace a b).length ≤ 16384*(natBits a+natBits b+1)^2 := by
  have hr : (PSTRTMRawPack045.rawPackTrace (PSTRTMNatValue017.rawPayload a) (PSTRTMNatValue017.rawPayload b)).length ≤
      2048*(natBits a+natBits b+1)^2 := by
    simpa only [PSTRTMNatValue017.rawPayload,List.length_ofFn] using
      PSTRTMRawPack045.rawPack_length_le (PSTRTMNatValue017.rawPayload a) (PSTRTMNatValue017.rawPayload b)
  have hs:=resident_length_le (pairs a b)
  have hw:=PSTRTMNativeAdd053.pairs_length_le a b
  change (pairs a b).length ≤ natBits a+natBits b at hw
  have hp:=Nat.pow_le_pow_left (show (pairs a b).length+1 ≤ natBits a+natBits b+1 by omega) 2
  simp only [nativeTrace,List.length_append,List.length_map]
  nlinarith

theorem native_visitedSpace_le (a b : Nat) :
    visitedSpace nativeGcdMachine (encodeNat a++encodeNat b).length (nativeTrace a b) ≤
      65536*(natBits a+natBits b+1)^2 := by
  have hs:=PSTRTMTrace002.visitedSpace_le nativeGcdMachine (encodeNat a++encodeNat b).length (nativeTrace a b)
  have ht:=native_length_le a b
  simp only [List.length_append,PSTRTMLength004.encodeNat_length] at hs ⊢
  nlinarith

/-- Original full-input gcd: one fixed machine is chosen before every
operand, including zero and unequal bit widths. Every scan, subtraction,
shift, counter update, codec step and visited cell is charged by real Runs. -/
theorem encodeNat_gcd_computes (a b : Nat) :
    computes nativeGcdMachine (encodeNat a++encodeNat b) (encodeNat (Nat.gcd a b))
      (16384*(natBits a+natBits b+1)^2) (65536*(natBits a+natBits b+1)^2) := by
  refine ⟨nativeTrace a b,nativeFinal a b,native_runs a b,?_,native_length_le a b,native_visitedSpace_le a b⟩
  rw [native_final_tape]
  exact Turing.Tape.mk'_right₀ _ _

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDNative037
