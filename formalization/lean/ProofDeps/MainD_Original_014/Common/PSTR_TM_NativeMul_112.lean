module
public import Common.PSTR_TM_MulProjectRun_107
public import Common.PSTR_TM_MulWidth_108
public import Common.PSTR_TM_TrimRun_111
public import Common.PSTR_TM_UnblockTrace_019

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNativeMul112
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMNatValue017

def productDigits (a b : Nat) : List Bool := PSTRTMMulProjectCode100.cBits (PSTRTMRawMulResident099.outputTriples a b)
def rawProjectMachine : Machine 945 := PSTRTMSeq005.seqMachine PSTRTMRawMulResident099.rawMulResidentMachine PSTRTMMulProjectRun107.projectMachine
def canonicalBlocksMachine : Machine 962 := PSTRTMSeq005.seqMachine rawProjectMachine PSTRTMTrimCode103.trimMachine
/-- ONE fixed983-label ordinary Bool machine. ORIGINAL raw two-Nat input,
real binary schoolbook multiplication/operand transport, real auxiliary
column projection, real high-zero erasure/one-zero allocation and inverse
codec. No output answer, width, padding, alignment, fuel or cost input. -/
def nativeMulMachine : Machine 982 := PSTRTMSeq005.seqMachine canonicalBlocksMachine PSTRTMUnblock018.unblockMachine

def rawProjectTrace (a b : Nat) : List (MachineState 945) :=
  (PSTRTMRawMulResident099.nativeTrace a b).map (PSTRTMSeq005.leftCfg (b:=224)) ++
    (PSTRTMMulProjectRun107.projectTrace (PSTRTMRawMulResident099.outputTriples a b)).map (PSTRTMSeq005.rightCfg (a:=720))
def rawProjectFinal (a b : Nat) : MachineState 945 :=
  PSTRTMSeq005.rightCfg (a:=720) (PSTRTMMulProjectRun107.projectFinal (PSTRTMRawMulResident099.outputTriples a b))
def blocksTrace (a b : Nat) : List (MachineState 962) :=
  (rawProjectTrace a b).map (PSTRTMSeq005.leftCfg (b:=16)) ++
    (PSTRTMTrimRun111.trimTrace (productDigits a b)).map (PSTRTMSeq005.rightCfg (a:=945))
def blocksFinal (a b : Nat) : MachineState 962 :=
  PSTRTMSeq005.rightCfg (a:=945) (PSTRTMTrimRun111.trimFinal (productDigits a b))
def nativeTrace (a b : Nat) : List (MachineState 982) :=
  (blocksTrace a b).map (PSTRTMSeq005.leftCfg (b:=19)) ++
    (PSTRTMUnblockTrace019.unblockTrace (rawPayload (a*b))).map (PSTRTMSeq005.rightCfg (a:=962))
def nativeFinal (a b : Nat) : MachineState 982 := PSTRTMSeq005.rightCfg (a:=962)
  (PSTRTMUnblock018.state 19 [false] (PSTRTMUnblockTrace019.rawWord (rawPayload (a*b))))

theorem productDigits_value (a b : Nat) : PSTRTMIncrement009.valueDigits (productDigits a b)=a*b :=
  (PSTRTMRawMulResident099.exact_product a b).1
theorem productDigits_length (a b : Nat) :
    (productDigits a b).length=(PSTRTMRawMulResident099.outputTriples a b).length :=
  PSTRTMMulProjectRun107.cBits_length _

theorem rawProject_runs (a b : Nat) :
    Runs rawProjectMachine (encodeNat a++encodeNat b) (rawProjectTrace a b) (rawProjectFinal a b) := by
  apply PSTRTMSeq005.seq_runs PSTRTMRawMulResident099.rawMulResidentMachine PSTRTMMulProjectRun107.projectMachine
    (encodeNat a++encodeNat b) (PSTRTMRawMulResident099.nativeFinal a b)
    (PSTRTMMulProjectRun107.projectFinal (PSTRTMRawMulResident099.outputTriples a b))
    (PSTRTMRawMulResident099.nativeTrace a b)
    (PSTRTMMulProjectRun107.projectTrace (PSTRTMRawMulResident099.outputTriples a b)) (PSTRTMRawMulResident099.native_runs a b)
  have hr := PSTRTMMulProjectRun107.project_runs (PSTRTMRawMulResident099.outputTriples a b)
  rw [PSTRTMRawMulResident099.native_final_tape]
  exact ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1⟩

theorem rawProject_final_tape (a b : Nat) :
    (rawProjectFinal a b).Tape=Turing.Tape.mk₁ (PSTRTMIncrement009.blocks (productDigits a b)) :=
  PSTRTMMulProjectRun107.project_final_tape (PSTRTMRawMulResident099.outputTriples a b)

theorem blocks_runs (a b : Nat) :
    Runs canonicalBlocksMachine (encodeNat a++encodeNat b) (blocksTrace a b) (blocksFinal a b) := by
  apply PSTRTMSeq005.seq_runs rawProjectMachine PSTRTMTrimCode103.trimMachine (encodeNat a++encodeNat b)
    (rawProjectFinal a b) (PSTRTMTrimRun111.trimFinal (productDigits a b))
    (rawProjectTrace a b) (PSTRTMTrimRun111.trimTrace (productDigits a b)) (rawProject_runs a b)
  have hr := PSTRTMTrimRun111.trim_runs (productDigits a b)
  rw [rawProject_final_tape]
  exact ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1⟩

theorem blocks_final_tape (a b : Nat) :
    (blocksFinal a b).Tape=Turing.Tape.mk₁ (PSTRTMIncrement009.blocks (rawPayload (a*b))) := by
  have ht := PSTRTMTrimRun111.trim_final_tape (productDigits a b)
  change (blocksFinal a b).Tape=Turing.Tape.mk₁ (PSTRTMIncrement009.blocks
    (rawPayload (PSTRTMIncrement009.valueDigits (productDigits a b)))) at ht
  rw [productDigits_value] at ht
  exact ht

theorem native_runs (a b : Nat) :
    Runs nativeMulMachine (encodeNat a++encodeNat b) (nativeTrace a b) (nativeFinal a b) := by
  apply PSTRTMSeq005.seq_runs canonicalBlocksMachine PSTRTMUnblock018.unblockMachine (encodeNat a++encodeNat b)
    (blocksFinal a b) (PSTRTMUnblock018.state 19 [false] (PSTRTMUnblockTrace019.rawWord (rawPayload (a*b))))
    (blocksTrace a b) (PSTRTMUnblockTrace019.unblockTrace (rawPayload (a*b))) (blocks_runs a b)
  have hr := PSTRTMUnblockTrace019.unblock_runs (rawPayload (a*b))
  rw [blocks_final_tape]
  exact ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1⟩

theorem native_final_tape_canonical (a b : Nat) : (nativeFinal a b).Tape=Turing.Tape.mk₁ (encodeNat (a*b)) := by
  have hraw : PSTRTMUnblockTrace019.rawWord (rawPayload (a*b))=encodeNat (a*b) := by
    simp [PSTRTMUnblockTrace019.rawWord,rawPayload,encodeNat]
  have ht : (nativeFinal a b).Tape=Turing.Tape.mk₁ (PSTRTMUnblockTrace019.rawWord (rawPayload (a*b))) := by
    simp only [nativeFinal,PSTRTMSeq005.rightCfg,PSTRTMUnblock018.state,Turing.Tape.mk₁,Turing.Tape.mk₂]
    rw [PSTRTMRawNat010.blank_single_false]
  rw [ht,hraw]

theorem product_payload_length_le (a b : Nat) : (rawPayload (a*b)).length ≤ 2*(natBits a+natBits b)+1 := by
  have hc := PSTRTMTrimValue104.trimmed_canonical (productDigits a b)
  rw [productDigits_value] at hc
  have hl := PSTRTMTrimValue104.trimmed_length_le (productDigits a b)
  rw [hc,productDigits_length] at hl
  have ho := PSTRTMMulWidth108.outputTriples_length_le a b
  omega

theorem native_length_le (a b : Nat) :
    (nativeTrace a b).length ≤ 16384*(natBits a+natBits b+1)^2 := by
  have hr := PSTRTMRawMulResident099.native_length_le a b
  have hp := PSTRTMMulProjectRun107.project_length_le (PSTRTMRawMulResident099.outputTriples a b)
  have ht := PSTRTMTrimRun111.trim_length_le (productDigits a b)
  rw [productDigits_length] at ht
  have ho := PSTRTMMulWidth108.outputTriples_length_le a b
  have hu := product_payload_length_le a b
  have hos : (PSTRTMRawMulResident099.outputTriples a b).length+1 ≤ 2*(natBits a+natBits b+1) := by omega
  have hus : (rawPayload (a*b)).length ≤ 2*(natBits a+natBits b+1) := by omega
  have ho2 := Nat.pow_le_pow_left hos 2
  have hu2 := Nat.pow_le_pow_left hus 2
  simp only [nativeTrace,blocksTrace,rawProjectTrace,List.length_append,List.length_map,PSTRTMUnblockTrace019.unblock_length]
  nlinarith

theorem native_visitedSpace_le (a b : Nat) :
    visitedSpace nativeMulMachine (encodeNat a++encodeNat b).length (nativeTrace a b) ≤
      65536*(natBits a+natBits b+1)^2 := by
  have hs := PSTRTMTrace002.visitedSpace_le nativeMulMachine (encodeNat a++encodeNat b).length (nativeTrace a b)
  have ht := native_length_le a b
  simp only [List.length_append,PSTRTMLength004.encodeNat_length] at hs ⊢
  nlinarith

/-- EXACT original Nat product at BOTH original raw codec ends, all zero
and unequal-width cases included. Runtime is binary schoolbook arithmetic,
not multiplier-value repeated increment. Every codec/transport/erasure/
copy/branch/rewind/HALT is charged in the SAME concrete genuine Runs trace. -/
theorem encodeNat_mul_computes (a b : Nat) :
    computes nativeMulMachine (encodeNat a++encodeNat b) (encodeNat (a*b))
      (16384*(natBits a+natBits b+1)^2) (65536*(natBits a+natBits b+1)^2) := by
  refine ⟨nativeTrace a b,nativeFinal a b,native_runs a b,?_,native_length_le a b,native_visitedSpace_le a b⟩
  rw [native_final_tape_canonical]
  simp [Turing.Tape.mk₁,Turing.Tape.mk₂]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNativeMul112
