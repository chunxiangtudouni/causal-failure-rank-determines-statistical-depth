module
public import PaperProofs.Common.PSTR_TM_B1Run_077

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNativeB1078
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMNatValue017

def pairs (numerator denominator : Nat) : List (Bool × Bool) :=
  PSTRTMPackCode036.digitPairs (rawPayload numerator) (rawPayload denominator)

def preparationMachine : Machine 376 := PSTRTMSeq005.seqMachine
  PSTRTMRawPack045.rawPackMachine PSTRTMB1PrepareCode069.prepareMachine
def blocksB1Machine : Machine 458 := PSTRTMSeq005.seqMachine preparationMachine PSTRTMB1LoopCode071.loopMachine
/-- ONE fixed479-label ordinary Bool program on the ORIGINAL raw two-Nat
input. No K, layout, counter, marker, width, answer or cost field is supplied. -/
def nativeB1Machine : Machine 478 := PSTRTMSeq005.seqMachine blocksB1Machine PSTRTMUnblock018.unblockMachine

def preparationTrace (numerator denominator : Nat) : List (MachineState 376) :=
  (PSTRTMRawPack045.rawPackTrace (rawPayload numerator) (rawPayload denominator)).map (PSTRTMSeq005.leftCfg (b:=31)) ++
    (PSTRTMB1PrepareTrace070.prepareTrace (pairs numerator denominator)).map (PSTRTMSeq005.rightCfg (a:=344))
def preparationFinal (numerator denominator : Nat) : MachineState 376 := PSTRTMSeq005.rightCfg (a:=344)
  (PSTRTMB1PrepareTrace070.prepareFinal (pairs numerator denominator))

def blocksTrace (numerator denominator : Nat) : List (MachineState 458) :=
  (preparationTrace numerator denominator).map (PSTRTMSeq005.leftCfg (b:=81)) ++
    (PSTRTMB1Run077.loopTrace numerator denominator).map (PSTRTMSeq005.rightCfg (a:=376))
def blocksFinal (numerator denominator : Nat) : MachineState 458 := PSTRTMSeq005.rightCfg (a:=376)
  (PSTRTMB1Run077.loopFinal numerator denominator)

def nativeTrace (numerator denominator : Nat) : List (MachineState 478) :=
  (blocksTrace numerator denominator).map (PSTRTMSeq005.leftCfg (b:=19)) ++
    (PSTRTMUnblockTrace019.unblockTrace (rawPayload (PSTRTMB1Value068.exponent numerator denominator))).map (PSTRTMSeq005.rightCfg (a:=458))
def nativeFinal (numerator denominator : Nat) : MachineState 478 := PSTRTMSeq005.rightCfg (a:=458)
  (PSTRTMUnblock018.state 19 [false] (PSTRTMUnblockTrace019.rawWord (rawPayload (PSTRTMB1Value068.exponent numerator denominator))))

private theorem payload_length (value : Nat) : (rawPayload value).length = natBits value := by
  simp only [rawPayload,List.length_ofFn]

theorem preparation_runs (numerator denominator : Nat) :
    Runs preparationMachine (encodeNat numerator++encodeNat denominator)
      (preparationTrace numerator denominator) (preparationFinal numerator denominator) := by
  apply PSTRTMSeq005.seq_runs PSTRTMRawPack045.rawPackMachine PSTRTMB1PrepareCode069.prepareMachine
    (encodeNat numerator++encodeNat denominator) (PSTRTMRawPack045.rawPackFinal (rawPayload numerator) (rawPayload denominator))
    (PSTRTMB1PrepareTrace070.prepareFinal (pairs numerator denominator))
    (PSTRTMRawPack045.rawPackTrace (rawPayload numerator) (rawPayload denominator))
    (PSTRTMB1PrepareTrace070.prepareTrace (pairs numerator denominator))
  · simpa only [PSTRTMTwoRawOperands029.rawInput,rawPayload,List.length_ofFn,encodeNat,List.append_assoc,List.singleton_append] using
      PSTRTMRawPack045.rawPack_runs (rawPayload numerator) (rawPayload denominator)
  · have hr := PSTRTMB1PrepareTrace070.prepare_runs (pairs numerator denominator)
    rw [PSTRTMRawPack045.rawPack_final_tape]
    exact ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1⟩

theorem preparation_final_tape (numerator denominator : Nat) :
    (preparationFinal numerator denominator).Tape = Turing.Tape.mk₁ (PSTRTMB1Run077.input numerator denominator) :=
  PSTRTMB1PrepareTrace070.prepare_final_tape (pairs numerator denominator)

theorem blocks_runs (numerator denominator : Nat) (hn : 0 < numerator) :
    Runs blocksB1Machine (encodeNat numerator++encodeNat denominator) (blocksTrace numerator denominator) (blocksFinal numerator denominator) := by
  apply PSTRTMSeq005.seq_runs preparationMachine PSTRTMB1LoopCode071.loopMachine
    (encodeNat numerator++encodeNat denominator) (preparationFinal numerator denominator) (PSTRTMB1Run077.loopFinal numerator denominator)
    (preparationTrace numerator denominator) (PSTRTMB1Run077.loopTrace numerator denominator) (preparation_runs numerator denominator)
  have hr := PSTRTMB1Run077.loop_runs numerator denominator hn
  rw [preparation_final_tape]
  exact ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1⟩

theorem blocks_final_tape (numerator denominator : Nat) :
    (blocksFinal numerator denominator).Tape = Turing.Tape.mk₁
      (PSTRTMIncrement009.blocks (rawPayload (PSTRTMB1Value068.exponent numerator denominator))) :=
  PSTRTMB1Run077.loop_final_tape numerator denominator

theorem native_runs (numerator denominator : Nat) (hn : 0 < numerator) :
    Runs nativeB1Machine (encodeNat numerator++encodeNat denominator) (nativeTrace numerator denominator) (nativeFinal numerator denominator) := by
  apply PSTRTMSeq005.seq_runs blocksB1Machine PSTRTMUnblock018.unblockMachine
    (encodeNat numerator++encodeNat denominator) (blocksFinal numerator denominator)
    (PSTRTMUnblock018.state 19 [false] (PSTRTMUnblockTrace019.rawWord (rawPayload (PSTRTMB1Value068.exponent numerator denominator))))
    (blocksTrace numerator denominator) (PSTRTMUnblockTrace019.unblockTrace (rawPayload (PSTRTMB1Value068.exponent numerator denominator)))
    (blocks_runs numerator denominator hn)
  have hr := PSTRTMUnblockTrace019.unblock_runs (rawPayload (PSTRTMB1Value068.exponent numerator denominator))
  rw [blocks_final_tape]
  exact ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1⟩

theorem native_final_tape_canonical (numerator denominator : Nat) :
    (nativeFinal numerator denominator).Tape = Turing.Tape.mk₁ (encodeNat (PSTRTMB1Value068.exponent numerator denominator)) := by
  have hraw : PSTRTMUnblockTrace019.rawWord (rawPayload (PSTRTMB1Value068.exponent numerator denominator)) =
      encodeNat (PSTRTMB1Value068.exponent numerator denominator) := by
    simp [PSTRTMUnblockTrace019.rawWord,rawPayload,encodeNat]
  have ht : (nativeFinal numerator denominator).Tape = Turing.Tape.mk₁
      (PSTRTMUnblockTrace019.rawWord (rawPayload (PSTRTMB1Value068.exponent numerator denominator))) := by
    simp only [nativeFinal,PSTRTMSeq005.rightCfg,PSTRTMUnblock018.state,Turing.Tape.mk₁,Turing.Tape.mk₂]
    rw [PSTRTMRawNat010.blank_single_false]
  rw [ht,hraw]

theorem pairs_length_le (numerator denominator : Nat) : (pairs numerator denominator).length ≤ natBits numerator+natBits denominator := by
  simp only [pairs,PSTRTMPackCode036.digitPairs_length,payload_length]
  exact max_le (by omega) (by omega)

theorem native_length_le (numerator denominator : Nat) (hn : 0 < numerator) :
    (nativeTrace numerator denominator).length ≤ 8192*(natBits numerator+natBits denominator+1)^2 := by
  have hr := PSTRTMRawPack045.rawPack_length_le (rawPayload numerator) (rawPayload denominator)
  simp only [payload_length] at hr
  have hl := PSTRTMB1Run077.loop_length_le numerator denominator hn
  have hp := pairs_length_le numerator denominator
  have hc := PSTRTMB1Invariant075.counter_payload_length_le numerator denominator (PSTRTMB1Value068.exponent numerator denominator) hn le_rfl
  have hcs : (rawPayload (PSTRTMB1Value068.exponent numerator denominator)).length ≤ natBits numerator+natBits denominator+1 := by omega
  have hsq := Nat.pow_le_pow_left hcs 2
  simp only [nativeTrace,blocksTrace,preparationTrace,List.length_append,List.length_map,
    PSTRTMB1PrepareTrace070.prepare_length,PSTRTMUnblockTrace019.unblock_length]
  nlinarith

theorem native_visitedSpace_le (numerator denominator : Nat) (hn : 0 < numerator) :
    visitedSpace nativeB1Machine (encodeNat numerator++encodeNat denominator).length (nativeTrace numerator denominator) ≤
      32768*(natBits numerator+natBits denominator+1)^2 := by
  have hs := PSTRTMTrace002.visitedSpace_le nativeB1Machine
    (encodeNat numerator++encodeNat denominator).length (nativeTrace numerator denominator)
  have ht := native_length_le numerator denominator hn
  simp only [List.length_append,PSTRTMLength004.encodeNat_length] at hs ⊢
  nlinarith

/-- Complete positive-numerator ORIGINAL raw two-Nat B1 scalar. Its loop
count, exact canonical output and bit-polynomial cost are all proved from
the SAME actual479-label Bool execution, not computability or labels. -/
theorem encodeNat_exponent_computes (numerator denominator : Nat) (hn : 0 < numerator) :
    computes nativeB1Machine (encodeNat numerator++encodeNat denominator)
      (encodeNat (PSTRTMB1Value068.exponent numerator denominator))
      (8192*(natBits numerator+natBits denominator+1)^2) (32768*(natBits numerator+natBits denominator+1)^2) := by
  refine ⟨nativeTrace numerator denominator,nativeFinal numerator denominator,native_runs numerator denominator hn,?_,
    native_length_le numerator denominator hn,native_visitedSpace_le numerator denominator hn⟩
  rw [native_final_tape_canonical]
  simp [Turing.Tape.mk₁,Turing.Tape.mk₂]

theorem encodeNat_controllerB_one_computes (numerator denominator : Nat) (hn : 0 < numerator) :
    computes nativeB1Machine (encodeNat numerator++encodeNat denominator)
      (encodeNat (PaperProofs.Statistics.controllerB ((numerator : Rat)/denominator) 1))
      (8192*(natBits numerator+natBits denominator+1)^2) (32768*(natBits numerator+natBits denominator+1)^2) := by
  rw [PSTRTMB1Value068.controllerB_one_ratio]
  exact encodeNat_exponent_computes numerator denominator hn

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNativeB1078
