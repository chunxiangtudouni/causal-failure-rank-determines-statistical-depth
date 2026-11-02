module
public import Structure.PA17_TM_Division_Init_004g
public import Structure.PA17_TM_Division_Codec_003h
public import Common.PSTR_TM_AddCanonical_052

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionFront007
open PaperProofs.Common.Native.RationalControllerComputation

def frontPairs (a b : Nat) : List (Bool × Bool) :=
  PSTRTMPackCode036.digitPairs (PSTRTMNatValue017.rawPayload a) (PSTRTMNatValue017.rawPayload b)

/-- One fixed418-label original-input front. Both constituent programs
run on the same entire tape; seq005 charges its real transfer write. -/
def frontMachine : Machine 417 :=
  PSTRTMSeq005.seqMachine PSTRTMRawPack045.rawPackMachine PA17TMDivisionInit004.initMachine

def frontTrace (a b : Nat) : List (MachineState 417) :=
  (PSTRTMRawPack045.rawPackTrace (PSTRTMNatValue017.rawPayload a) (PSTRTMNatValue017.rawPayload b)).map
      (PSTRTMSeq005.leftCfg (b := 72)) ++
    (PA17TMDivisionInit004.initTrace (frontPairs a b)).map (PSTRTMSeq005.rightCfg (a := 344))

def frontFinal (a b : Nat) : MachineState 417 :=
  PSTRTMSeq005.rightCfg (a := 344) (PA17TMDivisionInit004.initFinal (frontPairs a b))

private theorem payload_length (a : Nat) : (PSTRTMNatValue017.rawPayload a).length = natBits a := by
  simp only [PSTRTMNatValue017.rawPayload, List.length_ofFn]

private theorem raw_runs (a b : Nat) :
    Runs PSTRTMRawPack045.rawPackMachine (encodeNat a ++ encodeNat b)
      (PSTRTMRawPack045.rawPackTrace (PSTRTMNatValue017.rawPayload a) (PSTRTMNatValue017.rawPayload b))
      (PSTRTMRawPack045.rawPackFinal (PSTRTMNatValue017.rawPayload a) (PSTRTMNatValue017.rawPayload b)) := by
  simpa only [PSTRTMTwoRawOperands029.rawInput, PSTRTMNatValue017.rawPayload,
    List.length_ofFn, encodeNat, List.append_assoc, List.singleton_append] using
    PSTRTMRawPack045.rawPack_runs (PSTRTMNatValue017.rawPayload a) (PSTRTMNatValue017.rawPayload b)

theorem front_runs (a b : Nat) :
    Runs frontMachine (encodeNat a ++ encodeNat b) (frontTrace a b) (frontFinal a b) := by
  apply PSTRTMSeq005.seq_runs PSTRTMRawPack045.rawPackMachine PA17TMDivisionInit004.initMachine
    (encodeNat a ++ encodeNat b)
    (PSTRTMRawPack045.rawPackFinal (PSTRTMNatValue017.rawPayload a) (PSTRTMNatValue017.rawPayload b))
    (PA17TMDivisionInit004.initFinal (frontPairs a b))
    (PSTRTMRawPack045.rawPackTrace (PSTRTMNatValue017.rawPayload a) (PSTRTMNatValue017.rawPayload b))
    (PA17TMDivisionInit004.initTrace (frontPairs a b)) (raw_runs a b)
  rw [PSTRTMRawPack045.rawPack_final_tape]
  exact PA17TMDivisionInit004.init_runsFrom (frontPairs a b)

/-- Complete shared layout, including the archive, separators, real high
zero column, blank exterior and actual head at the resident start. -/
theorem front_final_tape (a b : Nat) :
    (frontFinal a b).Tape =
      PA17TMDivisionCodec003.residentTape
        (PA17TMDivisionInit004.archivePairs (frontPairs a b))
        (PA17TMDivisionInit004.residentHigh (frontPairs a b)) :=
  PA17TMDivisionInit004.init_final_tape (frontPairs a b)

theorem front_final_label (a b : Nat) : (frontFinal a b).q = 417 := rfl

theorem frontPairs_values (a b : Nat) :
    PSTRTMBinaryAdd024.firstValue (frontPairs a b) = a ∧
      PSTRTMBinaryAdd024.secondValue (frontPairs a b) = b := by
  simpa only [frontPairs, PSTRTMNatValue017.valueDigits_rawPayload] using
    PSTRTMAddCanonical052.digitPairs_values (PSTRTMNatValue017.rawPayload a) (PSTRTMNatValue017.rawPayload b)

theorem front_archive_firstValue (a b : Nat) :
    PSTRTMBinaryAdd024.firstValue (PA17TMDivisionInit004.archivePairs (frontPairs a b)) = a := by
  rw [PA17TMDivisionInit004.firstValue_archivePairs, (frontPairs_values a b).1]

theorem front_resident_firstValue (a b : Nat) :
    PSTRTMBinaryAdd024.firstValue (PA17TMDivisionInit004.residentHigh (frontPairs a b)) = 0 :=
  PA17TMDivisionInit004.firstValue_residentHigh (frontPairs a b)

theorem front_resident_secondValue (a b : Nat) :
    PSTRTMBinaryAdd024.secondValue (PA17TMDivisionInit004.residentHigh (frontPairs a b)) = b := by
  rw [PA17TMDivisionInit004.secondValue_residentHigh, (frontPairs_values a b).2]

theorem frontPairs_length (a b : Nat) :
    (frontPairs a b).length = max (natBits a) (natBits b) := by
  simp only [frontPairs, PSTRTMPackCode036.digitPairs_length, PSTRTMNatValue017.rawPayload,
    List.length_ofFn]

theorem front_archive_length (a b : Nat) :
    (PA17TMDivisionInit004.archivePairs (frontPairs a b)).length = max (natBits a) (natBits b) := by
  rw [PA17TMDivisionInit004.archivePairs, List.length_map, frontPairs_length]

theorem front_resident_length (a b : Nat) :
    (PA17TMDivisionInit004.residentHigh (frontPairs a b)).length = max (natBits a) (natBits b) + 1 := by
  rw [PA17TMDivisionInit004.residentHigh_length, frontPairs_length]

theorem frontTrace_length_le (a b : Nat) :
    (frontTrace a b).length ≤ 4096 * (natBits a + natBits b + 1)^2 := by
  have hr := PSTRTMRawPack045.rawPack_length_le
    (PSTRTMNatValue017.rawPayload a) (PSTRTMNatValue017.rawPayload b)
  simp only [payload_length] at hr
  have hi := PA17TMDivisionInit004.init_length_le (frontPairs a b)
  have hn : (frontPairs a b).length + 1 ≤ natBits a + natBits b + 1 := by
    rw [frontPairs_length]
    have hm : max (natBits a) (natBits b) ≤ natBits a + natBits b :=
      max_le (by omega) (by omega)
    omega
  have hs := Nat.pow_le_pow_left hn 2
  simp only [frontTrace, List.length_append, List.length_map]
  nlinarith

theorem frontTrace_visitedSpace_le (a b : Nat) :
    visitedSpace frontMachine (encodeNat a ++ encodeNat b).length (frontTrace a b) ≤
      16384 * (natBits a + natBits b + 1)^2 := by
  have ht := frontTrace_length_le a b
  calc
    visitedSpace frontMachine (encodeNat a ++ encodeNat b).length (frontTrace a b) ≤
        (encodeNat a ++ encodeNat b).length + 2 * (frontTrace a b).length + 1 :=
      PSTRTMTrace002.visitedSpace_le frontMachine (encodeNat a ++ encodeNat b).length (frontTrace a b)
    _ ≤ 16384 * (natBits a + natBits b + 1)^2 := by
      simp only [List.length_append, PSTRTMLength004.encodeNat_length]
      nlinarith

/-- Unconditional original-input producer. No input width, aligned words,
archive, fuel, numerical answer or performance certificate is a premise. -/
theorem front_original (a b : Nat) :
    Runs frontMachine (encodeNat a ++ encodeNat b) (frontTrace a b) (frontFinal a b) ∧
    (frontFinal a b).Tape = PA17TMDivisionCodec003.residentTape
      (PA17TMDivisionInit004.archivePairs (frontPairs a b))
      (PA17TMDivisionInit004.residentHigh (frontPairs a b)) ∧
    PSTRTMBinaryAdd024.firstValue (PA17TMDivisionInit004.archivePairs (frontPairs a b)) = a ∧
    PSTRTMBinaryAdd024.firstValue (PA17TMDivisionInit004.residentHigh (frontPairs a b)) = 0 ∧
    PSTRTMBinaryAdd024.secondValue (PA17TMDivisionInit004.residentHigh (frontPairs a b)) = b ∧
    (PA17TMDivisionInit004.archivePairs (frontPairs a b)).length = max (natBits a) (natBits b) ∧
    (PA17TMDivisionInit004.residentHigh (frontPairs a b)).length = max (natBits a) (natBits b) + 1 ∧
    (frontTrace a b).length ≤ 4096 * (natBits a + natBits b + 1)^2 ∧
    visitedSpace frontMachine (encodeNat a ++ encodeNat b).length (frontTrace a b) ≤
      16384 * (natBits a + natBits b + 1)^2 :=
  ⟨front_runs a b, front_final_tape a b, front_archive_firstValue a b,
    front_resident_firstValue a b, front_resident_secondValue a b,
    front_archive_length a b, front_resident_length a b,
    frontTrace_length_le a b, frontTrace_visitedSpace_le a b⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionFront007
