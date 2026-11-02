module
public import Structure.PA17_TM_RatArithmetic_Store_019a

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticStore019

open Turing

local notation "Parser" => PA17TMRatArithmeticParse002.streamMachine

def decodeMachine : Machine 23 := PSTRTMSeq005.seqMachine anchorMachine Parser

/-- One fixed 28-label program. The original canonical bit-length header is
consumed by the frozen actual parser, never replaced by a supplied width. -/
def storeMachine : Machine 27 := PSTRTMSeq005.seqMachine decodeMachine closeMachine

def recordLeft (archive : List Bool) (n : Nat) : List Bool :=
  false::false::(PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload n).reverse ++
    false::true::archive)

def decodeTrace (archive : List Bool) (n : Nat) : List (MachineState 23) :=
  (anchorTrace archive (encodeNat n)).map (PSTRTMSeq005.leftCfg (b:=17)) ++
    (PA17TMRatArithmeticParse002.streamTrace (false::true::archive) []
      (PSTRTMNatValue017.rawPayload n) []).map (PSTRTMSeq005.rightCfg (a:=5))

def decodeFinal (archive : List Bool) (n : Nat) : MachineState 23 :=
  PSTRTMSeq005.rightCfg (a:=5)
    (PA17TMRatArithmeticParse002.streamFinal (false::true::archive)
      (PSTRTMNatValue017.rawPayload n) [])

theorem decode_runsFrom (archive : List Bool) (n : Nat) :
    PSTRTMSeq005.RunsFrom decodeMachine
      ⟨0,Tape.mk₂ (false::false::archive) (encodeNat n)⟩
      (decodeTrace archive n) (decodeFinal archive n) := by
  have hr := PSTRTMSeq005.seq_runsFrom anchorMachine Parser
    (anchorState 0 (false::false::archive) (encodeNat n))
    (anchorState 5 (false::true::archive) (encodeNat n))
    (PA17TMRatArithmeticParse002.streamFinal (false::true::archive)
      (PSTRTMNatValue017.rawPayload n) [])
    (anchorTrace archive (encodeNat n))
    (PA17TMRatArithmeticParse002.streamTrace (false::true::archive) []
      (PSTRTMNatValue017.rawPayload n) [])
    (anchor_runsFrom archive (encodeNat n))
    (by simpa only [anchorState,PA17TMRatArithmeticParse002.streamState,List.append_nil] using
      PA17TMRatArithmeticParse002.encodeNat_stream_runsFrom (false::true::archive) [] n)
  simpa only [decodeMachine,decodeTrace,decodeFinal,anchorState,PSTRTMSeq005.leftCfg,
    PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using hr

def storeTrace (archive : List Bool) (n : Nat) : List (MachineState 27) :=
  (decodeTrace archive n).map (PSTRTMSeq005.leftCfg (b:=3)) ++
    (closeTrace (false::(PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload n).reverse ++
      false::true::archive))).map (PSTRTMSeq005.rightCfg (a:=23))

def storeFinal (archive : List Bool) (n : Nat) : MachineState 27 :=
  PSTRTMSeq005.rightCfg (a:=23) (closeState 3 (recordLeft archive n) [true])

/-- Both HALT transfers are real write-self transitions, charged in this
trace. The entire old archive is retained beyond the newly written anchor. -/
theorem store_runsFrom (archive : List Bool) (n : Nat) :
    PSTRTMSeq005.RunsFrom storeMachine
      ⟨0,Tape.mk₂ (false::false::archive) (encodeNat n)⟩
      (storeTrace archive n) (storeFinal archive n) := by
  have hr := PSTRTMSeq005.seq_runsFrom decodeMachine closeMachine
    ⟨0,Tape.mk₂ (false::false::archive) (encodeNat n)⟩ (decodeFinal archive n)
    (closeState 3 (recordLeft archive n) [true]) (decodeTrace archive n)
    (closeTrace (false::(PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload n).reverse ++
      false::true::archive))) (decode_runsFrom archive n)
    (close_runsFrom (false::(PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload n).reverse ++
      false::true::archive)))
  simpa only [storeMachine,storeTrace,storeFinal,decodeFinal,
    PA17TMRatArithmeticParse002.streamFinal,PA17TMRatArithmeticParse002.streamState,
    closeState,recordLeft,PSTRTMSeq005.rightCfg,PSTRTMSeq005.leftCfg,
    PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using hr

theorem store_final_tape (archive : List Bool) (n : Nat) :
    (storeFinal archive n).Tape = Tape.mk₂ (recordLeft archive n) [true] := rfl

theorem store_final_halt (archive : List Bool) (n : Nat) :
    TM0.step storeMachine (storeFinal archive n) = none := (store_runsFrom archive n).2.2.2

private theorem payload_length (n : Nat) :
    (PSTRTMNatValue017.rawPayload n).length = natBits n := by
  simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn]

theorem storeTrace_length (archive : List Bool) (n : Nat) :
    (storeTrace archive n).length = (natBits n)^2+9*natBits n+12 := by
  simp only [storeTrace,decodeTrace,List.length_append,List.length_map,
    anchorTrace_length,closeTrace_length,PA17TMRatArithmeticParse002.streamTrace_length,payload_length]
  omega

theorem store_length_le (archive : List Bool) (n : Nat) :
    (storeTrace archive n).length ≤ 32*(natBits n+1)^2 := by
  rw [storeTrace_length]
  nlinarith [Nat.zero_le ((natBits n)^2)]

theorem store_prefix_space (archive : List Bool) (n prefixLength chargedLength : Nat) :
    visitedSpace storeMachine chargedLength ((storeTrace archive n).take prefixLength) ≤
      chargedLength+64*(natBits n+1)^2+1 := by
  have hs := PSTRTMTrace002.visitedSpace_le storeMachine chargedLength
    ((storeTrace archive n).take prefixLength)
  have ht := store_length_le archive n
  have hp : ((storeTrace archive n).take prefixLength).length ≤ (storeTrace archive n).length := by
    simp only [List.length_take]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticStore019
