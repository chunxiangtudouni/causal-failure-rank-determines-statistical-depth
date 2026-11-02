module
public import Common.PSTR_TM_CounterFrame_064
public import Common.PSTR_TM_Arithmetic_008

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdAddTwoFrame161
open PaperProofs.Common.Native.RationalControllerComputation

/-- Two actual binary increments of the finite fifteen-label counter,
including both physical carry rewinds and the real sequencing write.
Arbitrary actual archive is retained behind the real false guard. -/
def addTwoMachine : Machine 29 := PSTRTMSeq005.seqMachine
  PSTRTMIncrement009.incrementMachine PSTRTMIncrement009.incrementMachine

def addTwoTrace (archive : List Bool) (value : Nat) : List (MachineState 29) :=
  (PSTRTMCounterFrame064.counterTrace archive 0 (PSTRTMNatValue017.rawPayload value)).map
    (PSTRTMSeq005.leftCfg (b:=14)) ++
  (PSTRTMCounterFrame064.counterTrace archive 0 (PSTRTMNatValue017.rawPayload (value+1))).map
    (PSTRTMSeq005.rightCfg (a:=14))

def addTwoFinal (archive : List Bool) (value : Nat) : MachineState 29 :=
  PSTRTMSeq005.rightCfg (a:=14) (PSTRTMIncrement009.state 14 (false::archive)
    (PSTRTMIncrement009.blocks (PSTRTMIncrement009.bumpDigits (PSTRTMNatValue017.rawPayload (value+1)))))

theorem addTwo_runsFrom (archive : List Bool) (value : Nat) :
    PSTRTMSeq005.RunsFrom addTwoMachine
      ⟨0,Turing.Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload value))⟩
      (addTwoTrace archive value) (addTwoFinal archive value) := by
  apply PSTRTMSeq005.seq_runsFrom PSTRTMIncrement009.incrementMachine PSTRTMIncrement009.incrementMachine
    (PSTRTMIncrement009.state 0 (false::archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload value)))
    (PSTRTMIncrement009.state 14 (false::archive)
      (PSTRTMIncrement009.blocks (PSTRTMIncrement009.bumpDigits (PSTRTMNatValue017.rawPayload value))))
    (PSTRTMIncrement009.state 14 (false::archive)
      (PSTRTMIncrement009.blocks (PSTRTMIncrement009.bumpDigits (PSTRTMNatValue017.rawPayload (value+1)))))
    (PSTRTMCounterFrame064.counterTrace archive 0 (PSTRTMNatValue017.rawPayload value))
    (PSTRTMCounterFrame064.counterTrace archive 0 (PSTRTMNatValue017.rawPayload (value+1)))
    (PSTRTMCounterFrame064.counter_runsFrom archive _)
  simpa only [PSTRTMIncrement009.state,PSTRTMCanonical020.bump_rawPayload_eq] using
    PSTRTMCounterFrame064.counter_runsFrom archive (PSTRTMNatValue017.rawPayload (value+1))

theorem addTwo_final_tape (archive : List Bool) (value : Nat) :
    (addTwoFinal archive value).Tape=Turing.Tape.mk₂ (false::archive)
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (value+2))) := by
  simp only [addTwoFinal,PSTRTMSeq005.rightCfg,PSTRTMIncrement009.state,
    PSTRTMCanonical020.bump_rawPayload_eq,Nat.add_assoc]

theorem addTwo_length_le (archive : List Bool) (value : Nat) :
    (addTwoTrace archive value).length≤32*(natBits value+1) := by
  have h1 := PSTRTMCounterFrame064.counter_length_le archive 0 (PSTRTMNatValue017.rawPayload value)
  have h2 := PSTRTMCounterFrame064.counter_length_le archive 0 (PSTRTMNatValue017.rawPayload (value+1))
  have hb := PSTRTMArithmetic008.natBits_add_le value 1
  have ho : natBits 1=1 := by decide
  rw [ho] at hb
  have hl1 : (PSTRTMNatValue017.rawPayload value).length=natBits value := by
    simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn]
  have hl2 : (PSTRTMNatValue017.rawPayload (value+1)).length=natBits (value+1) := by
    simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn]
  rw [hl1] at h1
  rw [hl2] at h2
  simp only [addTwoTrace,List.length_append,List.length_map]
  omega

theorem addTwo_visitedSpace_le (archive : List Bool) (value : Nat) :
    visitedSpace addTwoMachine (archive.length+1+2*natBits value) (addTwoTrace archive value)≤
      archive.length+128*(natBits value+1) := by
  have ht := addTwo_length_le archive value
  have hs := PSTRTMTrace002.visitedSpace_le addTwoMachine (archive.length+1+2*natBits value) (addTwoTrace archive value)
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdAddTwoFrame161
