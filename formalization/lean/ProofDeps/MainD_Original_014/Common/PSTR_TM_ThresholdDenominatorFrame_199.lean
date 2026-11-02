module
public import Common.PSTR_TM_ThresholdDoubleTrace_198
public import Common.PSTR_TM_CounterFrame_064
public import Common.PSTR_TM_Arithmetic_008

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDenominatorFrame199
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdDoubleTrace198

def firstMachine : Machine 38 :=
  PSTRTMSeq005.seqMachine PSTRTMIncrement009.incrementMachine doubleMachine

def firstTrace (archive : List Bool) (value : Nat) : List (MachineState 38) :=
  (PSTRTMCounterFrame064.counterTrace archive 0 (PSTRTMNatValue017.rawPayload value)).map
    (PSTRTMSeq005.leftCfg (b := 23)) ++
  (doubleTrace archive (PSTRTMNatValue017.rawPayload (value + 1))).map
    (PSTRTMSeq005.rightCfg (a := 14))

def firstFinal (archive : List Bool) (value : Nat) : MachineState 38 :=
  PSTRTMSeq005.rightCfg (a := 14) (doubleFinal archive (PSTRTMNatValue017.rawPayload (value + 1)))

theorem first_runsFrom (archive : List Bool) (value : Nat) :
    PSTRTMSeq005.RunsFrom firstMachine
      ⟨0,Turing.Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload value))⟩
      (firstTrace archive value) (firstFinal archive value) := by
  apply PSTRTMSeq005.seq_runsFrom PSTRTMIncrement009.incrementMachine doubleMachine
    (PSTRTMIncrement009.state 0 (false::archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload value)))
    (PSTRTMIncrement009.state 14 (false::archive)
      (PSTRTMIncrement009.blocks (PSTRTMIncrement009.bumpDigits (PSTRTMNatValue017.rawPayload value))))
    (doubleFinal archive (PSTRTMNatValue017.rawPayload (value + 1)))
    (PSTRTMCounterFrame064.counterTrace archive 0 (PSTRTMNatValue017.rawPayload value))
    (doubleTrace archive (PSTRTMNatValue017.rawPayload (value + 1)))
    (PSTRTMCounterFrame064.counter_runsFrom _ _)
  simpa only [PSTRTMIncrement009.state,PSTRTMCanonical020.bump_rawPayload_eq] using
    double_runsFrom archive (PSTRTMNatValue017.rawPayload (value + 1))

theorem first_final_tape (archive : List Bool) (value : Nat) :
    (firstFinal archive value).Tape = Turing.Tape.mk₂ (false::archive)
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (2*(value + 1)))) := by
  change (doubleFinal _ _).Tape = _
  rw [double_final_tape,false_cons_rawPayload _ (by omega)]

/-- Fixed63 labels form the exact target denominator4*(B+1), retaining
every archived source B/risk cell. The two doublings perform actual bit
transitions and rewinds; multiplication by a natural value is not primitive. -/
def denominatorMachine : Machine 62 := PSTRTMSeq005.seqMachine firstMachine doubleMachine

def denominatorTrace (archive : List Bool) (value : Nat) : List (MachineState 62) :=
  (firstTrace archive value).map (PSTRTMSeq005.leftCfg (b := 23)) ++
    (doubleTrace archive (PSTRTMNatValue017.rawPayload (2*(value + 1)))).map
      (PSTRTMSeq005.rightCfg (a := 38))

def denominatorFinal (archive : List Bool) (value : Nat) : MachineState 62 :=
  PSTRTMSeq005.rightCfg (a := 38)
    (doubleFinal archive (PSTRTMNatValue017.rawPayload (2*(value + 1))))

theorem denominator_runsFrom (archive : List Bool) (value : Nat) :
    PSTRTMSeq005.RunsFrom denominatorMachine
      ⟨0,Turing.Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload value))⟩
      (denominatorTrace archive value) (denominatorFinal archive value) := by
  apply PSTRTMSeq005.seq_runsFrom firstMachine doubleMachine
    ⟨0,Turing.Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload value))⟩
    (firstFinal archive value) (doubleFinal archive (PSTRTMNatValue017.rawPayload (2*(value + 1))))
    (firstTrace archive value) (doubleTrace archive (PSTRTMNatValue017.rawPayload (2*(value + 1))))
    (first_runsFrom _ _)
  rw [first_final_tape]
  exact double_runsFrom _ _

theorem denominator_final_tape (archive : List Bool) (value : Nat) :
    (denominatorFinal archive value).Tape = Turing.Tape.mk₂ (false::archive)
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (4*(value + 1)))) := by
  change (doubleFinal _ _).Tape = _
  rw [double_final_tape,false_cons_rawPayload _ (by omega)]
  have he : 2*(2*(value + 1)) = 4*(value + 1) := by omega
  rw [he]

theorem double_width (value : Nat) (hv : 0 < value) : natBits (2*value) = natBits value + 1 := by
  have hl := congrArg List.length (false_cons_rawPayload value hv)
  simpa only [List.length_cons,PSTRTMNatValue017.rawPayload,List.length_ofFn] using hl.symm

theorem denominator_length_le (archive : List Bool) (value : Nat) :
    (denominatorTrace archive value).length ≤ 64*(natBits value + 1) := by
  have hi := PSTRTMCounterFrame064.counter_length_le archive 0 (PSTRTMNatValue017.rawPayload value)
  have h1 := double_length archive (PSTRTMNatValue017.rawPayload (value + 1))
  have h2 := double_length archive (PSTRTMNatValue017.rawPayload (2*(value + 1)))
  have hl (n : Nat) : (PSTRTMNatValue017.rawPayload n).length = natBits n := by
    simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn]
  rw [hl] at hi h1 h2
  have hb := PSTRTMArithmetic008.natBits_add_le value 1
  have ho : natBits 1 = 1 := by decide
  rw [ho] at hb
  rw [double_width _ (by omega)] at h2
  simp only [denominatorTrace,firstTrace,List.length_append,List.length_map]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDenominatorFrame199
