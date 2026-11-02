module
public import Structure.RootB23_Threshold_Window_MarshalSerialize_Shift4_001
public import Structure.RootB23_Threshold_Uncapped_Serialize_008
public import Structure.PA17_TM_RatArithmetic_Width_018f
public import Common.PSTR_TM_ThresholdDenPrepare_141

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.Window.MarshalSerialize.SlideY
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PSTRTMIncrement009 PSTRTMRawNat010

def sixRightCode : Machine 7 := PSTRTMSeq005.seqMachine
  Uncapped.Steps.fourRightCode PA17TMRatArithmeticParse002.tagMachine
theorem sixRight_bounded (left word : List Bool) :
    BoundedRun sixRightCode (Tape.mk₂ left (false::false::false::false::true::false::word)) 7
      (Tape.mk₂ (false::true::false::false::false::false::left) word) 8 := by
  have four : BoundedRun Uncapped.Steps.fourRightCode
      (Tape.mk₂ left (false::false::false::false::true::false::word)) 4
      (Tape.mk₂ (false::false::false::false::left) (true::false::word)) 5 :=
    ⟨Uncapped.Steps.fourRightTrace left false false false false (true::false::word),
      Uncapped.Steps.fourRight_runsFrom _ _ _ _ _ _,by rfl⟩
  have two : BoundedRun PA17TMRatArithmeticParse002.tagMachine
      (Tape.mk₂ (false::false::false::false::left) (true::false::word)) 2
      (Tape.mk₂ (false::true::false::false::false::false::left) word) 3 :=
    ⟨PA17TMRatArithmeticParse002.tagTrace _ true false word,
      PA17TMRatArithmeticParse002.tag_runsFrom _ _ _ _,by rfl⟩
  exact four.seq two

def markerCode : Machine 8 := fun q _=>match q.val with
  | 0=>some (1,.write false)
  | 1=>some (2,.move .right)
  | 2=>some (3,.write false)
  | 3=>some (4,.move .right)
  | 4=>some (5,.write true)
  | 5=>some (6,.move .right)
  | 6=>some (7,.write false)
  | 7=>some (8,.move .right)
  | _=>none
def markerTrace (left tail : List Bool) : List (MachineState 8) :=
  [⟨0,Tape.mk₂ left (false::false::false::false::tail)⟩,
   ⟨1,Tape.mk₂ left (false::false::false::false::tail)⟩,
   ⟨2,Tape.mk₂ (false::left) (false::false::false::tail)⟩,
   ⟨3,Tape.mk₂ (false::left) (false::false::false::tail)⟩,
   ⟨4,Tape.mk₂ (false::false::left) (false::false::tail)⟩,
   ⟨5,Tape.mk₂ (false::false::left) (true::false::tail)⟩,
   ⟨6,Tape.mk₂ (true::false::false::left) (false::tail)⟩,
   ⟨7,Tape.mk₂ (true::false::false::left) (false::tail)⟩,
   ⟨8,Tape.mk₂ (false::true::false::false::left) tail⟩]
theorem marker_bounded (left tail : List Bool) :
    BoundedRun markerCode (Tape.mk₂ left (false::false::false::false::tail)) 8
      (Tape.mk₂ (false::true::false::false::left) tail) 9 := by
  refine ⟨markerTrace left tail,⟨rfl,?_,rfl,?_⟩,by rfl⟩
  · simp [markerTrace,List.isChain_cons_cons,TM0.step,markerCode,Tape.mk₂]
  · simp [TM0.step,markerCode]

def fourLeftCode : Machine 5 := PSTRTMSeq005.seqMachine
  PSTRTMThresholdDenPrepare141.twoLeftMachine PSTRTMThresholdDenPrepare141.twoLeftMachine
theorem fourLeft_bounded (left right : List Bool) :
    BoundedRun fourLeftCode (Tape.mk₂ (false::true::false::false::left) right) 5
      (Tape.mk₂ left (false::false::true::false::right)) 6 := by
  have first : BoundedRun PSTRTMThresholdDenPrepare141.twoLeftMachine
      (Tape.mk₂ (false::true::false::false::left) right) 2
      (Tape.mk₂ (false::false::left) (true::false::right)) 3 :=
    ⟨PSTRTMThresholdDenPrepare141.twoLeftTrace false true (false::false::left) right,
      PSTRTMThresholdDenPrepare141.twoLeft_runsFrom _ _ _ _,by rfl⟩
  have second : BoundedRun PSTRTMThresholdDenPrepare141.twoLeftMachine
      (Tape.mk₂ (false::false::left) (true::false::right)) 2
      (Tape.mk₂ left (false::false::true::false::right)) 3 :=
    ⟨PSTRTMThresholdDenPrepare141.twoLeftTrace false false left (true::false::right),
      PSTRTMThresholdDenPrepare141.twoLeft_runsFrom _ _ _ _,by rfl⟩
  exact first.seq second

def numShiftCode : Machine 42 := PSTRTMSeq005.seqMachine sixRightCode Shift4.code
def markerShiftCode : Machine 51 := PSTRTMSeq005.seqMachine numShiftCode markerCode
def denEntryCode : Machine 56 := PSTRTMSeq005.seqMachine markerShiftCode Uncapped.Steps.fourRightCode
def denShiftCode : Machine 91 := PSTRTMSeq005.seqMachine denEntryCode Shift4.code
def denBackCode : Machine 95 := PSTRTMSeq005.seqMachine denShiftCode PSTRTMMulRewind085.rewindMachine
def numEndCode : Machine 101 := PSTRTMSeq005.seqMachine denBackCode fourLeftCode
def code : Machine 105 := PSTRTMSeq005.seqMachine numEndCode PSTRTMMulRewind085.rewindMachine

def inputRight (num den suffix : List Bool) : List Bool :=
  false::false::false::false::true::false::
    (blocks num++Uncapped.Serialize.marker (blocks den++false::false::suffix))
def outputRight (num den suffix : List Bool) : List Bool :=
  blocks num++Uncapped.Serialize.marker
    (blocks den++false::false::false::false::false::false::suffix)

/-- The still-flagged Y fields really move LEFT4 into X's four residue
cells. Its 0010 separator is rewritten, four old trailing cells erased,
and both field heads reached by actual rewinds. The outer suffix stays
at exactly the same absolute boundary, with four new owned FALSE cells. -/
theorem actual_bounded (left num den suffix : List Bool) :
    BoundedRun code (Tape.mk₂ left (inputRight num den suffix)) 105
      (Tape.mk₂ (false::false::left) (outputRight num den suffix))
      (16*num.length+16*den.length+68) := by
  let numLeft:=leftBlocks num.reverse++false::false::left
  let markerLeft:=false::true::false::false::numLeft
  let denTail:=false::false::false::false::false::false::suffix
  have moved:=sixRight_bounded left
    (blocks num++Uncapped.Serialize.marker (blocks den++false::false::suffix))
  have numShift : BoundedRun Shift4.code
      (Tape.mk₂ (false::true::false::false::false::false::left)
        (blocks num++Uncapped.Serialize.marker (blocks den++false::false::suffix))) 34
      (Tape.mk₂ numLeft (false::false::false::false::false::false::true::false::
        (blocks den++false::false::suffix))) (14*num.length+17) :=
    ⟨Shift4.actualTrace (false::false::left) [] false true false false
        (true::false::(blocks den++false::false::suffix)) num,
      Shift4.shift_runsFrom _ _ _ _ _ _ _,by rw [Shift4.actual_length]⟩
  have marked:=marker_bounded numLeft (false::false::true::false::(blocks den++false::false::suffix))
  have denEntry : BoundedRun Uncapped.Steps.fourRightCode
      (Tape.mk₂ markerLeft (false::false::true::false::(blocks den++false::false::suffix))) 4
      (Tape.mk₂ (false::true::false::false::markerLeft) (blocks den++false::false::suffix)) 5 :=
    ⟨Uncapped.Steps.fourRightTrace markerLeft false false true false (blocks den++false::false::suffix),
      Uncapped.Steps.fourRight_runsFrom _ _ _ _ _ _,by rfl⟩
  have denShift : BoundedRun Shift4.code
      (Tape.mk₂ (false::true::false::false::markerLeft) (blocks den++false::false::suffix)) 34
      (Tape.mk₂ (leftBlocks den.reverse++markerLeft) denTail) (14*den.length+17) :=
    ⟨Shift4.actualTrace markerLeft [] false true false false suffix den,
      Shift4.shift_runsFrom _ _ _ _ _ _ _,by rw [Shift4.actual_length]⟩
  have denBack : BoundedRun PSTRTMMulRewind085.rewindMachine
      (Tape.mk₂ (leftBlocks den.reverse++markerLeft) denTail) 3
      (Tape.mk₂ markerLeft (blocks den++denTail)) (2*den.length+3) :=
    ⟨PSTRTMPairRewind105.fullTrace (true::false::false::numLeft) den.reverse denTail,
      PSTRTMPairRewind105.rewind_runsFrom _ _ _,
      by rw [PSTRTMPairRewind105.full_length,List.length_reverse]⟩
  have numEnd:=fourLeft_bounded numLeft (blocks den++denTail)
  have numBack : BoundedRun PSTRTMMulRewind085.rewindMachine
      (Tape.mk₂ numLeft (Uncapped.Serialize.marker (blocks den++denTail))) 3
      (Tape.mk₂ (false::false::left) (outputRight num den suffix)) (2*num.length+3) :=
    ⟨PSTRTMPairRewind105.fullTrace (false::left) num.reverse
      (Uncapped.Serialize.marker (blocks den++denTail)),
      PSTRTMPairRewind105.rewind_runsFrom _ _ _,
      by rw [PSTRTMPairRewind105.full_length,List.length_reverse]⟩
  have actual:=((((((moved.seq numShift).seq marked).seq denEntry).seq denShift).seq denBack).seq numEnd).seq numBack
  have port : PSTRTMSeq005.rightLabel (a:=101) (3 : Fin 4)=(105 : Fin 106) := by decide
  rw [port] at actual
  simpa only [code,numEndCode,denBackCode,denShiftCode,denEntryCode,markerShiftCode,numShiftCode,
    inputRight] using actual.mono (by omega :
      ((((((8+(14*num.length+17))+9)+5)+(14*den.length+17))+(2*den.length+3))+6)+
        (2*num.length+3)≤16*num.length+16*den.length+68)

end RootB23.Threshold.Window.MarshalSerialize.SlideY
