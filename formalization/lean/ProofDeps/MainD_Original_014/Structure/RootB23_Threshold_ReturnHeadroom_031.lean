module
public import Structure.RootB23_Threshold_ReturnFarActual_030

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnHeadroom
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticParse002
open PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow

def scanRightCode : Machine 3 := PSTRTMSeq005.seqMachine PA17TMRatArithmeticWidth018.scanMachine footerMachine
def plantCode : Machine 5 := PSTRTMSeq005.seqMachine scanRightCode (PA17TMRatArithmeticAllocate013.setMarkerMachine true)
def markerBackCode : Machine 7 := PSTRTMSeq005.seqMachine plantCode backOneMachine
def prepareCode : Machine 13 := PSTRTMSeq005.seqMachine markerBackCode fieldBackMachine
def shiftedCode : Machine 23 := PSTRTMSeq005.seqMachine prepareCode NatSplice.shiftMachine
def oneCode : Machine 29 := PSTRTMSeq005.seqMachine shiftedCode fieldBackMachine

theorem field_bounded (archive digits tail : List Bool) :
    BoundedRun fieldBackMachine (Tape.mk₂ (PA17TMRatArithmeticCopy006.sourceLeft archive digits) tail) 5
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++false::tail)) (2*digits.length+5) := by
  have port : PSTRTMSeq005.rightLabel (a:=1) (3 : Fin 4)=(5 : Fin 6) := by decide
  refine ⟨fieldBackTrace archive digits tail,?_,by rw [fieldBackTrace_length]⟩
  simpa only [fieldBackFinal,PA17TMRatArithmeticCopy006.sourceLeft,PSTRTMSeq005.rightCfg,
    PSTRTMMulRewind085.state,port] using fieldBack_runsFrom archive digits tail

/-- A real RIGHT1 of a flagged B field into its genuinely blank RIGHT:
write the necessary distant TRUE, rewind, run the paid FIFO shift, and
rewind again. The written TRUE is really cleared by the shift. -/
theorem one_bounded (archive digits : List Bool) :
    BoundedRun oneCode (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits)) 29
      (Tape.mk₂ (false::false::archive) (PSTRTMIncrement009.blocks digits)) (10*digits.length+24) := by
  let passed:=PSTRTMRawNat010.leftBlocks digits.reverse++false::archive
  have scan : BoundedRun PA17TMRatArithmeticWidth018.scanMachine
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++[false,false])) 1
      (Tape.mk₂ (false::passed) [false]) (2*digits.length+2) :=
    ⟨PA17TMRatArithmeticWidth018.scanTrace (false::archive) digits false [],
      PA17TMRatArithmeticWidth018.scan_runsFrom _ _ _ _,by rw [PA17TMRatArithmeticWidth018.scanTrace_length]⟩
  rw [PA17TMDivisionTape005.tape_owned00] at scan
  have forward:=MarshalAnchor.footer_any_bounded (false::passed) false []
  have planted : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine true)
      (Tape.mk₂ (false::false::passed) []) 1 (Tape.mk₂ (false::false::passed) [true]) 2 := by
    have actual : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine true)
        (Tape.mk₂ (false::false::passed) [false]) 1 (Tape.mk₂ (false::false::passed) [true]) 2 :=
      ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace false true (false::false::passed) [],
        PA17TMRatArithmeticAllocate013.setMarker_runsFrom _ _ _ _,by rfl⟩
    simpa only [Tape.mk₂,PSTRTMRawNat010.blank_single_false] using actual
  have backed : BoundedRun backOneMachine (Tape.mk₂ (false::false::passed) [true]) 1
      (Tape.mk₂ (false::passed) [false,true]) 2 :=
    ⟨backOneTrace (false::passed) false [true],backOne_runsFrom _ _ _,by rfl⟩
  have prepared:=field_bounded archive digits [false,true]
  have prepare:=(((scan.seq forward).seq planted).seq backed).seq prepared
  have preparePort : PSTRTMSeq005.rightLabel (a:=7) (5 : Fin 6)=(13 : Fin 14) := by decide
  rw [preparePort] at prepare
  have shifted : BoundedRun NatSplice.shiftMachine
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++false::false::true::[])) 9
      (Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::false::archive)) [false])
      (4*digits.length+6) :=
    ⟨NatSplice.shiftTrace false (false::archive) [] digits,NatSplice.shift_runsFrom _ _ _,by rw [NatSplice.shift_length]⟩
  have returned:=field_bounded (false::archive) digits [false]
  rw [PA17TMDivisionTape005.tape_owned00] at returned
  have actual:=(prepare.seq shifted).seq returned
  have port : PSTRTMSeq005.rightLabel (a:=23) (5 : Fin 6)=(29 : Fin 30) := by decide
  rw [port] at actual
  simpa only [oneCode,shiftedCode,prepareCode,markerBackCode,plantCode,scanRightCode] using actual.mono (by omega)

def twoCode : Machine 59 := PSTRTMSeq005.seqMachine oneCode oneCode
def fourCode : Machine 119 := PSTRTMSeq005.seqMachine twoCode twoCode
def code : Machine 239 := PSTRTMSeq005.seqMachine fourCode fourCode
theorem two_bounded (archive digits : List Bool) :
    BoundedRun twoCode (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits)) 59
      (Tape.mk₂ (false::false::false::archive) (PSTRTMIncrement009.blocks digits)) (20*digits.length+48) := by
  exact ((one_bounded archive digits).seq (one_bounded (false::archive) digits)).mono (by omega)
theorem four_bounded (archive digits : List Bool) :
    BoundedRun fourCode (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits)) 119
      (Tape.mk₂ (false::false::false::false::false::archive) (PSTRTMIncrement009.blocks digits)) (40*digits.length+96) := by
  exact ((two_bounded archive digits).seq (two_bounded (false::false::archive) digits)).mono (by omega)

/-- Fixed paid RIGHT8. The B/target consumer therefore inherits NINE
real owned FALSE cells, enough for the eventual count5 header, without
changing any caller archive cell or adding a room input. -/
theorem bounded (archive digits : List Bool) :
    BoundedRun code (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits)) 239
      (Tape.mk₂ (List.replicate 9 false++archive) (PSTRTMIncrement009.blocks digits)) (80*digits.length+192) := by
  exact ((four_bounded archive digits).seq (four_bounded (false::false::false::false::archive) digits)).mono (by omega)

end RootB23.Threshold.ReturnHeadroom
