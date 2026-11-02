module
public import Structure.RootB23_Threshold_ReturnNineCopy_051

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnNineMarshal
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticFarLoad031
open PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow
open ReturnNineLayout (Data)

/-- The public frozen prepareCode physically plants the final TRUE and
returns to the last DATA. No shift, supplied footer or gap is assumed. -/
theorem prepare_bounded (archive digits : List Bool) :
    BoundedRun ReturnHeadroom.prepareCode (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits)) 13
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++[false,false,true])) (4*digits.length+13) := by
  let passed:=PSTRTMRawNat010.leftBlocks digits.reverse++false::archive
  have scan:=ReturnNineOut.scan_bounded (false::archive) digits []
  rw [PA17TMDivisionTape005.tape_owned00] at scan
  have forward:=MarshalAnchor.footer_any_bounded (false::passed) false []
  have planted : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine true)
      (Tape.mk₂ (false::false::passed) []) 1 (Tape.mk₂ (false::false::passed) [true]) 2 := by
    have actual : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine true)
        (Tape.mk₂ (false::false::passed) [false]) 1 (Tape.mk₂ (false::false::passed) [true]) 2 :=
      ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace false true _ [],
        PA17TMRatArithmeticAllocate013.setMarker_runsFrom _ _ _ _,by rfl⟩
    simpa only [Tape.mk₂,PSTRTMRawNat010.blank_single_false] using actual
  have backed : BoundedRun backOneMachine (Tape.mk₂ (false::false::passed) [true]) 1
      (Tape.mk₂ (false::passed) [false,true]) 2 :=
    ⟨backOneTrace (false::passed) false [true],backOne_runsFrom _ _ _,by rfl⟩
  have returned:=ReturnHeadroom.field_bounded archive digits [false,true]
  have actual:=(((scan.seq forward).seq planted).seq backed).seq returned
  have exit : PSTRTMSeq005.rightLabel (a:=7) (5 : Fin 6)=(13 : Fin 14) := by decide
  rw [exit] at actual
  simpa only [ReturnHeadroom.prepareCode,ReturnHeadroom.markerBackCode,ReturnHeadroom.plantCode,
    ReturnHeadroom.scanRightCode,passed,List.append_assoc] using actual.mono (by omega)

theorem cursor_false (left : List Bool) (previous : List (List Bool)) (first : false::left.tail=left) :
    false::(ReturnNineStep.cursor left previous).tail=ReturnNineStep.cursor left previous := by
  induction previous generalizing left with
  | nil=>exact first
  | cons a rest ih=>exact ih (PayloadNav.nextLeft left a) rfl

def word (v : Data) (memory : Fin 8) : List Bool := ReturnNineDest.core (ReturnNineCopy.fields v memory)++[false,true]

def returnCode : Machine 64 := PSTRTMSeq005.seqMachine CountAppend.fromDestinationMachine (ReturnNineDest.backCode 7)

theorem return_bounded (base : List Bool) (v : Data) (memory : Fin 8) (suffix : List Bool) :
    BoundedRun returnCode
      (Tape.mk₂ (ReturnNineStep.cursor (ReturnNineCopy.home base v) ((ReturnNineCopy.fields v memory).take 8))
        (PSTRTMIncrement009.blocks (ReturnNineStep.output v 7 memory)++[false,false,true]++suffix)) 64
      (Tape.mk₂ (ReturnNineCopy.home base v) (word v memory++suffix))
      (2*ReturnNineDest.width ((ReturnNineCopy.fields v memory).take 8)+68) := by
  let fields:=ReturnNineCopy.fields v memory
  let left:=ReturnNineCopy.home base v
  let last:=PSTRTMIncrement009.blocks (ReturnNineStep.output v 7 memory)++[false,false,true]++suffix
  have split : fields.take 7++[fields.getD 7 []]=fields.take 8 := ReturnNineCopy.fields_take v memory (7 : Fin 8)
  have finishEq : ReturnNineDest.finish left (fields.take 8)=
      PA17TMRatArithmeticAllocatePass023.pushField (ReturnNineStep.cursor left (fields.take 7)) (fields.getD 7 []) := by
    rw [←split,ReturnNineStep.finish_append]
  have cursorEq : ReturnNineStep.cursor left (fields.take 8)=
      PayloadNav.nextLeft (ReturnNineStep.cursor left (fields.take 7)) (fields.getD 7 []) := by
    rw [←split]
    simp only [ReturnNineStep.cursor,List.foldl_append,List.foldl_cons,List.foldl_nil]
  have connector:=CountAppend.fromDestination_bounded
    (PA17TMRatArithmeticAllocatePass023.pushField (ReturnNineStep.cursor left (fields.take 7)) (fields.getD 7 [])) last
  rw [←finishEq] at connector
  change BoundedRun CountAppend.fromDestinationMachine
    (Tape.mk₂ (PayloadNav.nextLeft (ReturnNineStep.cursor left (fields.take 7)) (fields.getD 7 [])) last) 3
    (Tape.mk₂ (ReturnNineDest.finish left (fields.take 8)) (false::true::false::last)) 4 at connector
  rw [←cursorEq] at connector
  have lengthEq : (fields.take 8).length=7+1 := rfl
  have backed:=ReturnNineDest.back_bounded 7 (fields.take 8) lengthEq left.tail (true::false::last)
  have leftEq : false::left.tail=left := rfl
  rw [leftEq] at backed
  have actual:=connector.seq backed
  have exit : PSTRTMSeq005.rightLabel (a:=3) (ReturnNineDest.backPort 7)=(64 : Fin 65) := by apply Fin.ext;rfl
  rw [exit] at actual
  have rightEq : ReturnNineDest.core (fields.take 8)++false::true::false::last=word v memory++suffix := by
    simp [fields,last,word,ReturnNineCopy.fields,ReturnNineDest.core,PA17TMRatArithmeticCopy006.workspace,List.append_assoc]
  rw [rightEq] at actual
  exact actual.mono (by dsimp only [fields];omega)

def preparedCode (memory : Fin 8) : Machine 11550 := PSTRTMSeq005.seqMachine (ReturnNineCopy.machine memory) ReturnHeadroom.prepareCode
def code (memory : Fin 8) : Machine 11615 := PSTRTMSeq005.seqMachine (preparedCode memory) returnCode

def fee (v : Data) (memory : Fin 8) : ℕ := ReturnNineCopy.fee v memory 8+
  (4*(ReturnNineStep.output v 7 memory).length+13)+
  (2*ReturnNineDest.width ((ReturnNineCopy.fields v memory).take 8)+68)

/-- All nine true copies, seven paid leading FALSE cells, eight actual
0010 delimiters and the physically written00TRUE ending. This is the
complete input of the frozen count5 serializer at the real B DATA head. -/
theorem bounded (base : List Bool) (v : Data) (memory : Fin 8) :
    BoundedRun (code memory)
      (ReturnNineBook.tapeAt base (ReturnNineOut.mask v) 1 (workSuffix 0 [])) 11615
      (Tape.mk₂ (ReturnNineCopy.home base v) (word v memory)) (fee v memory) := by
  let left:=ReturnNineStep.cursor (ReturnNineCopy.home base v) ((ReturnNineCopy.fields v memory).take 8)
  let digits:=ReturnNineStep.output v 7 memory
  have first:=ReturnNineCopy.bounded base v memory
  have prepared:=prepare_bounded left.tail digits
  have leftEq : false::left.tail=left := cursor_false _ _ rfl
  rw [leftEq] at prepared
  have blank : Tape.mk₂ left (PA17TMRatArithmeticCopy006.workspace digits)=Tape.mk₂ left (PSTRTMIncrement009.blocks digits) :=
    PA17TMDivisionTape005.tape_owned00 _ _
  rw [←blank] at prepared
  have returned:=return_bounded base v memory []
  simp only [List.append_nil] at returned
  have actual:=(first.seq prepared).seq returned
  have exit : PSTRTMSeq005.rightLabel (a:=11550) (64 : Fin 65)=(11615 : Fin 11616) := by decide
  rw [exit] at actual
  exact actual

end RootB23.Threshold.ReturnNineMarshal
