module
public import Structure.RootB23_Threshold_ReturnCopyCore_027

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnCopy
open PaperProofs.Common.Native.RationalControllerComputation Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031
open PA17TMRatArithmeticParse002

def loopRows (capped : Bool) (phase : Fin 3) : Machine 461 :=
  if phase.val=0 then readerMachine else excursionMachine capped (phase.val==2)
def loopPorts (phase : Fin 3) (localLabel : Fin 462) : Option (Fin 3 × Fin 462) :=
  if phase.val=0 then
    if localLabel.val=5 then some (1,0)
    else if localLabel.val=8 then some (2,0) else none
  else if localLabel.val=461 then some (0,0) else none
def loopMachine (capped : Bool) : Machine (totalStates 2 461) := blockMachine (loopRows capped) loopPorts

theorem block_zero_three (tape : Tape Bool) :
    blockCfg (p:=2) (s:=461) 0 (⟨3,tape⟩ : MachineState 461)=
      (⟨3,tape⟩ : MachineState (totalStates 2 461)) := by
  have equal : label (p:=2) (s:=461) (0 : Fin 3) (3 : Fin 462)=
      (3 : Fin (totalStates 2 461+1)) := by decide
  change (⟨label (p:=2) (s:=461) 0 3,tape⟩ : MachineState (totalStates 2 461))=⟨3,tape⟩
  rw [equal]

theorem loop_bounded (capped : Bool) (x y q : Rat) (nonnegative : 0≤x) (qNonnegative : 0≤q)
    (credit : ℕ) (digits left copied : List Bool) (gap : ℕ) :
    BoundedRun (loopMachine capped)
      (Tape.mk₂ left (RoutedCopy.fieldWord (ReturnRoute.context capped x y q credit) digits (workSuffix gap copied))) 3
      (Tape.mk₂ (false::passedLeft left digits)
        (ReturnRoute.context capped x y q credit++false::workSuffix gap (copied++digits)))
      (loopFee (ReturnRoute.cost capped x y q credit) gap copied digits) := by
  induction digits generalizing left copied with
  | nil=>
    have contextHead:=context_false (ReturnRoute.context capped x y q credit) (workSuffix gap copied) rfl
    have read:=reader_eof_bounded left ((ReturnRoute.context capped x y q credit++false::workSuffix gap copied).tail)
    rw [←contextHead] at read
    obtain ⟨trace,run,fee⟩:=read
    have lifted:=block_runsFrom (loopRows capped) loopPorts 0 _ _ trace run (by rfl)
    refine ⟨trace.map (blockCfg (p:=2) (s:=461) (0 : Fin 3)),?_,?_⟩
    · simpa only [blockCfg_zero,block_zero_three,loopMachine,RoutedCopy.fieldWord,PSTRTMIncrement009.blocks,
        List.flatMap_nil,List.nil_append,List.append_nil,passedLeft] using lifted
    · change (trace.map (blockCfg (p:=2) (s:=461) (0 : Fin 3))).length≤3
      simpa only [List.length_map] using fee
  | cons bit later ih=>
    let suffix:=RoutedCopy.fieldWord (ReturnRoute.context capped x y q credit) later (workSuffix gap copied)
    obtain ⟨tr,read,readFee⟩:=reader_data_bounded left bit suffix
    have readRow : PSTRTMSeq005.RunsFrom (loopRows capped 0) ⟨0,Tape.mk₂ left (bit::true::suffix)⟩
        tr ⟨readerPort bit,Tape.mk₂ (false::bit::left) suffix⟩ := read
    obtain ⟨te,excursion,excursionFee⟩:=excursion_bounded capped x y q nonnegative qNonnegative credit left later copied bit gap
    have excursionRow : PSTRTMSeq005.RunsFrom (loopRows capped (PA17TMRatArithmeticBookmark014.readPort bit))
        ⟨0,Tape.mk₂ (false::bit::left) suffix⟩ te
        ⟨461,Tape.mk₂ (true::bit::left)
          (RoutedCopy.fieldWord (ReturnRoute.context capped x y q credit) later (workSuffix gap (copied++[bit])))⟩ := by
      cases bit <;> exact excursion
    obtain ⟨ti,tailRun,tailFee⟩:=ih (true::bit::left) (copied++[bit])
    have front:=segment_append (loopMachine capped) _ _ _ _ _ _
      (block_segment (loopRows capped) loopPorts 0 _ _ tr readRow)
      (block_segment (loopRows capped) loopPorts (PA17TMRatArithmeticBookmark014.readPort bit) _ _ te excursionRow)
      (block_transfer (loopRows capped) loopPorts 0 _
        (PA17TMRatArithmeticBookmark014.readPort bit,0) readRow.2.2.2 (by cases bit <;> rfl))
    have joined:=segment_append (loopMachine capped) _ _ _ _ _ _ front
      ⟨tailRun.1,tailRun.2.1,tailRun.2.2.1⟩
      (block_transfer (loopRows capped) loopPorts (PA17TMRatArithmeticBookmark014.readPort bit) _
        (0,0) excursionRow.2.2.2 (by cases bit <;> rfl))
    refine ⟨(tr.map (blockCfg (p:=2) (s:=461) (0 : Fin 3))++
      te.map (blockCfg (p:=2) (s:=461) (PA17TMRatArithmeticBookmark014.readPort bit)))++ti,?_,?_⟩
    · have actual:=segment_runsFrom _ _ _ _ joined tailRun.2.2.2
      simpa only [blockCfg_zero,suffix,RoutedCopy.fieldWord,PSTRTMIncrement009.blocks,List.flatMap_cons,
        List.cons_append,List.nil_append,List.append_assoc,List.singleton_append,passedLeft] using actual
    · simp only [List.length_append,List.length_map,loopFee]
      omega

theorem passedLeft_finish (capped : Bool) (x y q : Rat) (credit : ℕ) (left digits : List Bool) :
    ReturnRoute.finish capped x y q credit (passedLeft left digits) []=
      ReturnRoute.finish capped x y q credit left digits := by
  induction digits generalizing left with
  | nil=>rfl
  | cons bit later ih=>rw [passedLeft,ih,ReturnRoute.finish_cons]

def startupInitMachine (capped : Bool) : Machine 204 := PSTRTMSeq005.seqMachine (outDestMachine capped) initOwnMachine
def startupBackMachine (capped : Bool) : Machine 209 := PSTRTMSeq005.seqMachine (startupInitMachine capped) backFromDataMachine
def startupClearMachine (capped : Bool) : Machine 211 :=
  PSTRTMSeq005.seqMachine (startupBackMachine capped) (PA17TMRatArithmeticAllocate013.setMarkerMachine false)
def startupMachine (capped : Bool) : Machine 404 := PSTRTMSeq005.seqMachine (startupClearMachine capped) (ReturnRoute.back capped)
def startupPort (capped : Bool) : Fin 405 := PSTRTMSeq005.rightLabel (a:=211) (ReturnRoute.backPort capped)

theorem startup_bounded (capped : Bool) (x y q : Rat) (nonnegative : 0≤x) (qNonnegative : 0≤q)
    (credit : ℕ) (archive digits : List Bool) (gap : ℕ) :
    BoundedRun (startupMachine capped)
      (Tape.mk₂ (false::archive) (RoutedCopy.fieldWord (ReturnRoute.context capped x y q credit) digits (workSuffix gap [])))
      (startupPort capped)
      (Tape.mk₂ (false::archive) (RoutedCopy.fieldWord (ReturnRoute.context capped x y q credit) digits (workSuffix gap [])))
      (4*digits.length+2*ReturnRoute.cost capped x y q credit+2*gap+19) := by
  let left:=ReturnRoute.finish capped x y q credit (false::archive) digits
  have ho:=out_bounded capped x y q nonnegative credit (false::archive) digits (workSuffix gap [])
  have ht : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine true)
      (Tape.mk₂ left (false::workSuffix gap [])) 1 (Tape.mk₂ left (true::workSuffix gap [])) 2 :=
    ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace false true left (workSuffix gap []),
      PA17TMRatArithmeticAllocate013.setMarker_runsFrom _ _ _ _,by rfl⟩
  have hd:=toDest_bounded gap left true (PA17TMRatArithmeticCopy006.workspace [])
  have hi : BoundedRun initOwnMachine
      (Tape.mk₂ (false::true::(List.replicate gap false++true::left)) (PA17TMRatArithmeticCopy006.workspace [])) 4
      (Tape.mk₂ (false::true::(List.replicate gap false++true::left)) (PA17TMRatArithmeticCopy006.workspace [])) 5 :=
    ⟨initOwnTrace _,initOwn_runsFrom_full _,by rfl⟩
  have hb:=backFromData_bounded gap left (PA17TMRatArithmeticCopy006.workspace [])
  have hf : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine false)
      (Tape.mk₂ left (true::workSuffix gap [])) 1 (Tape.mk₂ left (false::workSuffix gap [])) 2 :=
    ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace true false left (workSuffix gap []),
      PA17TMRatArithmeticAllocate013.setMarker_runsFrom _ _ _ _,by rfl⟩
  have hr:=back_bounded capped x y q nonnegative qNonnegative credit archive digits (workSuffix gap [])
  have actual:=(((((ho.seq ht).seq hd).seq hi).seq hb).seq hf).seq hr
  exact actual.mono (by omega)

def finalOutMachine (capped : Bool) : Machine 194 := PSTRTMSeq005.seqMachine backOneMachine (ReturnRoute.out capped)
def finalMachine (capped : Bool) : Machine 199 := PSTRTMSeq005.seqMachine (finalOutMachine capped) toDestMachine
theorem final_bounded (capped : Bool) (x y q : Rat) (nonnegative : 0≤x)
    (credit : ℕ) (left copied : List Bool) (gap : ℕ) :
    BoundedRun (finalMachine capped)
      (Tape.mk₂ (false::left) (ReturnRoute.context capped x y q credit++false::workSuffix gap copied)) 199
      (Tape.mk₂ (RoutedCopy.destinationLeft gap (ReturnRoute.finish capped x y q credit left []))
        (PA17TMRatArithmeticCopy006.workspace copied))
      (ReturnRoute.cost capped x y q credit+gap+7) := by
  have hl : BoundedRun backOneMachine
      (Tape.mk₂ (false::left) (ReturnRoute.context capped x y q credit++false::workSuffix gap copied)) 1
      (Tape.mk₂ left (RoutedCopy.fieldWord (ReturnRoute.context capped x y q credit) [] (workSuffix gap copied))) 2 :=
    ⟨backOneTrace left false _,backOne_runsFrom _ _ _,by rfl⟩
  have ho:=out_bounded capped x y q nonnegative credit left [] (workSuffix gap copied)
  have hd:=toDest_bounded gap (ReturnRoute.finish capped x y q credit left []) false (PA17TMRatArithmeticCopy006.workspace copied)
  exact ((hl.seq ho).seq hd).mono (by simp only [List.length_nil];omega)

def startupLoopMachine (capped : Bool) : Machine 1790 := PSTRTMSeq005.seqMachine (startupMachine capped) (loopMachine capped)
def copyMachine (capped : Bool) : Machine 1990 := PSTRTMSeq005.seqMachine (startupLoopMachine capped) (finalMachine capped)
def copyFee (capped : Bool) (x y q : Rat) (credit : ℕ) (digits : List Bool) (gap : ℕ) : ℕ :=
  4*digits.length^2+(2*ReturnRoute.cost capped x y q credit+2*gap+41)*digits.length+
    3*ReturnRoute.cost capped x y q credit+3*gap+29

theorem copy_bounded (capped : Bool) (x y q : Rat) (nonnegative : 0≤x) (qNonnegative : 0≤q)
    (credit : ℕ) (archive digits : List Bool) (gap : ℕ) :
    BoundedRun (copyMachine capped)
      (Tape.mk₂ (false::archive) (RoutedCopy.fieldWord (ReturnRoute.context capped x y q credit) digits (workSuffix gap []))) 1990
      (Tape.mk₂ (RoutedCopy.destinationLeft gap (ReturnRoute.finish capped x y q credit (false::archive) digits))
        (PA17TMRatArithmeticCopy006.workspace digits)) (copyFee capped x y q credit digits gap) := by
  have startup:=startup_bounded capped x y q nonnegative qNonnegative credit archive digits gap
  have loop:=loop_bounded capped x y q nonnegative qNonnegative credit digits (false::archive) [] gap
  have final:=final_bounded capped x y q nonnegative credit (passedLeft (false::archive) digits) digits gap
  have same:=passedLeft_finish capped x y q credit (false::archive) digits
  rw [same] at final
  have actual:=(startup.seq loop).seq final
  have loopFeeBound:=loopFee_le (ReturnRoute.cost capped x y q credit) gap [] digits
  simp only [List.length_nil] at loopFeeBound
  exact actual.mono (by dsimp only [copyFee];nlinarith)

end RootB23.Threshold.ReturnCopy
