module
public import Structure.RootB23_Threshold_RoutedCopy_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.RoutedCopy
open PaperProofs.Common.Native.RationalControllerComputation Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031

def readerMachine : Machine 277 := padMachine (by decide : 8≤277) readMarkMachine

def readerPort (bit : Bool) : Fin 278 := if bit then 8 else 5

theorem reader_data_bounded (left : List Bool) (bit : Bool) (suffix : List Bool) :
    BoundedRun readerMachine (Tape.mk₂ left (bit::true::suffix)) (readerPort bit)
      (Tape.mk₂ (false::bit::left) suffix) 5 := by
  have h := pad_runsFrom (by decide : 8≤277) readMarkMachine _ _ _ (readMark_runsFrom left bit suffix)
  refine ⟨(readMarkTrace left bit suffix).map (padCfg (by decide : 8≤277)),?_,?_⟩
  · cases bit <;> exact h
  · rw [List.length_map,readMarkTrace_length]

theorem reader_eof_bounded (left suffix : List Bool) :
    BoundedRun readerMachine (Tape.mk₂ left (false::false::suffix)) 3
      (Tape.mk₂ (false::left) (false::suffix)) 3 := by
  have h := pad_runsFrom (by decide : 8≤277) readMarkMachine _ _ _ (eof_runsFrom left suffix)
  exact ⟨(eofTrace left suffix).map (padCfg (by decide : 8≤277)),h,
    by rw [List.length_map,eofTrace_length]⟩

def loopRows (route : Route) (phase : Fin 3) : Machine 277 :=
  if phase.val=0 then readerMachine else excursionMachine route (phase.val==2)

def loopPorts (phase : Fin 3) (localLabel : Fin 278) : Option (Fin 3 × Fin 278) :=
  if phase.val=0 then
    if localLabel.val=5 then some (1,0)
    else if localLabel.val=8 then some (2,0) else none
  else if localLabel.val=277 then some (0,0) else none

def loopMachine (route : Route) : Machine (totalStates 2 277) := blockMachine (loopRows route) loopPorts

theorem block_zero_three (tape : Tape Bool) :
    blockCfg (p:=2) (s:=277) 0 (⟨3,tape⟩ : MachineState 277)=
      (⟨3,tape⟩ : MachineState (totalStates 2 277)) := by
  have hq : label (p:=2) (s:=277) (0 : Fin 3) (3 : Fin 278)=
      (3 : Fin (totalStates 2 277+1)) := by decide
  change (⟨label (p:=2) (s:=277) 0 3,tape⟩ : MachineState (totalStates 2 277))=⟨3,tape⟩
  rw [hq]

theorem loop_bounded (route : Route) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (routes : RouteCorrect route context finish cost)
    (digits left copied : List Bool) (gap : Nat) :
    BoundedRun (loopMachine route)
      (Tape.mk₂ left (fieldWord context digits (workSuffix gap copied))) 3
      (Tape.mk₂ (false::passedLeft left digits)
        (context++false::workSuffix gap (copied++digits)))
      (loopFee cost gap copied digits) := by
  induction digits generalizing left copied with
  | nil =>
    have hc := context_false context (workSuffix gap copied) routes.end_false
    have hr := reader_eof_bounded left ((context++false::workSuffix gap copied).tail)
    rw [← hc] at hr
    obtain ⟨trace,hr,hl⟩ := hr
    have hb := block_runsFrom (loopRows route) loopPorts 0 _ _ trace hr (by rfl)
    refine ⟨trace.map (blockCfg (p:=2) (s:=277) (0 : Fin 3)),?_,?_⟩
    · simpa only [blockCfg_zero,block_zero_three,loopMachine,fieldWord,PSTRTMIncrement009.blocks,List.flatMap_nil,
        List.nil_append,List.append_nil,passedLeft] using hb
    · change (trace.map (blockCfg (p:=2) (s:=277) (0 : Fin 3))).length≤3
      simpa only [List.length_map] using hl
  | cons bit later ih =>
    let suffix := fieldWord context later (workSuffix gap copied)
    obtain ⟨tr,hr,hlr⟩ := reader_data_bounded left bit suffix
    have hre : PSTRTMSeq005.RunsFrom (loopRows route 0) ⟨0,Tape.mk₂ left (bit::true::suffix)⟩
        tr ⟨readerPort bit,Tape.mk₂ (false::bit::left) suffix⟩ := hr
    obtain ⟨te,he,hle⟩ := excursion_bounded route context finish cost routes left later copied bit gap
    have hee : PSTRTMSeq005.RunsFrom (loopRows route (PA17TMRatArithmeticBookmark014.readPort bit))
        ⟨0,Tape.mk₂ (false::bit::left) suffix⟩ te
        ⟨277,Tape.mk₂ (true::bit::left) (fieldWord context later (workSuffix gap (copied++[bit])))⟩ := by
      cases bit <;> exact he
    obtain ⟨ti,hi,hli⟩ := ih (true::bit::left) (copied++[bit])
    have hs := segment_append (loopMachine route) _ _ _ _ _ _
      (block_segment (loopRows route) loopPorts 0 _ _ tr hre)
      (block_segment (loopRows route) loopPorts (PA17TMRatArithmeticBookmark014.readPort bit) _ _ te hee)
      (block_transfer (loopRows route) loopPorts 0 _
        (PA17TMRatArithmeticBookmark014.readPort bit,0) hre.2.2.2 (by cases bit <;> rfl))
    have hs' := segment_append (loopMachine route) _ _ _ _ _ _ hs
      ⟨hi.1,hi.2.1,hi.2.2.1⟩
      (block_transfer (loopRows route) loopPorts (PA17TMRatArithmeticBookmark014.readPort bit) _
        (0,0) hee.2.2.2 (by cases bit <;> rfl))
    refine ⟨(tr.map (blockCfg (p:=2) (s:=277) (0 : Fin 3))++
      te.map (blockCfg (p:=2) (s:=277) (PA17TMRatArithmeticBookmark014.readPort bit)))++ti,?_,?_⟩
    · have h := segment_runsFrom _ _ _ _ hs' hi.2.2.2
      simpa only [blockCfg_zero,suffix,fieldWord,PSTRTMIncrement009.blocks,List.flatMap_cons,
        List.cons_append,List.nil_append,List.append_assoc,List.singleton_append,passedLeft] using h
    · simp only [List.length_append,List.length_map,loopFee]
      omega

theorem passedLeft_finish (route : Route) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (routes : RouteCorrect route context finish cost) (left digits : List Bool) :
    finish (passedLeft left digits) []=finish left digits := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    rw [passedLeft,ih,routes.finish_cons]


def startupInitMachine (route : Route) : Machine 112 :=
  PSTRTMSeq005.seqMachine (outDestMachine route) initOwnMachine
def startupBackMachine (route : Route) : Machine 117 :=
  PSTRTMSeq005.seqMachine (startupInitMachine route) backFromDataMachine
def startupClearMachine (route : Route) : Machine 119 :=
  PSTRTMSeq005.seqMachine (startupBackMachine route) (PA17TMRatArithmeticAllocate013.setMarkerMachine false)
def startupMachine (route : Route) : Machine 220 :=
  PSTRTMSeq005.seqMachine (startupClearMachine route) route.back
def startupPort (route : Route) : Fin 221 := PSTRTMSeq005.rightLabel (a:=119) route.backPort

theorem startup_bounded (route : Route) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (routes : RouteCorrect route context finish cost) (archive digits : List Bool) (gap : Nat) :
    BoundedRun (startupMachine route)
      (Tape.mk₂ (false::archive) (fieldWord context digits (workSuffix gap []))) (startupPort route)
      (Tape.mk₂ (false::archive) (fieldWord context digits (workSuffix gap [])))
      (4*digits.length+2*cost+2*gap+19) := by
  let left := finish (false::archive) digits
  have ho := routes.out_run (false::archive) digits (workSuffix gap [])
  have ht : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine true)
      (Tape.mk₂ left (false::workSuffix gap [])) 1
      (Tape.mk₂ left (true::workSuffix gap [])) 2 :=
    ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace false true left (workSuffix gap []),
      PA17TMRatArithmeticAllocate013.setMarker_runsFrom false true left (workSuffix gap []),by rfl⟩
  have hd := toDest_bounded gap left true (PA17TMRatArithmeticCopy006.workspace [])
  have hi : BoundedRun initOwnMachine
      (Tape.mk₂ (false::true::(List.replicate gap false++true::left))
        (PA17TMRatArithmeticCopy006.workspace [])) 4
      (Tape.mk₂ (false::true::(List.replicate gap false++true::left))
        (PA17TMRatArithmeticCopy006.workspace [])) 5 :=
    ⟨initOwnTrace _,initOwn_runsFrom_full _,by rfl⟩
  have hb := backFromData_bounded gap left (PA17TMRatArithmeticCopy006.workspace [])
  have hf : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine false)
      (Tape.mk₂ left (true::workSuffix gap [])) 1
      (Tape.mk₂ left (false::workSuffix gap [])) 2 :=
    ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace true false left (workSuffix gap []),
      PA17TMRatArithmeticAllocate013.setMarker_runsFrom true false left (workSuffix gap []),by rfl⟩
  have hr := routes.back_run archive digits (workSuffix gap [])
  have h := (((((ho.seq ht).seq hd).seq hi).seq hb).seq hf).seq hr
  exact h.mono (by omega)

def finalOutMachine (route : Route) : Machine 102 :=
  PSTRTMSeq005.seqMachine PA17TMRatArithmeticParse002.backOneMachine route.out
def finalMachine (route : Route) : Machine 107 :=
  PSTRTMSeq005.seqMachine (finalOutMachine route) toDestMachine

def destinationLeft (gap : Nat) (archive : List Bool) : List Bool :=
  false::true::(List.replicate gap false++false::archive)

theorem final_bounded (route : Route) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (routes : RouteCorrect route context finish cost) (left copied : List Bool) (gap : Nat) :
    BoundedRun (finalMachine route)
      (Tape.mk₂ (false::left) (context++false::workSuffix gap copied)) 107
      (Tape.mk₂ (destinationLeft gap (finish left [])) (PA17TMRatArithmeticCopy006.workspace copied))
      (cost+gap+7) := by
  have hl : BoundedRun PA17TMRatArithmeticParse002.backOneMachine
      (Tape.mk₂ (false::left) (context++false::workSuffix gap copied)) 1
      (Tape.mk₂ left (fieldWord context [] (workSuffix gap copied))) 2 :=
    ⟨PA17TMRatArithmeticParse002.backOneTrace left false (context++false::workSuffix gap copied),
      PA17TMRatArithmeticParse002.backOne_runsFrom left false (context++false::workSuffix gap copied),by rfl⟩
  have ho := routes.out_run left [] (workSuffix gap copied)
  have hd := toDest_bounded gap (finish left []) false (PA17TMRatArithmeticCopy006.workspace copied)
  exact ((hl.seq ho).seq hd).mono (by simp only [List.length_nil] ; omega)

def startupLoopMachine (route : Route) : Machine 1054 :=
  PSTRTMSeq005.seqMachine (startupMachine route) (loopMachine route)
def copyMachine (route : Route) : Machine 1162 :=
  PSTRTMSeq005.seqMachine (startupLoopMachine route) (finalMachine route)

theorem copy_bounded (route : Route) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (routes : RouteCorrect route context finish cost) (archive digits : List Bool) (gap : Nat) :
    BoundedRun (copyMachine route)
      (Tape.mk₂ (false::archive) (fieldWord context digits (workSuffix gap []))) 1162
      (Tape.mk₂ (destinationLeft gap (finish (false::archive) digits))
        (PA17TMRatArithmeticCopy006.workspace digits))
      (4*digits.length^2+(2*cost+2*gap+41)*digits.length+3*cost+3*gap+29) := by
  have hs := startup_bounded route context finish cost routes archive digits gap
  have hl := loop_bounded route context finish cost routes digits (false::archive) [] gap
  have hf := final_bounded route context finish cost routes (passedLeft (false::archive) digits) digits gap
  have he := passedLeft_finish route context finish cost routes (false::archive) digits
  rw [he] at hf
  have h := (hs.seq hl).seq hf
  have hb := loopFee_le cost gap [] digits
  simp only [List.length_nil] at hb
  exact h.mono (by nlinarith)

theorem copy_contract (route : Route) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (routes : RouteCorrect route context finish cost) (archive digits : List Bool) (gap inputLength : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (copyMachine route)
      ⟨0,Tape.mk₂ (false::archive) (fieldWord context digits (workSuffix gap []))⟩ trace
      ⟨1162,Tape.mk₂ (destinationLeft gap (finish (false::archive) digits))
        (PA17TMRatArithmeticCopy006.workspace digits)⟩ ∧
      trace.length≤4*digits.length^2+(2*cost+2*gap+41)*digits.length+3*cost+3*gap+29 ∧
      ∀ k, visitedSpace (copyMachine route) inputLength (trace.take k) ≤
        inputLength+2*(4*digits.length^2+(2*cost+2*gap+41)*digits.length+3*cost+3*gap+29)+1 := by
  obtain ⟨trace,hr,hl⟩ := copy_bounded route context finish cost routes archive digits gap
  refine ⟨trace,hr,hl,?_⟩
  intro k
  have hs := PSTRTMTrace002.visitedSpace_le (copyMachine route) inputLength (trace.take k)
  have hk : (trace.take k).length≤trace.length := by simp only [List.length_take]; omega
  omega


end RootB23.Threshold.RoutedCopy
