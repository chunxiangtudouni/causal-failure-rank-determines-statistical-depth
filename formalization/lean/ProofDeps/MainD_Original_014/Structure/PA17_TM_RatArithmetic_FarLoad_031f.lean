module
public import Structure.PA17_TM_RatArithmetic_FarLoad_031e

/-! Paid OWN00 initialization, the actual finite copy loop, and a final
outbound trip to DEST DATA. The original footer is FALSE at the final tape.
No source-head navigation or saved-bit restoration is claimed here. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFarLoad031
open Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)

def startupInitMachine (route : FarRoute) : Machine 22 :=
  PSTRTMSeq005.seqMachine (outDestMachine route) initOwnMachine
def startupBackMachine (route : FarRoute) : Machine 27 :=
  PSTRTMSeq005.seqMachine (startupInitMachine route) backFromDataMachine
def startupClearMachine (route : FarRoute) : Machine 29 :=
  PSTRTMSeq005.seqMachine (startupBackMachine route) (PA17TMRatArithmeticAllocate013.setMarkerMachine false)
def startupMachine (route : FarRoute) : Machine 56 :=
  PSTRTMSeq005.seqMachine (startupClearMachine route) route.back
def startupPort (route : FarRoute) : Fin 57 := PSTRTMSeq005.rightLabel (a:=29) route.backPort

theorem startup_bounded (route : FarRoute) (context : List Bool)
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

def finalOutMachine (route : FarRoute) : Machine 12 :=
  PSTRTMSeq005.seqMachine PA17TMRatArithmeticParse002.backOneMachine route.out
def finalMachine (route : FarRoute) : Machine 17 :=
  PSTRTMSeq005.seqMachine (finalOutMachine route) toDestMachine

def destinationLeft (gap : Nat) (archive : List Bool) : List Bool :=
  false::true::(List.replicate gap false++false::archive)

theorem final_bounded (route : FarRoute) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (routes : RouteCorrect route context finish cost) (left copied : List Bool) (gap : Nat) :
    BoundedRun (finalMachine route)
      (Tape.mk₂ (false::left) (context++false::workSuffix gap copied)) 17
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

def startupLoopMachine (route : FarRoute) : Machine 398 :=
  PSTRTMSeq005.seqMachine (startupMachine route) (loopMachine route)
def copyMachine (route : FarRoute) : Machine 416 :=
  PSTRTMSeq005.seqMachine (startupLoopMachine route) (finalMachine route)

theorem copy_bounded (route : FarRoute) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (routes : RouteCorrect route context finish cost) (archive digits : List Bool) (gap : Nat) :
    BoundedRun (copyMachine route)
      (Tape.mk₂ (false::archive) (fieldWord context digits (workSuffix gap []))) 416
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

theorem copy_contract (route : FarRoute) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (routes : RouteCorrect route context finish cost) (archive digits : List Bool) (gap inputLength : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (copyMachine route)
      ⟨0,Tape.mk₂ (false::archive) (fieldWord context digits (workSuffix gap []))⟩ trace
      ⟨416,Tape.mk₂ (destinationLeft gap (finish (false::archive) digits))
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

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFarLoad031
