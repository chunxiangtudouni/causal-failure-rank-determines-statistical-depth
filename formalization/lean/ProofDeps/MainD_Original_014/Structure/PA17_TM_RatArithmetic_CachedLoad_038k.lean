module
public import Structure.PA17_TM_RatArithmetic_CachedLoad_038j

/-! Paid plain OWN initialization and the one frozen042 loop. The output
is the real SOURCE EOF, ready for original-old-F or cached-LSB hooks. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticPairExcursion041 (SourceRoute SourceCorrect sourceWord)

def plainStartupInitMachine {a b : Nat} (route : SourceRoute a b) : Machine (a+12) :=
  PSTRTMSeq005.seqMachine (a:=a+7) (b:=4) (plainOutDestMachine route)
    PA17TMRatArithmeticFarLoad031.initOwnMachine
def plainStartupBackMachine {a b : Nat} (route : SourceRoute a b) : Machine (a+17) :=
  PSTRTMSeq005.seqMachine (a:=a+12) (b:=4) (plainStartupInitMachine route)
    PA17TMRatArithmeticFarLoad031.backFromDataMachine
def plainStartupClearMachine {a b : Nat} (route : SourceRoute a b) : Machine (a+19) :=
  PSTRTMSeq005.seqMachine (a:=a+17) (b:=1) (plainStartupBackMachine route)
    (PA17TMRatArithmeticAllocate013.setMarkerMachine route.footerBit)
def plainStartupMachine {a b : Nat} (route : SourceRoute a b) : Machine (a+19+b+1) :=
  PSTRTMSeq005.seqMachine (a:=a+19) (b:=b) (plainStartupClearMachine route) route.back
def plainStartupPort {a b : Nat} (route : SourceRoute a b) : Fin (a+19+b+1+1) :=
  PSTRTMSeq005.rightLabel (a:=a+19) route.backPort

theorem plain_startup_bounded {a b : Nat} (route : SourceRoute a b) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (routes : SourceCorrect route context finish cost) (archive digits : List Bool) (gap : Nat) :
    BoundedRun (plainStartupMachine route)
      (Tape.mk₂ (false::archive) (sourceWord route context digits (plainWorkSuffix gap []))) (plainStartupPort route)
      (Tape.mk₂ (false::archive) (sourceWord route context digits (plainWorkSuffix gap [])))
      (4*digits.length+2*cost+2*gap+19) := by
  let left := finish (false::archive) digits
  have ho := routes.out_run (false::archive) digits (plainWorkSuffix gap [])
  have ht : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine true)
      (Tape.mk₂ left (route.footerBit::plainWorkSuffix gap [])) 1
      (Tape.mk₂ left (true::plainWorkSuffix gap [])) 2 :=
    ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace route.footerBit true left (plainWorkSuffix gap []),
      PA17TMRatArithmeticAllocate013.setMarker_runsFrom route.footerBit true left (plainWorkSuffix gap []),by rfl⟩
  have hd := PA17TMRatArithmeticFarLoad031.toDest_bounded gap left true
    (PA17TMRatArithmeticCopy006.workspace [])
  have hi : BoundedRun PA17TMRatArithmeticFarLoad031.initOwnMachine
      (Tape.mk₂ (false::true::(List.replicate gap false++true::left))
        (PA17TMRatArithmeticCopy006.workspace [])) 4
      (Tape.mk₂ (false::true::(List.replicate gap false++true::left))
        (PA17TMRatArithmeticCopy006.workspace [])) 5 :=
    ⟨PA17TMRatArithmeticFarLoad031.initOwnTrace _,
      PA17TMRatArithmeticFarLoad031.initOwn_runsFrom_full _,by rfl⟩
  have hb := PA17TMRatArithmeticFarLoad031.backFromData_bounded gap left
    (PA17TMRatArithmeticCopy006.workspace [])
  have hf : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine route.footerBit)
      (Tape.mk₂ left (true::plainWorkSuffix gap [])) 1
      (Tape.mk₂ left (route.footerBit::plainWorkSuffix gap [])) 2 :=
    ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace true route.footerBit left (plainWorkSuffix gap []),
      PA17TMRatArithmeticAllocate013.setMarker_runsFrom true route.footerBit left (plainWorkSuffix gap []),by rfl⟩
  have hr := routes.back_run archive digits (plainWorkSuffix gap [])
  have combined := (((((ho.seq ht).seq hd).seq hi).seq hb).seq hf).seq hr
  have hc : ((((((2*digits.length+cost)+2)+(gap+5))+5)+(gap+5))+2)+(2*digits.length+cost)≤
      4*digits.length+2*cost+2*gap+19 := by omega
  simpa [plainStartupMachine,plainStartupClearMachine,plainStartupBackMachine,plainStartupInitMachine,
    plainOutDestMachine,plainOutSetMachine,plainStartupPort,plainWorkSuffix] using combined.mono hc

def plainBeforeCap (a b : Nat) : Nat := (a+19+b+1)+totalStates 2 (plainExcursionCap a b)+1
def plainBeforeMachine {a b : Nat} (route : SourceRoute a b) : Machine (plainBeforeCap a b) :=
  PSTRTMSeq005.seqMachine (a:=a+19+b+1) (b:=totalStates 2 (plainExcursionCap a b))
    (plainStartupMachine route) (plainLoopMachine route)
def plainBeforePort (a b : Nat) : Fin (plainBeforeCap a b+1) :=
  PSTRTMSeq005.rightLabel (a:=a+19+b+1) (plainLoopPort a b)

theorem plain_before_bounded {a b : Nat} (route : SourceRoute a b) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost gap : Nat) (archive digits : List Bool)
    (routes : SourceCorrect route context finish cost) (clamped : digits.headD false=false) :
    BoundedRun (plainBeforeMachine route)
      (Tape.mk₂ (false::archive) (sourceWord route context digits (plainWorkSuffix gap []))) (plainBeforePort a b)
      (Tape.mk₂ (false::PA17TMRatArithmeticFarLoad031.passedLeft (false::archive) digits)
        (context++route.footerBit::plainWorkSuffix gap digits))
      ((4*digits.length+2*cost+2*gap+19)+
        PA17TMRatArithmeticCopyLoop042.loopFee (plainLoopFee cost gap) [] digits) := by
  have hs := plain_startup_bounded route context finish cost routes archive digits gap
  have hl := plain_loop_bounded route context finish cost gap digits (false::archive) [] routes
    (by simpa only [List.nil_append] using clamped)
  simp only [List.nil_append] at hl
  simpa only [plainBeforeMachine,plainBeforeCap,plainBeforePort] using hs.seq hl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
