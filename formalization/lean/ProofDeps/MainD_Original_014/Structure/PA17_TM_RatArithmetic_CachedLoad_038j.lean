module
public import Structure.PA17_TM_RatArithmetic_CachedLoad_038i

/-! Generic SOURCE routes with the frozen plain destination kernels. This
is the plain counterpart of041's shared-B excursion. Actual read/mark/loop
control and its induction remain the SAME frozen042 program. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticPairExcursion041 (SourceRoute SourceCorrect sourceWord)

def plainWorkSuffix (gap : Nat) (copied : List Bool) : List Bool :=
  PA17TMRatArithmeticFarLoad031.workSuffix gap copied

def plainOutSetMachine {a b : Nat} (route : SourceRoute a b) : Machine (a+2) :=
  PSTRTMSeq005.seqMachine (a:=a) (b:=1) route.out
    (PA17TMRatArithmeticAllocate013.setMarkerMachine true)
def plainOutDestMachine {a b : Nat} (route : SourceRoute a b) : Machine (a+7) :=
  PSTRTMSeq005.seqMachine (a:=a+2) (b:=4) (plainOutSetMachine route)
    PA17TMRatArithmeticFarLoad031.toDestMachine
def plainOutAppendMachine {a b : Nat} (route : SourceRoute a b) (bit : Bool) : Machine (a+66) :=
  PSTRTMSeq005.seqMachine (a:=a+7) (b:=58) (plainOutDestMachine route)
    (PA17TMRatArithmeticFarLoad031.appendStartMachine bit)
def plainOutBackMachine {a b : Nat} (route : SourceRoute a b) (bit : Bool) : Machine (a+70) :=
  PSTRTMSeq005.seqMachine (a:=a+66) (b:=3) (plainOutAppendMachine route bit)
    PA17TMRatArithmeticFarLoad031.backFromGuardMachine
def plainOutClearMachine {a b : Nat} (route : SourceRoute a b) (bit : Bool) : Machine (a+72) :=
  PSTRTMSeq005.seqMachine (a:=a+70) (b:=1) (plainOutBackMachine route bit)
    (PA17TMRatArithmeticAllocate013.setMarkerMachine route.footerBit)
def plainOutReturnMachine {a b : Nat} (route : SourceRoute a b) (bit : Bool) : Machine (a+72+b+1) :=
  PSTRTMSeq005.seqMachine (a:=a+72) (b:=b) (plainOutClearMachine route bit) route.back
def plainExcursionCap (a b : Nat) : Nat := a+72+b+5
def plainExcursionMachine {a b : Nat} (route : SourceRoute a b) (bit : Bool) : Machine (plainExcursionCap a b) :=
  PSTRTMSeq005.seqMachine (a:=a+72+b+1) (b:=3) (plainOutReturnMachine route bit)
    PA17TMRatArithmeticAllocatePass023.restoreBackMachine

theorem plain_excursion_bounded {a b : Nat} (route : SourceRoute a b) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (routes : SourceCorrect route context finish cost)
    (left later copied : List Bool) (bit : Bool) (gap : Nat) :
    BoundedRun (plainExcursionMachine route bit)
      (Tape.mk₂ (false::bit::left) (sourceWord route context later (plainWorkSuffix gap copied)))
      (Fin.last (plainExcursionCap a b))
      (Tape.mk₂ (true::bit::left) (sourceWord route context later (plainWorkSuffix gap (copied++[bit]))))
      (4*later.length+2*cost+2*gap+4*copied.length+32) := by
  let archive := finish (false::bit::left) later
  have ho := routes.out_run (false::bit::left) later (plainWorkSuffix gap copied)
  have ht : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine true)
      (Tape.mk₂ archive (route.footerBit::plainWorkSuffix gap copied)) 1
      (Tape.mk₂ archive (true::plainWorkSuffix gap copied)) 2 :=
    ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace route.footerBit true archive (plainWorkSuffix gap copied),
      PA17TMRatArithmeticAllocate013.setMarker_runsFrom route.footerBit true archive (plainWorkSuffix gap copied),by rfl⟩
  have hd := PA17TMRatArithmeticFarLoad031.toDest_bounded gap archive true
    (PA17TMRatArithmeticCopy006.workspace copied)
  have ha := PA17TMRatArithmeticFarLoad031.appendStart_bounded bit
    (true::(List.replicate gap false++true::archive)) copied
  have hb := PA17TMRatArithmeticFarLoad031.backFromGuard_bounded gap archive
    (PA17TMRatArithmeticCopy006.workspace (copied++[bit]))
  have hf : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine route.footerBit)
      (Tape.mk₂ archive (true::plainWorkSuffix gap (copied++[bit]))) 1
      (Tape.mk₂ archive (route.footerBit::plainWorkSuffix gap (copied++[bit]))) 2 :=
    ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace true route.footerBit archive (plainWorkSuffix gap (copied++[bit])),
      PA17TMRatArithmeticAllocate013.setMarker_runsFrom true route.footerBit archive (plainWorkSuffix gap (copied++[bit])),by rfl⟩
  have hr := routes.back_run (bit::left) later (plainWorkSuffix gap (copied++[bit]))
  have hs : BoundedRun PA17TMRatArithmeticAllocatePass023.restoreBackMachine
      (Tape.mk₂ (false::bit::left) (sourceWord route context later (plainWorkSuffix gap (copied++[bit])))) 3
      (Tape.mk₂ (true::bit::left) (sourceWord route context later (plainWorkSuffix gap (copied++[bit])))) 4 :=
    ⟨PA17TMRatArithmeticAllocatePass023.restoreBackTrace (bit::left)
        (sourceWord route context later (plainWorkSuffix gap (copied++[bit]))),
      PA17TMRatArithmeticAllocatePass023.restoreBack_runsFrom (bit::left)
        (sourceWord route context later (plainWorkSuffix gap (copied++[bit]))),by rfl⟩
  have combined := ((((((ho.seq ht).seq hd).seq ha).seq hb).seq hf).seq hr).seq hs
  have hc : (((((((2*later.length+cost)+2)+(gap+5))+(4*copied.length+15))+(gap+4))+2)+
      (2*later.length+cost))+4≤4*later.length+2*cost+2*gap+4*copied.length+32 := by omega
  have finished : BoundedRun (plainExcursionMachine route bit)
      (Tape.mk₂ (false::bit::left) (sourceWord route context later (plainWorkSuffix gap copied)))
      (PSTRTMSeq005.rightLabel (a:=a+72+b+1) (3 : Fin 4))
      (Tape.mk₂ (true::bit::left) (sourceWord route context later (plainWorkSuffix gap (copied++[bit]))))
      (4*later.length+2*cost+2*gap+4*copied.length+32) := by
    simpa [plainExcursionMachine,plainOutReturnMachine,plainOutClearMachine,plainOutBackMachine,
      plainOutAppendMachine,plainOutDestMachine,plainOutSetMachine,plainExcursionCap,plainWorkSuffix] using combined.mono hc
  have end_eq : PSTRTMSeq005.rightLabel (a:=a+72+b+1) (3 : Fin 4)=Fin.last (plainExcursionCap a b) := by
    apply Fin.ext
    change (a+72+b+1)+1+3=a+72+b+5
    omega
  simpa only [end_eq] using finished

theorem plain_excursion_room (a b : Nat) : 8≤plainExcursionCap a b := by
  unfold plainExcursionCap
  omega

def plainLoopMachine {a b : Nat} (route : SourceRoute a b) :
    Machine (totalStates 2 (plainExcursionCap a b)) :=
  PA17TMRatArithmeticCopyLoop042.loopMachine (plain_excursion_room a b)
    (plainExcursionMachine route) (Fin.last (plainExcursionCap a b))

def plainLoopPort (a b : Nat) : Fin (totalStates 2 (plainExcursionCap a b)+1) :=
  PA17TMRatArithmeticCopyLoop042.haltLabel (plain_excursion_room a b)

def plainLoopFee (cost gap : Nat) (later copied : List Bool) : Nat :=
  4*later.length+4*copied.length+2*cost+2*gap+32

theorem plain_loop_bounded {a b : Nat} (route : SourceRoute a b) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost gap : Nat) (digits left copied : List Bool)
    (routes : SourceCorrect route context finish cost) (clamped : (copied++digits).headD false=false) :
    BoundedRun (plainLoopMachine route)
      (Tape.mk₂ left (sourceWord route context digits (plainWorkSuffix gap copied))) (plainLoopPort a b)
      (Tape.mk₂ (false::PA17TMRatArithmeticFarLoad031.passedLeft left digits)
        (context++route.footerBit::plainWorkSuffix gap (copied++digits)))
      (PA17TMRatArithmeticCopyLoop042.loopFee (plainLoopFee cost gap) copied digits) := by
  have he : ∀ c, (context++route.footerBit::plainWorkSuffix gap c).head?=some false := by
    intro c
    cases context with
    | nil =>
      have hb : route.footerBit=false := routes.end_false
      simp only [List.nil_append,List.head?_cons,hb]
    | cons bit tail =>
      have hb : bit=false := routes.end_false
      simp only [List.cons_append,List.head?_cons,hb]
  have hx : PA17TMRatArithmeticCopyLoop042.ExcursionCorrect (plainExcursionMachine route)
      (Fin.last (plainExcursionCap a b)) context
      (fun c => route.footerBit::plainWorkSuffix gap c) (plainLoopFee cost gap) := by
    intro l r c bit _
    have h := plain_excursion_bounded route context finish cost routes l r c bit gap
    have hc : 4*r.length+2*cost+2*gap+4*c.length+32=plainLoopFee cost gap r c := by
      unfold plainLoopFee
      omega
    simpa only [PA17TMRatArithmeticCopyLoop042.sourceWord,sourceWord,hc] using h
  have hl := PA17TMRatArithmeticCopyLoop042.loop_bounded (plain_excursion_room a b)
    (plainExcursionMachine route) (Fin.last (plainExcursionCap a b)) context
    (fun c => route.footerBit::plainWorkSuffix gap c) (plainLoopFee cost gap) hx he digits left copied clamped
  simpa only [plainLoopMachine,plainLoopPort,PA17TMRatArithmeticCopyLoop042.sourceWord,sourceWord] using hl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
