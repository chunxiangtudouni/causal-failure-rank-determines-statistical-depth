module
public import Structure.PA17_TM_RatArithmetic_PairDestination_040b
public import Structure.PA17_TM_RatArithmetic_FarLoad_031g

/-! A source route and the actual shared-B destination form one real
excursion. Source routes remain executable fixed machines. Context/finish,
widths and data lists specify their actual tapes, never machine inputs. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairExcursion041

open Turing PA17TMRatArithmeticWidth018 PA17TMRatArithmeticAllocate013
open PA17TMRatArithmeticPairDestination040

structure SourceRoute (outStates backStates : Nat) where
  out : Machine outStates
  back : Machine backStates
  footerBit : Bool
  outPort : Fin (outStates+1)
  backPort : Fin (backStates+1)

def sourceWord {a b : Nat} (route : SourceRoute a b) (context digits suffix : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks digits++false::(context++route.footerBit::suffix)

structure SourceCorrect {a b : Nat} (route : SourceRoute a b) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat) : Prop where
  end_false : context.headD route.footerBit=false
  finish_cons : ∀ left bit later, finish (true::bit::left) later=finish left (bit::later)
  out_run : ∀ left later suffix,
    BoundedRun route.out
      (Tape.mk₂ left (sourceWord route context later suffix)) route.outPort
      (Tape.mk₂ (finish left later) (route.footerBit::suffix)) (2*later.length+cost)
  back_run : ∀ archive later suffix,
    BoundedRun route.back (Tape.mk₂ (finish (false::archive) later) (route.footerBit::suffix)) route.backPort
      (Tape.mk₂ (false::archive) (sourceWord route context later suffix))
      (2*later.length+cost)

def originalRoute (route : PA17TMRatArithmeticFarLoad031.FarRoute) : SourceRoute 10 26 :=
  ⟨route.out,route.back,false,route.outPort,route.backPort⟩

theorem original_correct (route : PA17TMRatArithmeticFarLoad031.FarRoute)
    (context : List Bool) (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (correct : PA17TMRatArithmeticFarLoad031.RouteCorrect route context finish cost) :
    SourceCorrect (originalRoute route) context finish cost :=
  ⟨correct.end_false,correct.finish_cons,correct.out_run,correct.back_run⟩

def workSuffix (gap : Nat) (first copied : List Bool) : List Bool :=
  List.replicate gap false++true::false::
    (PSTRTMIncrement009.blocks first++false::PA17TMRatArithmeticCopy006.workspace copied)

def outSetMachine {a b : Nat} (route : SourceRoute a b) : Machine (a+2) :=
  PSTRTMSeq005.seqMachine (a:=a) (b:=1) route.out (setMarkerMachine true)

def outDestMachine {a b : Nat} (route : SourceRoute a b) : Machine (a+9) :=
  PSTRTMSeq005.seqMachine (a:=a+2) (b:=6) (outSetMachine route) outToBMachine

def outAppendMachine {a b : Nat} (route : SourceRoute a b) (bit : Bool) : Machine (a+68) :=
  PSTRTMSeq005.seqMachine (a:=a+9) (b:=58) (outDestMachine route) (PA17TMRatArithmeticFarLoad031.appendStartMachine bit)

def outBackMachine {a b : Nat} (route : SourceRoute a b) (bit : Bool) : Machine (a+81) :=
  PSTRTMSeq005.seqMachine (a:=a+68) (b:=12) (outAppendMachine route bit) backFromBMachine

def outClearMachine {a b : Nat} (route : SourceRoute a b) (bit : Bool) : Machine (a+83) :=
  PSTRTMSeq005.seqMachine (a:=a+81) (b:=1) (outBackMachine route bit) (setMarkerMachine route.footerBit)

def outReturnMachine {a b : Nat} (route : SourceRoute a b) (bit : Bool) : Machine (a+83+b+1) :=
  PSTRTMSeq005.seqMachine (a:=a+83) (b:=b) (outClearMachine route bit) route.back

def excursionCap (a b : Nat) : Nat := a+83+b+5

def excursionMachine {a b : Nat} (route : SourceRoute a b) (bit : Bool) : Machine (excursionCap a b) :=
  PSTRTMSeq005.seqMachine (a:=a+83+b+1) (b:=3)
    (outReturnMachine route bit) PA17TMRatArithmeticAllocatePass023.restoreBackMachine

theorem excursionCap_eq (a b : Nat) : excursionCap a b=a+b+88 := by
  unfold excursionCap
  omega

theorem workspace_false (copied : List Bool) (h : copied.headD false=false) :
    PA17TMRatArithmeticCopy006.workspace copied=
      false::(PA17TMRatArithmeticCopy006.workspace copied).tail := by
  cases copied with
  | nil => rfl
  | cons bit later =>
    have hb : bit=false := h
    subst bit
    rfl

theorem prefix_head_false (copied : List Bool) (bit : Bool)
    (h : (copied++[bit]).headD false=false) : copied.headD false=false := by
  cases copied with
  | nil => rfl
  | cons first later => exact h

theorem excursion_bounded {a b : Nat} (route : SourceRoute a b) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (routes : SourceCorrect route context finish cost)
    (left later first copied : List Bool) (bit : Bool) (gap : Nat)
    (firstBFalse : (copied++[bit]).headD false=false) :
    BoundedRun (excursionMachine route bit)
      (Tape.mk₂ (false::bit::left)
        (sourceWord route context later (workSuffix gap first copied)))
      (Fin.last (excursionCap a b))
      (Tape.mk₂ (true::bit::left)
        (sourceWord route context later (workSuffix gap first (copied++[bit]))))
      (4*later.length+2*cost+2*gap+4*first.length+4*copied.length+42) := by
  let archive := finish (false::bit::left) later
  let before := PA17TMRatArithmeticCopy006.workspace copied
  let after := PA17TMRatArithmeticCopy006.workspace (copied++[bit])
  let destLeft := PSTRTMRawNat010.leftBlocks first.reverse++false::true::
    (List.replicate gap false++true::archive)
  have before_eq : before=false::before.tail := workspace_false copied (prefix_head_false copied bit firstBFalse)
  have after_eq : after=false::after.tail := workspace_false (copied++[bit]) firstBFalse
  have ho := routes.out_run (false::bit::left) later (workSuffix gap first copied)
  have ht : BoundedRun (setMarkerMachine true)
      (Tape.mk₂ archive (route.footerBit::workSuffix gap first copied)) 1
      (Tape.mk₂ archive (true::workSuffix gap first copied)) 2 :=
    ⟨setMarkerTrace route.footerBit true archive (workSuffix gap first copied),
      setMarker_runsFrom route.footerBit true archive (workSuffix gap first copied),by rfl⟩
  have hd := out_to_B_bounded true archive first before.tail gap
  rw [←before_eq] at hd
  have ha := PA17TMRatArithmeticFarLoad031.appendStart_bounded bit destLeft copied
  have hb := back_from_B_bounded archive first after.tail gap
  rw [←after_eq] at hb
  have hf : BoundedRun (setMarkerMachine route.footerBit)
      (Tape.mk₂ archive (true::workSuffix gap first (copied++[bit]))) 1
      (Tape.mk₂ archive (route.footerBit::workSuffix gap first (copied++[bit]))) 2 :=
    ⟨setMarkerTrace true route.footerBit archive (workSuffix gap first (copied++[bit])),
      setMarker_runsFrom true route.footerBit archive (workSuffix gap first (copied++[bit])),by rfl⟩
  have hr := routes.back_run (bit::left) later (workSuffix gap first (copied++[bit]))
  have hs : BoundedRun PA17TMRatArithmeticAllocatePass023.restoreBackMachine
      (Tape.mk₂ (false::bit::left)
        (sourceWord route context later (workSuffix gap first (copied++[bit])))) 3
      (Tape.mk₂ (true::bit::left)
        (sourceWord route context later (workSuffix gap first (copied++[bit])))) 4 :=
    ⟨PA17TMRatArithmeticAllocatePass023.restoreBackTrace (bit::left)
        (sourceWord route context later (workSuffix gap first (copied++[bit]))),
      PA17TMRatArithmeticAllocatePass023.restoreBack_runsFrom (bit::left)
        (sourceWord route context later (workSuffix gap first (copied++[bit]))),by rfl⟩
  change BoundedRun outToBMachine (Tape.mk₂ archive (true::workSuffix gap first copied)) 6
    (Tape.mk₂ (false::destLeft) before) (gap+2*first.length+7) at hd
  change BoundedRun backFromBMachine (Tape.mk₂ destLeft (false::after)) 12
    (Tape.mk₂ archive (true::workSuffix gap first (copied++[bit]))) (gap+2*first.length+12) at hb
  have combined := ((((((ho.seq ht).seq hd).seq ha).seq hb).seq hf).seq hr).seq hs
  have costBound : (((((((2*later.length+cost)+2)+(gap+2*first.length+7))+
      (4*copied.length+15))+(gap+2*first.length+12))+2)+(2*later.length+cost))+4 ≤
      4*later.length+2*cost+2*gap+4*first.length+4*copied.length+42 := by omega
  have finished : BoundedRun (excursionMachine route bit)
      (Tape.mk₂ (false::bit::left) (sourceWord route context later (workSuffix gap first copied)))
      (PSTRTMSeq005.rightLabel (a:=a+83+b+1) (3 : Fin 4))
      (Tape.mk₂ (true::bit::left) (sourceWord route context later (workSuffix gap first (copied++[bit]))))
      (4*later.length+2*cost+2*gap+4*first.length+4*copied.length+42) := by
    simpa [excursionMachine,outReturnMachine,outClearMachine,outBackMachine,outAppendMachine,
      outDestMachine,outSetMachine,excursionCap] using combined.mono costBound
  have end_eq : PSTRTMSeq005.rightLabel (a:=a+83+b+1) (3 : Fin 4)=Fin.last (excursionCap a b) := by
    apply Fin.ext
    change (a+83+b+1)+1+3=a+83+b+5
    omega
  simpa only [end_eq] using finished

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairExcursion041
