module
public import Structure.PA17_TM_RatArithmetic_PairExcursion_041b

/-! Paid shared-B OWN initialization and final one-way source-to-B trip.
The first B DATA remains the real FALSE A.OWN until the caller performs the
last saved-bit write. No head reset, implicit padding, or separator deletion. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairExcursion041

open Turing PA17TMRatArithmeticWidth018 PA17TMRatArithmeticParse002
open PA17TMRatArithmeticAllocate013 PA17TMRatArithmeticPairDestination040

def backFromBDataMachine : Machine 14 := PSTRTMSeq005.seqMachine backOneMachine backFromBMachine

def destinationLeft {a b : Nat} (route : SourceRoute a b) (gap : Nat)
    (archive first : List Bool) : List Bool :=
  false::(PSTRTMRawNat010.leftBlocks first.reverse++false::true::
    (List.replicate gap false++route.footerBit::archive))

theorem back_from_B_data_bounded (archive first copied : List Bool) (gap : Nat)
    (firstBFalse : copied.headD false=false) :
    BoundedRun backFromBDataMachine
      (Tape.mk₂
        (false::(PSTRTMRawNat010.leftBlocks first.reverse++false::true::
          (List.replicate gap false++true::archive)))
        (PA17TMRatArithmeticCopy006.workspace copied)) 14
      (Tape.mk₂ archive (true::workSuffix gap first copied)) (gap+2*first.length+14) := by
  let word := PA17TMRatArithmeticCopy006.workspace copied
  let aLeft := PSTRTMRawNat010.leftBlocks first.reverse++false::true::
    (List.replicate gap false++true::archive)
  have word_eq : word=false::word.tail := workspace_false copied firstBFalse
  have hl : BoundedRun backOneMachine (Tape.mk₂ (false::aLeft) word) 1
      (Tape.mk₂ aLeft (false::word)) 2 :=
    ⟨backOneTrace aLeft false word,backOne_runsFrom aLeft false word,by rfl⟩
  have hb := back_from_B_bounded archive first word.tail gap
  rw [←word_eq] at hb
  change BoundedRun backFromBMachine (Tape.mk₂ aLeft (false::word)) 12
    (Tape.mk₂ archive (true::workSuffix gap first copied)) (gap+2*first.length+12) at hb
  have combined := hl.seq hb
  have cost : 2+(gap+2*first.length+12)≤gap+2*first.length+14 := by omega
  simpa [backFromBDataMachine,PSTRTMSeq005.rightLabel,aLeft,word] using combined.mono cost

def startupInitMachine {a b : Nat} (route : SourceRoute a b) : Machine (a+14) :=
  PSTRTMSeq005.seqMachine (a:=a+9) (b:=4) (outDestMachine route) PA17TMRatArithmeticFarLoad031.initOwnMachine

def startupBackMachine {a b : Nat} (route : SourceRoute a b) : Machine (a+29) :=
  PSTRTMSeq005.seqMachine (a:=a+14) (b:=14) (startupInitMachine route) backFromBDataMachine

def startupClearMachine {a b : Nat} (route : SourceRoute a b) : Machine (a+31) :=
  PSTRTMSeq005.seqMachine (a:=a+29) (b:=1) (startupBackMachine route) (setMarkerMachine route.footerBit)

def startupMachine {a b : Nat} (route : SourceRoute a b) : Machine (a+31+b+1) :=
  PSTRTMSeq005.seqMachine (a:=a+31) (b:=b) (startupClearMachine route) route.back

def startupPort {a b : Nat} (route : SourceRoute a b) : Fin (a+31+b+1+1) :=
  PSTRTMSeq005.rightLabel (a:=a+31) route.backPort

theorem startup_bounded {a b : Nat} (route : SourceRoute a b) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (routes : SourceCorrect route context finish cost) (archive digits first : List Bool) (gap : Nat) :
    BoundedRun (startupMachine route)
      (Tape.mk₂ (false::archive) (sourceWord route context digits (workSuffix gap first []))) (startupPort route)
      (Tape.mk₂ (false::archive) (sourceWord route context digits (workSuffix gap first [])))
      (4*digits.length+2*cost+2*gap+4*first.length+30) := by
  let left := finish (false::archive) digits
  let destLeft := false::(PSTRTMRawNat010.leftBlocks first.reverse++false::true::
    (List.replicate gap false++true::left))
  have ho := routes.out_run (false::archive) digits (workSuffix gap first [])
  have ht : BoundedRun (setMarkerMachine true)
      (Tape.mk₂ left (route.footerBit::workSuffix gap first [])) 1
      (Tape.mk₂ left (true::workSuffix gap first [])) 2 :=
    ⟨setMarkerTrace route.footerBit true left (workSuffix gap first []),
      setMarker_runsFrom route.footerBit true left (workSuffix gap first []),by rfl⟩
  have hd := out_to_B_bounded true left first [false] gap
  have hi : BoundedRun PA17TMRatArithmeticFarLoad031.initOwnMachine
      (Tape.mk₂ destLeft (PA17TMRatArithmeticCopy006.workspace [])) 4
      (Tape.mk₂ destLeft (PA17TMRatArithmeticCopy006.workspace [])) 5 :=
    ⟨PA17TMRatArithmeticFarLoad031.initOwnTrace destLeft,
      PA17TMRatArithmeticFarLoad031.initOwn_runsFrom_full destLeft,by rfl⟩
  have hb := back_from_B_data_bounded left first [] gap (by rfl)
  have hf : BoundedRun (setMarkerMachine route.footerBit)
      (Tape.mk₂ left (true::workSuffix gap first [])) 1
      (Tape.mk₂ left (route.footerBit::workSuffix gap first [])) 2 :=
    ⟨setMarkerTrace true route.footerBit left (workSuffix gap first []),
      setMarker_runsFrom true route.footerBit left (workSuffix gap first []),by rfl⟩
  have hr := routes.back_run archive digits (workSuffix gap first [])
  change BoundedRun outToBMachine (Tape.mk₂ left (true::workSuffix gap first [])) 6
    (Tape.mk₂ destLeft (PA17TMRatArithmeticCopy006.workspace [])) (gap+2*first.length+7) at hd
  have combined := (((((ho.seq ht).seq hd).seq hi).seq hb).seq hf).seq hr
  have costBound : ((((((2*digits.length+cost)+2)+(gap+2*first.length+7))+5)+
      (gap+2*first.length+14))+2)+(2*digits.length+cost)≤
      4*digits.length+2*cost+2*gap+4*first.length+30 := by omega
  simpa [startupMachine,startupClearMachine,startupBackMachine,startupInitMachine,
    outDestMachine,outSetMachine,startupPort] using combined.mono costBound

def finalOutCap (a : Nat) : Nat := 1+a+1

def finalCap (a : Nat) : Nat := finalOutCap a+6+1

def finalOutMachine {a b : Nat} (route : SourceRoute a b) : Machine (finalOutCap a) :=
  PSTRTMSeq005.seqMachine (a:=1) (b:=a) backOneMachine route.out

def finalMachine {a b : Nat} (route : SourceRoute a b) : Machine (finalCap a) :=
  PSTRTMSeq005.seqMachine (a:=finalOutCap a) (b:=6) (finalOutMachine route) outToBMachine

theorem finalCap_eq (a : Nat) : finalCap a=a+9 := by
  unfold finalCap finalOutCap
  omega

theorem final_bounded {a b : Nat} (route : SourceRoute a b) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (routes : SourceCorrect route context finish cost) (left first copied : List Bool) (gap : Nat)
    (firstBFalse : copied.headD false=false) :
    BoundedRun (finalMachine route)
      (Tape.mk₂ (false::left) (context++route.footerBit::workSuffix gap first copied)) (Fin.last (finalCap a))
      (Tape.mk₂ (destinationLeft route gap (finish left []) first) (PA17TMRatArithmeticCopy006.workspace copied))
      (cost+gap+2*first.length+9) := by
  let word := PA17TMRatArithmeticCopy006.workspace copied
  have word_eq : word=false::word.tail := workspace_false copied firstBFalse
  have hl : BoundedRun backOneMachine
      (Tape.mk₂ (false::left) (context++route.footerBit::workSuffix gap first copied)) 1
      (Tape.mk₂ left (sourceWord route context [] (workSuffix gap first copied))) 2 :=
    ⟨backOneTrace left false (context++route.footerBit::workSuffix gap first copied),
      backOne_runsFrom left false (context++route.footerBit::workSuffix gap first copied),by rfl⟩
  have ho := routes.out_run left [] (workSuffix gap first copied)
  have hd := out_to_B_bounded route.footerBit (finish left []) first word.tail gap
  rw [←word_eq] at hd
  change BoundedRun outToBMachine
    (Tape.mk₂ (finish left []) (route.footerBit::workSuffix gap first copied)) 6
    (Tape.mk₂ (destinationLeft route gap (finish left []) first) word) (gap+2*first.length+7) at hd
  have combined := (hl.seq ho).seq hd
  have costBound : (2+(2*(([] : List Bool).length)+cost))+(gap+2*first.length+7)≤cost+gap+2*first.length+9 := by
    simp only [List.length_nil]
    omega
  have finished : BoundedRun (finalMachine route)
      (Tape.mk₂ (false::left) (context++route.footerBit::workSuffix gap first copied))
      (PSTRTMSeq005.rightLabel (a:=finalOutCap a) (6 : Fin 7))
      (Tape.mk₂ (destinationLeft route gap (finish left []) first) word)
      (cost+gap+2*first.length+9) := by
    simpa [finalMachine,finalOutMachine,finalCap,finalOutCap] using combined.mono costBound
  have end_eq : PSTRTMSeq005.rightLabel (a:=finalOutCap a) (6 : Fin 7)=Fin.last (finalCap a) := by
    apply Fin.ext
    change (1+a+1)+1+6=(1+a+1)+6+1
    omega
  simpa only [end_eq,word] using finished

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairExcursion041
