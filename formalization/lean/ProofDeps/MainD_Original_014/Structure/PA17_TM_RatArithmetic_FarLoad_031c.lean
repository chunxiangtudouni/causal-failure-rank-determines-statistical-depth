module
public import Structure.PA17_TM_RatArithmetic_FarLoad_031b
public import Structure.PA17_TM_RatArithmetic_AllocatePass_023e
public import Structure.PA17_TM_RatArithmetic_RecordNav_032b

/-! j0 transport reuses the frozen read-only gap kernel. Only the global
old footer is TRUE during a round trip; following original fields stay intact.
This module does not implement or duplicate shared cached-record walks. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFarLoad031
open Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)

def toDestMachine : Machine 4 := PA17TMRatArithmeticRecordNav032.nextHeaderMachine

theorem toDest_bounded (gap : Nat) (archive : List Bool) (oldBit : Bool) (word : List Bool) :
    BoundedRun toDestMachine
      (Tape.mk₂ archive (oldBit::(List.replicate gap false++true::false::word))) 4
      (Tape.mk₂ (false::true::(List.replicate gap false++oldBit::archive)) word) (gap+5) := by
  have hg : BoundedRun (PA17TMRatArithmeticAllocate013.gapSeekMachine .right)
      (Tape.mk₂ archive (oldBit::(List.replicate gap false++true::false::word))) 1
      (Tape.mk₂ (List.replicate gap false++oldBit::archive) (true::false::word)) (gap+2) := by
    exact ⟨PA17TMRatArithmeticRecordNav032.gapRightTrace gap archive oldBit (false::word),
      PA17TMRatArithmeticRecordNav032.gapRight_runsFrom gap archive oldBit (false::word),
      by rw [PA17TMRatArithmeticRecordNav032.gapRightTrace_length]⟩
  have hh : BoundedRun PA17TMRatArithmeticWidth018.headerRightMachine
      (Tape.mk₂ (List.replicate gap false++oldBit::archive) (true::false::word)) 2
      (Tape.mk₂ (false::true::(List.replicate gap false++oldBit::archive)) word) 3 :=
    ⟨PA17TMRatArithmeticWidth018.headerRightTrace (List.replicate gap false++oldBit::archive) true false word,
      PA17TMRatArithmeticWidth018.headerRight_runsFrom (List.replicate gap false++oldBit::archive) true false word,
      by rfl⟩
  have h := hg.seq hh
  exact h.mono (by omega)

def backFromGuardMachine : Machine 3 := PSTRTMSeq005.seqMachine
  PA17TMRatArithmeticParse002.backOneMachine (PA17TMRatArithmeticAllocate013.gapSeekMachine .left)

theorem backFromGuard_bounded (gap : Nat) (archive word : List Bool) :
    BoundedRun backFromGuardMachine
      (Tape.mk₂ (true::(List.replicate gap false++true::archive)) (false::word)) 3
      (Tape.mk₂ archive (true::(List.replicate gap false++true::false::word))) (gap+4) := by
  have hb : BoundedRun PA17TMRatArithmeticParse002.backOneMachine
      (Tape.mk₂ (true::(List.replicate gap false++true::archive)) (false::word)) 1
      (Tape.mk₂ (List.replicate gap false++true::archive) (true::false::word)) 2 :=
    ⟨PA17TMRatArithmeticParse002.backOneTrace (List.replicate gap false++true::archive) true (false::word),
      PA17TMRatArithmeticParse002.backOne_runsFrom (List.replicate gap false++true::archive) true (false::word),
      by rfl⟩
  have hg : BoundedRun (PA17TMRatArithmeticAllocate013.gapSeekMachine .left)
      (Tape.mk₂ (List.replicate gap false++true::archive) (true::false::word)) 1
      (Tape.mk₂ archive (true::(List.replicate gap false++true::false::word))) (gap+2) :=
    ⟨PA17TMRatArithmeticAllocate013.returnGapTrace gap archive (false::word),
      PA17TMRatArithmeticAllocate013.returnGap_runsFrom gap archive (false::word),
      by rw [PA17TMRatArithmeticAllocate013.returnGap_length]⟩
  exact (hb.seq hg).mono (by omega)

def backFromDataMachine : Machine 4 := PSTRTMSeq005.seqMachine
  PA17TMRatArithmeticFieldNav012.headerBackMachine (PA17TMRatArithmeticAllocate013.gapSeekMachine .left)

theorem backFromData_bounded (gap : Nat) (archive word : List Bool) :
    BoundedRun backFromDataMachine
      (Tape.mk₂ (false::true::(List.replicate gap false++true::archive)) word) 4
      (Tape.mk₂ archive (true::(List.replicate gap false++true::false::word))) (gap+5) := by
  have hb : BoundedRun PA17TMRatArithmeticFieldNav012.headerBackMachine
      (Tape.mk₂ (false::true::(List.replicate gap false++true::archive)) word) 2
      (Tape.mk₂ (List.replicate gap false++true::archive) (true::false::word)) 3 :=
    ⟨PA17TMRatArithmeticFieldNav012.headerBackTrace (List.replicate gap false++true::archive) false true word,
      PA17TMRatArithmeticFieldNav012.headerBack_runsFrom (List.replicate gap false++true::archive) false true word,
      by rfl⟩
  have hg : BoundedRun (PA17TMRatArithmeticAllocate013.gapSeekMachine .left)
      (Tape.mk₂ (List.replicate gap false++true::archive) (true::false::word)) 1
      (Tape.mk₂ archive (true::(List.replicate gap false++true::false::word))) (gap+2) :=
    ⟨PA17TMRatArithmeticAllocate013.returnGapTrace gap archive (false::word),
      PA17TMRatArithmeticAllocate013.returnGap_runsFrom gap archive (false::word),
      by rw [PA17TMRatArithmeticAllocate013.returnGap_length]⟩
  exact (hb.seq hg).mono (by omega)

def initOwnMachine : Machine 4 := fun q _ =>
  match q.val with
  | 0 => some (1,.write false)
  | 1 => some (2,.move .right)
  | 2 => some (3,.write false)
  | 3 => some (4,.move .left)
  | _ => none

def initOwnTrace (left : List Bool) : List (MachineState 4) :=
  [⟨0,Tape.mk₂ left [false,false]⟩,⟨1,Tape.mk₂ left [false,false]⟩,
   ⟨2,Tape.mk₂ (false::left) [false]⟩,⟨3,Tape.mk₂ (false::left) [false]⟩,
   ⟨4,Tape.mk₂ left [false,false]⟩]

theorem initOwn_runsFrom_full (left : List Bool) :
    PSTRTMSeq005.RunsFrom initOwnMachine ⟨0,Tape.mk₂ left [false,false]⟩
      (initOwnTrace left) ⟨4,Tape.mk₂ left [false,false]⟩ := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [initOwnTrace,List.isChain_cons_cons,TM0.step,initOwnMachine,Tape.mk₂]
  · simp [TM0.step,initOwnMachine]

/-- The descriptor uses the real infinite blank tail. Both OWN zeros are
still individually WRITTEN in the five-configuration actual trace. -/
theorem initOwn_runsFrom (left : List Bool) :
    PSTRTMSeq005.RunsFrom initOwnMachine ⟨0,Tape.mk₂ left []⟩
      (initOwnTrace left) ⟨4,Tape.mk₂ left [false,false]⟩ := by
  have h : Tape.mk₂ left [false,false]=Tape.mk₂ left [] :=
    (PA17TMRatArithmeticBankCopy024.tape_append_false left [false]).trans
      (PA17TMRatArithmeticBankCopy024.tape_append_false left [])
  rw [← h]
  exact initOwn_runsFrom_full left

theorem initOwnTrace_length (left : List Bool) : (initOwnTrace left).length=5 := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFarLoad031
