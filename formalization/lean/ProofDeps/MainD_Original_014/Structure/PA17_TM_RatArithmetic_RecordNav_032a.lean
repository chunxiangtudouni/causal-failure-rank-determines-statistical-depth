module
public import Structure.PA17_TM_RatArithmetic_Allocate_013d
public import Structure.PA17_TM_RatArithmetic_Width_018f
public import Structure.PA17_TM_RatArithmetic_FieldNav_012a
public import Structure.PA17_TM_RatArithmetic_Cleanup_026b

/-! Fixed read-only next-record navigation. Metadata describes actual cells;
neither a gap length nor a field width is an argument of executable code. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticRecordNav032

open Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)

def gapRightTrace (gap : Nat) (archive : List Bool) (oldBit : Bool) (suffix : List Bool) :
    List (MachineState 1) :=
  PA17TMRatArithmeticAllocate013.seekState 0 archive
      (oldBit::(List.replicate gap false++true::suffix)) ::
    PA17TMRatArithmeticAllocate013.seekRightTrace gap (oldBit::archive) suffix

/-- The initial move accepts the real old bit, including the original FALSE
footer. It does not silently replace that bit with a TRUE marker. -/
theorem gapRight_runsFrom (gap : Nat) (archive : List Bool) (oldBit : Bool) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom (PA17TMRatArithmeticAllocate013.gapSeekMachine .right)
      ⟨0,Tape.mk₂ archive (oldBit::(List.replicate gap false++true::suffix))⟩
      (gapRightTrace gap archive oldBit suffix)
      ⟨1,Tape.mk₂ (List.replicate gap false++oldBit::archive) (true::suffix)⟩ := by
  refine ⟨rfl,?_,?_,?_⟩
  · apply List.IsChain.cons (PA17TMRatArithmeticAllocate013.seekRight_chain gap (oldBit::archive) suffix)
    intro next hn
    rw [PA17TMRatArithmeticAllocate013.seekRight_head] at hn
    simp only [Option.mem_some_iff] at hn
    subst next
    simp [TM0.step,PA17TMRatArithmeticAllocate013.gapSeekMachine,
      PA17TMRatArithmeticAllocate013.seekState,Tape.mk₂]
  · change ([_]++PA17TMRatArithmeticAllocate013.seekRightTrace gap (oldBit::archive) suffix).getLast? = _
    rw [List.getLast?_append,PA17TMRatArithmeticAllocate013.seekRight_last]
    rfl
  · simp [TM0.step,PA17TMRatArithmeticAllocate013.gapSeekMachine,Tape.mk₂]

theorem gapRightTrace_length (gap : Nat) (archive : List Bool) (oldBit : Bool) (suffix : List Bool) :
    (gapRightTrace gap archive oldBit suffix).length=gap+2 := by
  simp [gapRightTrace,PA17TMRatArithmeticAllocate013.seekRight_length]

def recordWord (digits suffix : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks digits++false::false::true::suffix

def oldContext (gap : Nat) (oldBit : Bool) (archive : List Bool) : List Bool :=
  List.replicate gap false++oldBit::archive

def nextInput (gap : Nat) (archive : List Bool) (oldBit : Bool) (digits suffix : List Bool) : Tape Bool :=
  Tape.mk₂ archive (oldBit::(List.replicate gap false++true::false::recordWord digits suffix))

def recordLeft (gap : Nat) (archive : List Bool) (oldBit : Bool) (digits : List Bool) : List Bool :=
  false::false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::true::oldContext gap oldBit archive)

def nextOutput (gap : Nat) (archive : List Bool) (oldBit : Bool) (digits suffix : List Bool) : Tape Bool :=
  Tape.mk₂ (recordLeft gap archive oldBit digits) (true::suffix)

def nextHeaderMachine : Machine 4 := PSTRTMSeq005.seqMachine
  (PA17TMRatArithmeticAllocate013.gapSeekMachine .right) PA17TMRatArithmeticWidth018.headerRightMachine
def nextScanMachine : Machine 6 := PSTRTMSeq005.seqMachine
  nextHeaderMachine PA17TMRatArithmeticWidth018.scanMachine

/-- Fixed nine labels: actual gap scan, two RIGHTs, actual flagged scan,
and a final RIGHT across the second OWN FALSE to the new end TRUE. -/
def recordNextMachine : Machine 8 := PSTRTMSeq005.seqMachine
  nextScanMachine PA17TMRatArithmeticParse002.footerMachine

theorem recordNext_bounded (gap : Nat) (archive : List Bool) (oldBit : Bool) (digits suffix : List Bool) :
    BoundedRun recordNextMachine (nextInput gap archive oldBit digits suffix) 8
      (nextOutput gap archive oldBit digits suffix) (gap+2*digits.length+9) := by
  have hg : BoundedRun (PA17TMRatArithmeticAllocate013.gapSeekMachine .right)
      (nextInput gap archive oldBit digits suffix) 1
      (Tape.mk₂ (oldContext gap oldBit archive) (true::false::recordWord digits suffix)) (gap+2) := by
    refine ⟨gapRightTrace gap archive oldBit (false::recordWord digits suffix),
      gapRight_runsFrom gap archive oldBit (false::recordWord digits suffix),?_⟩
    rw [gapRightTrace_length]
  have hh : BoundedRun PA17TMRatArithmeticWidth018.headerRightMachine
      (Tape.mk₂ (oldContext gap oldBit archive) (true::false::recordWord digits suffix)) 2
      (Tape.mk₂ (false::true::oldContext gap oldBit archive) (recordWord digits suffix)) 3 := by
    exact ⟨PA17TMRatArithmeticWidth018.headerRightTrace (oldContext gap oldBit archive)
        true false (recordWord digits suffix),
      PA17TMRatArithmeticWidth018.headerRight_runsFrom (oldContext gap oldBit archive)
        true false (recordWord digits suffix),by rfl⟩
  have hs : BoundedRun PA17TMRatArithmeticWidth018.scanMachine
      (Tape.mk₂ (false::true::oldContext gap oldBit archive) (recordWord digits suffix)) 1
      (Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::true::oldContext gap oldBit archive))
        (false::true::suffix)) (2*digits.length+2) := by
    refine ⟨PA17TMRatArithmeticWidth018.scanTrace (false::true::oldContext gap oldBit archive)
        digits false (true::suffix),
      PA17TMRatArithmeticWidth018.scan_runsFrom (false::true::oldContext gap oldBit archive)
        digits false (true::suffix),?_⟩
    rw [PA17TMRatArithmeticWidth018.scanTrace_length]
  have ha : BoundedRun PA17TMRatArithmeticParse002.footerMachine
      (Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::true::oldContext gap oldBit archive))
        (false::true::suffix)) 1 (nextOutput gap archive oldBit digits suffix) 2 := by
    exact ⟨PA17TMRatArithmeticCleanup026.advanceTrace
        (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::true::oldContext gap oldBit archive))
        false (true::suffix),
      PA17TMRatArithmeticCleanup026.advance_runsFrom
        (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::true::oldContext gap oldBit archive))
        false (true::suffix),by rfl⟩
  have h := ((hg.seq hh).seq hs).seq ha
  apply h.mono
  omega

/-- Whole final Tape includes the old bit, every gap cell, record marker,
guard, data flags, END/OWN00, and the arbitrary suffix. All are retained. -/
theorem recordNext_contract (gap : Nat) (archive : List Bool) (oldBit : Bool) (digits suffix : List Bool) :
    ∃ trace, PSTRTMSeq005.RunsFrom recordNextMachine
        ⟨0,nextInput gap archive oldBit digits suffix⟩ trace
        ⟨8,nextOutput gap archive oldBit digits suffix⟩ ∧
      trace.length≤gap+2*digits.length+9 ∧
      ∀ prefixLength chargedL, visitedSpace recordNextMachine chargedL (trace.take prefixLength) ≤
        chargedL+2*gap+4*digits.length+19 := by
  obtain ⟨trace,hr,hl⟩ := recordNext_bounded gap archive oldBit digits suffix
  refine ⟨trace,hr,hl,?_⟩
  intro prefixLength chargedL
  have hs := PSTRTMTrace002.visitedSpace_le recordNextMachine chargedL (trace.take prefixLength)
  have ht : (trace.take prefixLength).length≤trace.length := by
    simp only [List.length_take]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticRecordNav032
