module
public import Structure.PA17_TM_RatArithmetic_BankWalk_033b
public import Structure.PA17_TM_RatArithmetic_Allocate_013e

/-! Actual destructive record erase, preserving the old TRUE marker and
arbitrary archive/right suffix. Frozen reverse prefix is followed by actual
record erasure and end-marker clearing BEFORE the genuine return scan. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticEraseBank034

open Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticRecordNav032
open PA17TMRatArithmeticAllocate013

def returnAnyTrace (n : Nat) (archive : List Bool) (bit : Bool) (suffix : List Bool) :
    List (MachineState 1) :=
  seekState 0 (List.replicate n false++true::archive) (bit::suffix) ::
    seekLeftTrace n archive (bit::suffix)

/-- The cleared newest end is FALSE. This proves its actual initial LEFT,
instead of applying the old TRUE-head return lemma to a different tape. -/
theorem returnAny_runsFrom (n : Nat) (archive : List Bool) (bit : Bool) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom (gapSeekMachine .left)
      (seekState 0 (List.replicate n false++true::archive) (bit::suffix))
      (returnAnyTrace n archive bit suffix)
      (seekState 1 archive (true::(List.replicate n false++bit::suffix))) := by
  refine ⟨rfl,?_,?_,?_⟩
  · apply List.IsChain.cons (seekLeft_chain n archive (bit::suffix))
    intro next hn
    rw [seekLeft_head] at hn
    simp only [Option.mem_some_iff] at hn
    subst next
    simp [TM0.step,gapSeekMachine,seekState]
  · change ([_]++seekLeftTrace n archive (bit::suffix)).getLast? = _
    rw [List.getLast?_append,seekLeft_last]
    rfl
  · simp [TM0.step,gapSeekMachine,seekState,Tape.mk₂]

theorem returnAnyTrace_length (n : Nat) (archive : List Bool) (bit : Bool) (suffix : List Bool) :
    (returnAnyTrace n archive bit suffix).length=n+2 := by
  simp [returnAnyTrace,seekLeft_length]

theorem reverseAnchor_bounded (gap : Nat) (archive digits suffix : List Bool) :
    BoundedRun prevAnchorMachine (nextOutput gap archive true digits suffix) 10
      (Tape.mk₂ (oldContext gap true archive) (true::false::recordWord digits suffix))
      (2*digits.length+10) := by
  have hb : BoundedRun PA17TMRatArithmeticParse002.backOneMachine
      (nextOutput gap archive true digits suffix) 1
      (Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::true::oldContext gap true archive))
        (false::true::suffix)) 2 := by
    exact ⟨PA17TMRatArithmeticParse002.backOneTrace
        (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::true::oldContext gap true archive))
        false (true::suffix),
      PA17TMRatArithmeticParse002.backOne_runsFrom
        (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::true::oldContext gap true archive))
        false (true::suffix),by rfl⟩
  have hf : BoundedRun PA17TMRatArithmeticParse002.fieldBackMachine
      (Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::true::oldContext gap true archive))
        (false::true::suffix)) 5
      (Tape.mk₂ (false::true::oldContext gap true archive) (recordWord digits suffix))
      (2*digits.length+5) := by
    refine ⟨PA17TMRatArithmeticParse002.fieldBackTrace (true::oldContext gap true archive)
        digits (false::true::suffix),
      PA17TMRatArithmeticParse002.fieldBack_runsFrom (true::oldContext gap true archive)
        digits (false::true::suffix),?_⟩
    rw [PA17TMRatArithmeticParse002.fieldBackTrace_length]
  have hh : BoundedRun PA17TMRatArithmeticFieldNav012.headerBackMachine
      (Tape.mk₂ (false::true::oldContext gap true archive) (recordWord digits suffix)) 2
      (Tape.mk₂ (oldContext gap true archive) (true::false::recordWord digits suffix)) 3 := by
    exact ⟨PA17TMRatArithmeticFieldNav012.headerBackTrace (oldContext gap true archive)
        false true (recordWord digits suffix),
      PA17TMRatArithmeticFieldNav012.headerBack_runsFrom (oldContext gap true archive)
        false true (recordWord digits suffix),by rfl⟩
  exact ((hb.seq hf).seq hh).mono (by omega)

private theorem zeros_merge (a b : Nat) (tail : List Bool) :
    List.replicate a false++(List.replicate b false++tail)=List.replicate (a+b) false++tail := by
  calc
    _ = (List.replicate a false++List.replicate b false)++tail := (List.append_assoc _ _ _).symm
    _ = _ := congrArg (fun bits : List Bool => bits++tail) (List.replicate_add a b false).symm

def eraseBodyMachine : Machine 21 :=
  PSTRTMSeq005.seqMachine prevAnchorMachine PA17TMRatArithmeticCleanup026.recordEraseMachine
def clearEndMachine : Machine 23 :=
  PSTRTMSeq005.seqMachine eraseBodyMachine (setMarkerMachine false)

/-- Fixed26labels. No gap, width, data, marker answer or count is a code
argument. The old marker really is TRUE; its preceding archive is arbitrary. -/
def eraseOneMachine : Machine 25 :=
  PSTRTMSeq005.seqMachine clearEndMachine (gapSeekMachine .left)

def oneSpan (gap : Nat) (digits : List Bool) : Nat := gap+2*digits.length+5
def eraseOneOutput (gap : Nat) (archive digits suffix : List Bool) : Tape Bool :=
  Tape.mk₂ archive (true::(List.replicate (oneSpan gap digits) false++suffix))

theorem eraseOne_bounded (gap : Nat) (archive digits suffix : List Bool) :
    BoundedRun eraseOneMachine (nextOutput gap archive true digits suffix) 25
      (eraseOneOutput gap archive digits suffix) (gap+8*digits.length+28) := by
  let n := gap+2*digits.length+4
  have hz : List.replicate (2*digits.length+4) false++oldContext gap true archive =
      List.replicate n false++true::archive := by
    change List.replicate (2*digits.length+4) false++(List.replicate gap false++true::archive) = _
    rw [zeros_merge]
    rw [show 2*digits.length+4+gap=n by dsimp [n];omega]
  have he : BoundedRun PA17TMRatArithmeticCleanup026.recordEraseMachine
      (Tape.mk₂ (oldContext gap true archive) (true::false::recordWord digits suffix)) 10
      (Tape.mk₂ (List.replicate n false++true::archive) (true::suffix)) (4*digits.length+10) := by
    have hr := PA17TMRatArithmeticCleanup026.record_runsFrom (oldContext gap true archive) digits suffix
    have hfinal : PA17TMRatArithmeticCleanup026.recordFinal (oldContext gap true archive) digits suffix =
        ⟨(10 : Fin 11),(PA17TMRatArithmeticCleanup026.recordFinal (oldContext gap true archive) digits suffix).Tape⟩ := rfl
    rw [PA17TMRatArithmeticCleanup026.record_final_tape,hz] at hfinal
    rw [hfinal] at hr
    refine ⟨PA17TMRatArithmeticCleanup026.recordTrace (oldContext gap true archive) digits suffix,hr,?_⟩
    rw [PA17TMRatArithmeticCleanup026.recordTrace_length]
  have hc : BoundedRun (setMarkerMachine false)
      (Tape.mk₂ (List.replicate n false++true::archive) (true::suffix)) 1
      (Tape.mk₂ (List.replicate n false++true::archive) (false::suffix)) 2 :=
    ⟨setMarkerTrace true false (List.replicate n false++true::archive) suffix,
     setMarker_runsFrom true false (List.replicate n false++true::archive) suffix,by rfl⟩
  have ht : List.replicate n false++false::suffix=List.replicate (oneSpan gap digits) false++suffix := by
    have h := zeros_merge n 1 suffix
    change List.replicate n false++false::suffix=List.replicate (n+1) false++suffix at h
    simpa only [n,oneSpan] using h
  have hg : BoundedRun (gapSeekMachine .left)
      (Tape.mk₂ (List.replicate n false++true::archive) (false::suffix)) 1
      (eraseOneOutput gap archive digits suffix) (n+2) := by
    have hr := returnAny_runsFrom n archive false suffix
    rw [ht] at hr
    refine ⟨returnAnyTrace n archive false suffix,hr,?_⟩
    rw [returnAnyTrace_length]
  have h := (((reverseAnchor_bounded gap archive digits suffix).seq he).seq hc).seq hg
  apply h.mono
  dsimp [n]
  omega

/-- Whole final Tape: all record cells and its end are really cleared;
the old TRUE marker, preceding archive and arbitrary right suffix survive. -/
theorem eraseOne_contract (gap : Nat) (archive digits suffix : List Bool) :
    ∃ trace, PSTRTMSeq005.RunsFrom eraseOneMachine
        ⟨0,nextOutput gap archive true digits suffix⟩ trace
        ⟨25,eraseOneOutput gap archive digits suffix⟩ ∧
      trace.length≤gap+8*digits.length+28 ∧
      ∀ prefixLength chargedL, visitedSpace eraseOneMachine chargedL (trace.take prefixLength) ≤
        chargedL+2*gap+16*digits.length+57 := by
  obtain ⟨trace,hr,hl⟩ := eraseOne_bounded gap archive digits suffix
  refine ⟨trace,hr,hl,?_⟩
  intro prefixLength chargedL
  have hs := PSTRTMTrace002.visitedSpace_le eraseOneMachine chargedL (trace.take prefixLength)
  have ht : (trace.take prefixLength).length≤trace.length := by
    simp only [List.length_take]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticEraseBank034
