module
public import Structure.PA17_TM_RatArithmetic_AllocationBounds_056a
public import Structure.PA17_TM_RatArithmetic_BankWalk_033c
public import Structure.PA17_TM_RatArithmetic_FarLoad_031c
public import Structure.PA17_TM_RatArithmetic_Literal_027a
public import Structure.PA17_TM_RatArithmetic_OutputFinish_044c

/-! Fixed physical terminal code for the ACTUALLY OBSERVED division-zero
branch. Neither the observed bit nor 0/1 is supplied as an input datum. The
caller really dispatches to label0; all code below is fixed before x/y.
The standalone cache bank has blank right tail. This is no suffix allocator. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticDivZero068

open Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticCachedPass036
open PA17TMRatArithmeticCachedOuter043
open PA17TMRatArithmeticWideCache045 (allocationK)
open PA17TMRatArithmeticOutputFinish044

def walkCap : Nat := 18+forwardCap 2+1
def destinationCap : Nat := walkCap+4+1
def literalCap : Nat := destinationCap+19+1
def finishCap : Nat := literalCap+tailCap 1+1
def zeroCap : Nat := outerCap 2 allocationK+finishCap+1
attribute [local implicit_reducible] walkCap destinationCap literalCap finishCap zeroCap

def walkMachine : Machine walkCap :=
  PSTRTMSeq005.seqMachine seekFooterMachine (forwardMachine 2)
def destinationMachine : Machine destinationCap :=
  PSTRTMSeq005.seqMachine walkMachine PA17TMRatArithmeticFarLoad031.toDestMachine
def literalFinishMachine : Machine literalCap :=
  PSTRTMSeq005.seqMachine destinationMachine PA17TMRatArithmeticLiteral027.literalMachine
def finishMachine : Machine finishCap :=
  PSTRTMSeq005.seqMachine literalFinishMachine (tailMachine 1)

/-- No width, gap, record, sign, answer, or memory argument occurs in this code. -/
def zeroMachine : Machine zeroCap :=
  PSTRTMSeq005.seqMachine (outerMachine 2 allocationK) finishMachine

def walkPort : Fin (walkCap+1) := PSTRTMSeq005.rightLabel (a:=18) (forwardPort 2)
def destinationPort : Fin (destinationCap+1) := PSTRTMSeq005.rightLabel (a:=walkCap) (4 : Fin 5)
def literalPort : Fin (literalCap+1) := PSTRTMSeq005.rightLabel (a:=destinationCap) (19 : Fin 20)
def finishPort : Fin (finishCap+1) := PSTRTMSeq005.rightLabel (a:=literalCap) (tailPort 1)
def zeroPort : Fin (zeroCap+1) := PSTRTMSeq005.rightLabel (a:=outerCap 2 allocationK) finishPort

def headerTape (sx : Bool) (nxTail dxTail nyTail dyTail : List Bool)
    (records : List RecordSpec) (suffix : List Bool) : Tape Bool :=
  Tape.mk₂ [false] (PA17TMRatArithmeticWidth018.prefixRight sx
    (sourceWord nxTail dxTail nyTail dyTail (bankTail records suffix)))

def cacheLeft (sx : Bool) (nxTail dxTail nyTail dyTail : List Bool)
    (first second : RecordSpec) : List Bool :=
  latestLeft sx (false::nxTail) dxTail (false::nyTail) dyTail first [second]

def latestTape (sx : Bool) (nxTail dxTail nyTail dyTail : List Bool)
    (first second : RecordSpec) (gap : Nat) : Tape Bool :=
  Tape.mk₂ (cacheLeft sx nxTail dxTail nyTail dyTail first second) (true::gapWord gap)

def blankOutputTape (gap : Nat) (archive : List Bool) : Tape Bool :=
  Tape.mk₂ (false::workArchive gap archive) []

def localFee (records : List RecordSpec) (width gap : Nat) : Nat :=
  5*totalGap records+16*totalWidth records+12*width+3*gap+281

def zeroFee (records : List RecordSpec) (width : Nat) : Nat :=
  outerFee 2 allocationK records width+localFee records width (allocationK*width^2)

theorem forward_to_latest (sx : Bool) (nxTail dxTail nyTail dyTail : List Bool)
    (first second : RecordSpec) (gap : Nat) :
    BoundedRun (forwardMachine 2)
      (Tape.mk₂ (sourceFooter sx [false] nxTail dxTail nyTail dyTail)
        (false::bankTail [first,second] (gapWord gap))) (forwardPort 2)
      (latestTape sx nxTail dxTail nyTail dyTail first second gap)
      (totalGap [first,second]+2*totalWidth [first,second]+19) := by
  have h := forwardAny_bounded 2 false [first,second] rfl
    (sourceFooter sx [false] nxTail dxTail nyTail dyTail) (gapWord gap)
  simpa only [bankStartAny,bankEndAny,bankLeftAny,bankEndBitAny,latestTape,
    cacheLeft,latestLeft,PA17TMRatArithmeticReturnHome037.firstLeft,
    PA17TMRatArithmeticReturnHome037.footerLeft,sourceFooter] using h

/-- The extra false descriptor denotes the existing infinite blank tail.
The toDest program still makes all actual gap/anchor/guard moves. -/
theorem latest_to_blank (gap : Nat) (archive : List Bool) :
    BoundedRun PA17TMRatArithmeticFarLoad031.toDestMachine
      (Tape.mk₂ archive (true::gapWord gap)) 4 (blankOutputTape gap archive) (gap+5) := by
  have hb := PA17TMRatArithmeticFarLoad031.toDest_bounded gap archive true []
  have heq : Tape.mk₂ archive (true::(List.replicate gap false++[true,false])) =
      Tape.mk₂ archive (true::(List.replicate gap false++[true])) := by
    simpa only [List.cons_append,List.append_assoc,List.nil_append] using
      PA17TMRatArithmeticBankCopy024.tape_append_false archive
        (true::(List.replicate gap false++[true]))
  change BoundedRun PA17TMRatArithmeticFarLoad031.toDestMachine
    (Tape.mk₂ archive (true::(List.replicate gap false++[true,false]))) 4
    (blankOutputTape gap archive) (gap+5) at hb
  rw [heq] at hb
  exact hb

/-- Seven real constant WRITEs, six RIGHTs, six LEFTs. No inverse encoder
is run afterwards: public044.tail starts strictly AFTER its marked017 stage. -/
theorem write_zero_pair (gap : Nat) (archive : List Bool) :
    BoundedRun PA17TMRatArithmeticLiteral027.literalMachine
      (blankOutputTape gap archive) 19 (pairOutput gap archive 0 1) 20 := by
  refine ⟨PA17TMRatArithmeticLiteral027.literalTrace false false false false false false false
    (false::workArchive gap archive) [],?_,?_⟩
  · exact PA17TMRatArithmeticLiteral027.literal_blank_runsFrom (false::workArchive gap archive)
  · rfl

theorem finish_bounded (sx : Bool) (nxTail dxTail nyTail dyTail : List Bool)
    (first second : RecordSpec) (gap : Nat) (hgap : 3≤gap) :
    BoundedRun finishMachine
      (headerTape sx nxTail dxTail nyTail dyTail [first,second] (gapWord gap)) finishPort
      (Tape.mk₁ (physicalWord false 0 1))
      (localFee [first,second] (sourceWidth nxTail dxTail nyTail dyTail) gap) := by
  let archive := cacheLeft sx nxTail dxTail nyTail dyTail first second
  have hs := seek_footer_bounded sx [false] nxTail dxTail nyTail dyTail
    (bankTail [first,second] (gapWord gap))
  have hw := forward_to_latest sx nxTail dxTail nyTail dyTail first second gap
  have hwalk : BoundedRun walkMachine
      (headerTape sx nxTail dxTail nyTail dyTail [first,second] (gapWord gap)) walkPort
      (latestTape sx nxTail dxTail nyTail dyTail first second gap)
      ((2*sourceWidth nxTail dxTail nyTail dyTail+19)+
        (totalGap [first,second]+2*totalWidth [first,second]+19)) := hs.seq hw
  have hd := latest_to_blank gap archive
  have hdest := hwalk.seq hd
  have hl := write_zero_pair gap archive
  have hraw := hdest.seq hl
  have ht : BoundedRun (tailMachine 1) (pairOutput gap archive 0 1) (tailPort 1)
      (Tape.mk₁ (physicalWord false 0 1))
      (tailFee 1 first [second] (false::nxTail) dxTail (false::nyTail) dyTail gap) := by
    exact tail_bounded 1 false first [second] rfl sx (false::nxTail) dxTail
      (false::nyTail) dyTail gap hgap 0 1
  have h := hraw.seq ht
  apply h.mono
  unfold localFee tailFee PA17TMRatArithmeticFinalClean039.cacheGap
    PA17TMRatArithmeticFinalClean039.cacheWidth PA17TMRatArithmeticFinalClean039.sourceWidth
    sourceWidth
  omega

theorem physical_zero_canonical : physicalWord false 0 1=encode [.rational (0 : Rat)] := by
  simpa using physicalWord_canonical (0 : Rat)

/-- Whole physical standalone zero finish. Records and source widths occur
only in this theorem's tape and fee, never in zeroMachine. Both old caches,
the original source, counter and markers are actually cleaned by044/039. -/
theorem zero_bounded (sx : Bool) (nxTail dxTail nyTail dyTail : List Bool)
    (first second : RecordSpec) :
    BoundedRun zeroMachine
      (headerTape sx nxTail dxTail nyTail dyTail [first,second] []) zeroPort
      (Tape.mk₁ (encode [.rational (0 : Rat)]))
      (zeroFee [first,second] (sourceWidth nxTail dxTail nyTail dyTail)) := by
  let width := sourceWidth nxTail dxTail nyTail dyTail
  have ha := outer_bounded 2 allocationK [first,second] rfl sx nxTail dxTail nyTail dyTail
  have hg : 3≤allocationK*width^2 := grownGap_ge_three allocationK (by decide)
    nxTail dxTail nyTail dyTail
  have hf := finish_bounded sx nxTail dxTail nyTail dyTail first second (allocationK*width^2) hg
  have h := ha.seq hf
  rw [physical_zero_canonical] at h
  exact h

theorem zero_contract (sx : Bool) (nxTail dxTail nyTail dyTail : List Bool)
    (first second : RecordSpec) :
    ∃ trace, PSTRTMSeq005.RunsFrom zeroMachine
        ⟨0,headerTape sx nxTail dxTail nyTail dyTail [first,second] []⟩ trace
        ⟨zeroPort,Tape.mk₁ (encode [.rational (0 : Rat)])⟩ ∧
      trace.length≤zeroFee [first,second] (sourceWidth nxTail dxTail nyTail dyTail) ∧
      ∀ prefixLength chargedL, visitedSpace zeroMachine chargedL (trace.take prefixLength)≤
        chargedL+2*zeroFee [first,second] (sourceWidth nxTail dxTail nyTail dyTail)+1 := by
  obtain ⟨trace,hr,ht⟩ := zero_bounded sx nxTail dxTail nyTail dyTail first second
  refine ⟨trace,hr,ht,?_⟩
  intro prefixLength chargedL
  have hs := PSTRTMTrace002.visitedSpace_le zeroMachine chargedL (trace.take prefixLength)
  have hp : (trace.take prefixLength).length≤trace.length := by
    simp only [List.length_take]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticDivZero068
