module
public import Structure.PA17_TM_RatArithmetic_CachedOuter_043a
public import Structure.PA17_TM_RatArithmetic_CachedLoad_038c
public import Structure.PA17_TM_RatArithmetic_PairInput_050b

/-! Actual original-header to selected cached field. Only static record
counts and finite carry bound occur in executable code. The arbitrary
suffix may contain a real nonzero A workspace; it is never a zero gap. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPair054

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticRecordNav032
open PA17TMRatArithmeticCachedLoad038 PA17TMRatArithmeticFarLoad031
open PA17TMRatArithmeticMul047 PA17TMRatArithmeticPairInput050

theorem trueLeft_append (archive : List Bool) (before following : List RecordSpec) :
    bankLeft archive (before++following)=bankLeft (bankLeft archive before) following := by
  induction before generalizing archive with
  | nil => rfl
  | cons record before ih =>
    simpa only [List.cons_append,bankLeft] using ih (recordLeft record.gap archive true record.digits)

theorem anyLeft_true (archive : List Bool) (records : List RecordSpec) :
    bankLeftAny true archive records=bankLeft archive records := by
  cases records <;> rfl

theorem anyLeft_append (oldBit : Bool) (archive : List Bool) (before following : List RecordSpec) :
    bankLeftAny oldBit archive (before++following)=
      bankLeftAny (bankEndBitAny oldBit before) (bankLeftAny oldBit archive before) following := by
  cases before with
  | nil => rfl
  | cons record before =>
    let next := recordLeft record.gap archive oldBit record.digits
    change bankLeft next (before++following)=bankLeftAny true (bankLeft next before) following
    rw [anyLeft_true]
    exact trueLeft_append next before following

def cachedSourceArchive (archive : List Bool) (before : List RecordSpec) (source : RecordSpec) : List Bool :=
  true::(List.replicate source.gap false++bankEndBitAny false before::bankLeftAny false archive before)

theorem latestLeft_split (archive : List Bool) (before following : List RecordSpec) (source : RecordSpec) :
    bankLeftAny false archive (before++source::following)=
      cachedFinish following (false::cachedSourceArchive archive before source) source.digits := by
  rw [anyLeft_append false archive before (source::following)]
  rfl

theorem latestBit_true (before following : List RecordSpec) (source : RecordSpec) :
    bankEndBitAny false (before++source::following)=true := by
  cases before <;> rfl

def latestCap (total : Nat) : Nat := 18+forwardCap total+1
def locatorCap (total sourceLater : Nat) : Nat := latestCap total+cachedBackCap sourceLater+1
attribute [local implicit_reducible] latestCap locatorCap

def latestMachine (total : Nat) : Machine (latestCap total) :=
  PSTRTMSeq005.seqMachine (a:=18) (b:=forwardCap total)
    PA17TMRatArithmeticCachedOuter043.seekFooterMachine (forwardMachine total)
def latestPort (total : Nat) : Fin (latestCap total+1) :=
  PSTRTMSeq005.rightLabel (a:=18) (forwardPort total)

def locatorMachine (total sourceLater : Nat) : Machine (locatorCap total sourceLater) :=
  PSTRTMSeq005.seqMachine (a:=latestCap total) (b:=cachedBackCap sourceLater)
    (latestMachine total) (cachedBackMachine sourceLater)
def locatorPort (total sourceLater : Nat) : Fin (locatorCap total sourceLater+1) :=
  PSTRTMSeq005.rightLabel (a:=latestCap total) (cachedBackPort sourceLater)

def latestFee (total : Nat) (nxTail dxTail nyTail dyTail : List Bool) (records : List RecordSpec) : Nat :=
  (2*PA17TMRatArithmeticFarLoad031.bankWidth nxTail dxTail nyTail dyTail+19)+
    (totalGap records+2*totalWidth records+9*total+1)
def locatorFee (total sourceLater : Nat) (nxTail dxTail nyTail dyTail : List Bool)
    (before : List RecordSpec) (source : RecordSpec) (following : List RecordSpec) : Nat :=
  latestFee total nxTail dxTail nyTail dyTail (before++source::following)+
    (2*source.digits.length+totalGap following+2*totalWidth following+12*sourceLater+8)

def headerInput (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool)
    (records : List RecordSpec) (suffix : List Bool) : Tape Bool :=
  sourceHeaderTape sx counter nxTail dxTail nyTail dyTail (bankTail records suffix)
def sourceOutput (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool)
    (before : List RecordSpec) (source : RecordSpec) (following : List RecordSpec) (suffix : List Bool) : Tape Bool :=
  Tape.mk₂ (false::cachedSourceArchive (globalSourceLeft sx counter nxTail dxTail nyTail dyTail) before source)
    (cachedWord following source.digits suffix)

theorem latest_bounded (total : Nat) (records : List RecordSpec) (hcount : records.length=total)
    (sx : Bool) (counter nxTail dxTail nyTail dyTail suffix : List Bool) :
    BoundedRun (latestMachine total) (headerInput sx counter nxTail dxTail nyTail dyTail records suffix)
      (latestPort total)
      (bankEndAny false (globalSourceLeft sx counter nxTail dxTail nyTail dyTail) records suffix)
      (latestFee total nxTail dxTail nyTail dyTail records) := by
  have seek := PA17TMRatArithmeticCachedOuter043.seek_footer_bounded sx counter nxTail dxTail nyTail dyTail
    (bankTail records suffix)
  have input_eq : Tape.mk₂ counter (prefixRight sx
      (PA17TMRatArithmeticCachedOuter043.sourceWord nxTail dxTail nyTail dyTail (bankTail records suffix)))=
      headerInput sx counter nxTail dxTail nyTail dyTail records suffix := by
    simp only [headerInput,sourceHeaderTape,PA17TMRatArithmeticCachedOuter043.sourceWord,sourceBank_widthBank]
  have footer_eq : PA17TMRatArithmeticCachedOuter043.sourceFooter sx counter nxTail dxTail nyTail dyTail=
      globalSourceLeft sx counter nxTail dxTail nyTail dyTail := rfl
  rw [input_eq,footer_eq] at seek
  have walk := forwardAny_bounded total false records hcount
    (globalSourceLeft sx counter nxTail dxTail nyTail dyTail) suffix
  have combined := seek.seq walk
  simpa only [latestMachine,latestPort,latestCap,latestFee,bankStartAny,
    PA17TMRatArithmeticCachedOuter043.sourceWidth,PA17TMRatArithmeticFarLoad031.bankWidth,
    PA17TMRatArithmeticWidth018.bankWidth] using combined

/-- The selected field is an actual record in this physical bank. Both
counts are compiled before all bank values, not read as extra inputs. -/
theorem locator_bounded (total sourceLater : Nat) (before : List RecordSpec) (source : RecordSpec)
    (following : List RecordSpec) (hcount : (before++source::following).length=total)
    (hsource : following.length=sourceLater) (sx : Bool)
    (counter nxTail dxTail nyTail dyTail suffix : List Bool) :
    BoundedRun (locatorMachine total sourceLater)
      (headerInput sx counter nxTail dxTail nyTail dyTail (before++source::following) suffix)
      (locatorPort total sourceLater)
      (sourceOutput sx counter nxTail dxTail nyTail dyTail before source following suffix)
      (locatorFee total sourceLater nxTail dxTail nyTail dyTail before source following) := by
  have latest := latest_bounded total (before++source::following) hcount sx counter nxTail dxTail nyTail dyTail suffix
  have output_eq : bankEndAny false (globalSourceLeft sx counter nxTail dxTail nyTail dyTail)
      (before++source::following) suffix=
      Tape.mk₂ (cachedFinish following
        (false::cachedSourceArchive (globalSourceLeft sx counter nxTail dxTail nyTail dyTail) before source) source.digits)
        (true::suffix) := by
    simp only [bankEndAny,latestLeft_split,latestBit_true]
  rw [output_eq] at latest
  have back := cached_back_bounded sourceLater following hsource
    (cachedSourceArchive (globalSourceLeft sx counter nxTail dxTail nyTail dyTail) before source) source.digits suffix
  have combined := latest.seq back
  simpa only [locatorMachine,locatorPort,locatorCap,locatorFee,sourceOutput] using combined

theorem locatorCap_eq (total sourceLater : Nat) : locatorCap total sourceLater=9*total+13*sourceLater+28 := by
  unfold locatorCap latestCap cachedBackCap cachedBackEndCap
  rw [forwardCap_eq,backwardCap_eq]
  omega

def locatorFamily (p total sourceLater : Nat) (_memory : Fin (p+1)) : Machine (locatorCap total sourceLater) :=
  locatorMachine total sourceLater
def locatorPorts (p total sourceLater : Nat) (_memory : Fin (p+1)) (_local : Fin (locatorCap total sourceLater+1)) :
    Option (Fin (p+1) × Fin (locatorCap total sourceLater+1)) := none
def carryCap (p total sourceLater : Nat) : Nat := totalStates p (locatorCap total sourceLater)
attribute [local implicit_reducible] carryCap totalStates

def carryLocatorMachine (p total sourceLater : Nat) : Machine (carryCap p total sourceLater) :=
  blockMachine (locatorFamily p total sourceLater) (locatorPorts p total sourceLater)
def carryEntry (p total sourceLater : Nat) (memory : Fin (p+1)) : Fin (carryCap p total sourceLater+1) :=
  label memory (0 : Fin (locatorCap total sourceLater+1))
def carryPort (p total sourceLater : Nat) (memory : Fin (p+1)) : Fin (carryCap p total sourceLater+1) :=
  label memory (locatorPort total sourceLater)

/-- Opaque carry, including p=127's actual U-zero bit, is retained. No
memory tuple or source head is given freely by an original caller. -/
theorem carry_locator_contract (p total sourceLater : Nat) (memory : Fin (p+1))
    (before : List RecordSpec) (source : RecordSpec) (following : List RecordSpec)
    (hcount : (before++source::following).length=total) (hsource : following.length=sourceLater)
    (sx : Bool) (counter nxTail dxTail nyTail dyTail suffix : List Bool) :
    ∃ trace, PSTRTMSeq005.RunsFrom (carryLocatorMachine p total sourceLater)
        ⟨carryEntry p total sourceLater memory,
          headerInput sx counter nxTail dxTail nyTail dyTail (before++source::following) suffix⟩ trace
        ⟨carryPort p total sourceLater memory,
          sourceOutput sx counter nxTail dxTail nyTail dyTail before source following suffix⟩ ∧
      trace.length≤locatorFee total sourceLater nxTail dxTail nyTail dyTail before source following ∧
      ∀ prefixLength chargedL, visitedSpace (carryLocatorMachine p total sourceLater) chargedL (trace.take prefixLength)≤
        chargedL+2*locatorFee total sourceLater nxTail dxTail nyTail dyTail before source following+1 := by
  obtain ⟨trace,hr,hl⟩ := locator_bounded total sourceLater before source following hcount hsource sx
    counter nxTail dxTail nyTail dyTail suffix
  have lifted := block_runsFrom (locatorFamily p total sourceLater) (locatorPorts p total sourceLater) memory _ _ _ hr rfl
  refine ⟨trace.map (blockCfg (s:=locatorCap total sourceLater) memory),?_,?_,?_⟩
  · simpa only [carryLocatorMachine,carryEntry,carryPort,blockCfg] using lifted
  · simpa only [List.length_map] using hl
  · intro prefixLength chargedL
    have hs := PSTRTMTrace002.visitedSpace_le (carryLocatorMachine p total sourceLater) chargedL
      ((trace.map (blockCfg (s:=locatorCap total sourceLater) memory)).take prefixLength)
    have ht : ((trace.map (blockCfg (s:=locatorCap total sourceLater) memory)).take prefixLength).length≤trace.length := by
      simp only [List.length_take,List.length_map]
      omega
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPair054
