module
public import Structure.PA17_TM_RatArithmetic_CachedPair_054a
public import Structure.PA17_TM_RatArithmetic_CachedLoad_038r
public import Structure.PA17_TM_RatArithmetic_WorkHome_046b

/-! Two original fields through an already-produced nonempty cache bank.
The first actual loader, physical work-home, and second shared loader are
sequenced before exposing BReady. The optional plain017 stage is separate:
the final output consumer044 instead consumes BReady itself. Only fixed
field choices, record count and finite row bound enter executable code. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPair054

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticRecordNav032
open PA17TMRatArithmeticCachedLoad038 PA17TMRatArithmeticFarLoad031
open PA17TMRatArithmeticMul047 PA17TMRatArithmeticPairInput050

theorem bankTail_append (records : List RecordSpec) (word suffix : List Bool) :
    bankTail records (word++suffix)=bankTail records word++suffix := by
  induction records with
  | nil => rfl
  | cons record records ih =>
    simp only [bankTail,recordWord,ih,List.append_assoc,List.cons_append]

def originalBankLeft (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool)
    (first : RecordSpec) (records : List RecordSpec) : List Bool :=
  bankLeftAny false (globalSourceLeft sx counter nxTail dxTail nyTail dyTail) (first::records)

theorem originalBankLeft_home (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool)
    (first : RecordSpec) (records : List RecordSpec) :
    originalBankLeft sx counter nxTail dxTail nyTail dyTail first records=
      bankLeft (PA17TMRatArithmeticReturnHome037.firstLeft sx counter
        (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail) first) records := by
  rw [originalBankLeft,globalSourceLeft_footer]
  rfl

/-- Only a final blank descriptor is added; all A END/B DATA cells keep
their actual positions, including across the complete nonzero cache bank. -/
theorem shared_empty_bank_tape (sx : Bool) (counter nxTail dxTail nyTail dyTail a : List Bool)
    (first : RecordSpec) (records : List RecordSpec) (gap : Nat) :
    PA17TMRatArithmeticReturnHome037.homeOutput sx counter
      (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail) first records
      (List.replicate gap false++true::false::PA17TMRatArithmeticCopy006.workspace a)=
      headerInput sx counter nxTail dxTail nyTail dyTail (first::records) (copyWork .shared gap a []) := by
  have suffix : copyWork .shared gap a []=
      (List.replicate gap false++true::false::PA17TMRatArithmeticCopy006.workspace a)++[false] := by
    simp only [copyWork,PA17TMRatArithmeticPairExcursion041.workSuffix,
      PA17TMRatArithmeticCopy006.workspace,PSTRTMIncrement009.blocks,List.flatMap_nil,
      List.append_assoc,List.cons_append,List.nil_append]
  unfold PA17TMRatArithmeticReturnHome037.homeOutput headerInput sourceHeaderTape
  rw [sourceBank_widthBank]
  rw [suffix,bankTail_append (first::records)
    (List.replicate gap false++true::false::PA17TMRatArithmeticCopy006.workspace a) [false]]
  rw [←PA17TMRatArithmeticPairEncode017.tape_trailing_false counter
    (prefixRight sx (bank (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail)
      (bankTail (first::records)
        (List.replicate gap false++true::false::PA17TMRatArithmeticCopy006.workspace a))))]
  congr 1
  simp only [prefixRight,bank,nxStream,List.append_assoc,List.cons_append]

def originalFirstCap (j : Nat) : Nat := originalBankRowCap j .plain+
  PA17TMRatArithmeticWorkHome046.withCacheCap j+1
def originalReadyCap (j : Nat) : Nat := originalFirstCap j+originalBankRowCap j .shared+1
def originalPairCap (j : Nat) : Nat := originalReadyCap j+47+1
attribute [local implicit_reducible] originalFirstCap originalReadyCap originalPairCap totalStates

def originalFirstRow (field : SourceField) (memory j : Nat) : Machine (originalFirstCap j) :=
  PSTRTMSeq005.seqMachine (a:=originalBankRowCap j .plain)
    (b:=PA17TMRatArithmeticWorkHome046.withCacheCap j)
    (originalBankRowMachine memory field j .plain) (PA17TMRatArithmeticWorkHome046.withCacheMachine j)
def originalFirstPort (j : Nat) : Fin (originalFirstCap j+1) :=
  PSTRTMSeq005.rightLabel (a:=originalBankRowCap j .plain) (PA17TMRatArithmeticWorkHome046.withCachePort j)

def originalReadyRow (fieldA fieldB : SourceField) (memory j : Nat) : Machine (originalReadyCap j) :=
  PSTRTMSeq005.seqMachine (a:=originalFirstCap j) (b:=originalBankRowCap j .shared)
    (originalFirstRow fieldA memory j) (originalBankRowMachine memory fieldB j .shared)
def originalReadyPort (j : Nat) : Fin (originalReadyCap j+1) :=
  PSTRTMSeq005.rightLabel (a:=originalFirstCap j) (originalBankRowPort j .shared)

def originalPairRow (fieldA fieldB : SourceField) (memory j : Nat) : Machine (originalPairCap j) :=
  PSTRTMSeq005.seqMachine (a:=originalReadyCap j) (b:=47)
    (originalReadyRow fieldA fieldB memory j) PA17TMRatArithmeticPairEncode017.plainMachine
def originalPairPort (j : Nat) : Fin (originalPairCap j+1) :=
  PSTRTMSeq005.rightLabel (a:=originalReadyCap j) (47 : Fin 48)

def originalWorkHeader (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool)
    (first : RecordSpec) (records : List RecordSpec) (gap : Nat) : Tape Bool :=
  headerInput sx counter nxTail dxTail nyTail dyTail (first::records) (copyWork .plain gap [] [])

def originalWorkArchive (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool)
    (first : RecordSpec) (records : List RecordSpec) (gap : Nat) : List Bool :=
  true::(List.replicate gap false++true::originalBankLeft sx counter nxTail dxTail nyTail dyTail first records)

def originalBReady (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool)
    (first : RecordSpec) (records : List RecordSpec) (gap : Nat) (a b : List Bool) : Tape Bool :=
  Tape.mk₂ (destinationLeft .shared
    (originalBankLeft sx counter nxTail dxTail nyTail dyTail first records) a gap true)
    (PA17TMRatArithmeticCopy006.workspace b)

def originalNativeInput (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool)
    (first : RecordSpec) (records : List RecordSpec) (gap a b : Nat) : Tape Bool :=
  Tape.mk₂ (false::originalWorkArchive sx counter nxTail dxTail nyTail dyTail first records gap)
    (encodeNat a++encodeNat b)

def originalHomeFee (j : Nat) (first : RecordSpec) (records : List RecordSpec)
    (nxTail dxTail nyTail dyTail : List Bool) (gap : Nat) : Nat :=
  gap+totalGap (first::records)+2*totalWidth (first::records)+12*j+
    2*PA17TMRatArithmeticFarLoad031.bankWidth nxTail dxTail nyTail dyTail+54
def originalFirstFee (field : SourceField) (j : Nat) (first : RecordSpec) (records : List RecordSpec)
    (nxTail dxTail nyTail dyTail : List Bool) (gap : Nat) : Nat :=
  originalBankRowFee field .plain j gap first records nxTail dxTail nyTail dyTail []+
    originalHomeFee j first records nxTail dxTail nyTail dyTail gap
def originalReadyFee (fieldA fieldB : SourceField) (memory j : Nat) (first : RecordSpec)
    (records : List RecordSpec) (nxTail dxTail nyTail dyTail : List Bool) (gap : Nat) : Nat :=
  originalFirstFee fieldA j first records nxTail dxTail nyTail dyTail gap+
    originalBankRowFee fieldB .shared j gap first records nxTail dxTail nyTail dyTail
      (restoredDigits fieldA memory nxTail dxTail nyTail dyTail)
def originalPairFee (fieldA fieldB : SourceField) (memory j : Nat) (first : RecordSpec)
    (records : List RecordSpec) (nxTail dxTail nyTail dyTail : List Bool) (gap a b : Nat) : Nat :=
  originalReadyFee fieldA fieldB memory j first records nxTail dxTail nyTail dyTail gap+
    64*((PA17TMRatArithmeticPairEncode017.payload a).length+
      (PA17TMRatArithmeticPairEncode017.payload b).length+1)^2

theorem original_first_bounded (field : SourceField) (memory j : Nat) (first : RecordSpec)
    (records : List RecordSpec) (hj : records.length=j) (sx : Bool)
    (counter nxTail dxTail nyTail dyTail : List Bool) (gap : Nat) :
    BoundedRun (originalFirstRow field memory j)
      (originalWorkHeader sx counter nxTail dxTail nyTail dyTail first records gap) (originalFirstPort j)
      (headerInput sx counter nxTail dxTail nyTail dyTail (first::records)
        (copyWork .shared gap (restoredDigits field memory nxTail dxTail nyTail dyTail) []))
      (originalFirstFee field j first records nxTail dxTail nyTail dyTail gap) := by
  have load := original_bank_row_bounded memory field j .plain first records hj sx counter
    nxTail dxTail nyTail dyTail [] gap
  have home := PA17TMRatArithmeticWorkHome046.with_cache_work_home_bounded j first records hj sx counter
    (false::nxTail) (false::dxTail) (false::nyTail) dyTail gap
    (PA17TMRatArithmeticCopy006.workspace (restoredDigits field memory nxTail dxTail nyTail dyTail))
  change BoundedRun (PA17TMRatArithmeticWorkHome046.withCacheMachine j)
    (Tape.mk₂ (destinationLeft .plain
      (originalBankLeft sx counter nxTail dxTail nyTail dyTail first records) [] gap true)
      (PA17TMRatArithmeticCopy006.workspace (restoredDigits field memory nxTail dxTail nyTail dyTail)))
    (PA17TMRatArithmeticWorkHome046.withCachePort j)
    (PA17TMRatArithmeticReturnHome037.homeOutput sx counter
      (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail) first records
      (List.replicate gap false++true::false::PA17TMRatArithmeticCopy006.workspace
        (restoredDigits field memory nxTail dxTail nyTail dyTail))) _ at home
  rw [shared_empty_bank_tape] at home
  have combined := load.seq home
  simpa only [originalFirstRow,originalFirstPort,originalFirstCap,originalFirstFee,originalHomeFee,
    originalWorkHeader,headerInput,originalBankLeft,restoredDigits,
    PA17TMRatArithmeticFarLoad031.bankWidth,PA17TMRatArithmeticWidth018.bankWidth] using combined

theorem original_ready_bounded (fieldA fieldB : SourceField) (memory j : Nat) (first : RecordSpec)
    (records : List RecordSpec) (hj : records.length=j) (sx : Bool)
    (counter nxTail dxTail nyTail dyTail : List Bool) (gap : Nat) :
    BoundedRun (originalReadyRow fieldA fieldB memory j)
      (originalWorkHeader sx counter nxTail dxTail nyTail dyTail first records gap) (originalReadyPort j)
      (originalBReady sx counter nxTail dxTail nyTail dyTail first records gap
        (restoredDigits fieldA memory nxTail dxTail nyTail dyTail)
        (restoredDigits fieldB memory nxTail dxTail nyTail dyTail))
      (originalReadyFee fieldA fieldB memory j first records nxTail dxTail nyTail dyTail gap) := by
  have firstRun := original_first_bounded fieldA memory j first records hj sx counter
    nxTail dxTail nyTail dyTail gap
  have secondRun := original_bank_row_bounded memory fieldB j .shared first records hj sx counter
    nxTail dxTail nyTail dyTail (restoredDigits fieldA memory nxTail dxTail nyTail dyTail) gap
  have combined := firstRun.seq secondRun
  simpa only [originalReadyRow,originalReadyPort,originalReadyCap,originalReadyFee,
    originalBReady,originalBankLeft,headerInput,restoredDigits] using combined

theorem original_pair_bounded (fieldA fieldB : SourceField) (memory j : Nat) (first : RecordSpec)
    (records : List RecordSpec) (hj : records.length=j) (sx : Bool)
    (counter nxTail dxTail nyTail dyTail : List Bool) (gap a b : Nat)
    (ha : restoredDigits fieldA memory nxTail dxTail nyTail dyTail=PA17TMRatArithmeticPairEncode017.payload a)
    (hb : restoredDigits fieldB memory nxTail dxTail nyTail dyTail=PA17TMRatArithmeticPairEncode017.payload b) :
    BoundedRun (originalPairRow fieldA fieldB memory j)
      (originalWorkHeader sx counter nxTail dxTail nyTail dyTail first records gap) (originalPairPort j)
      (originalNativeInput sx counter nxTail dxTail nyTail dyTail first records gap a b)
      (originalPairFee fieldA fieldB memory j first records nxTail dxTail nyTail dyTail gap a b) := by
  have ready := original_ready_bounded fieldA fieldB memory j first records hj sx counter
    nxTail dxTail nyTail dyTail gap
  rw [ha,hb] at ready
  let archive := originalWorkArchive sx counter nxTail dxTail nyTail dyTail first records gap
  have serialize : BoundedRun PA17TMRatArithmeticPairEncode017.plainMachine
      (originalBReady sx counter nxTail dxTail nyTail dyTail first records gap
        (PA17TMRatArithmeticPairEncode017.payload a) (PA17TMRatArithmeticPairEncode017.payload b)) 47
      (originalNativeInput sx counter nxTail dxTail nyTail dyTail first records gap a b)
      (64*((PA17TMRatArithmeticPairEncode017.payload a).length+
        (PA17TMRatArithmeticPairEncode017.payload b).length+1)^2) :=
    ⟨PA17TMRatArithmeticPairEncode017.plainTrace archive a b,
      PA17TMRatArithmeticPairEncode017.plain_runsFrom archive a b,
      PA17TMRatArithmeticPairEncode017.pair_time_le false archive a b []⟩
  have combined := ready.seq serialize
  simpa only [originalPairRow,originalPairPort,originalPairCap,originalPairFee] using combined

def originalReadyFamily (p : Nat) (fieldA fieldB : SourceField) (j : Nat)
    (memory : Fin (p+1)) : Machine (originalReadyCap j) := originalReadyRow fieldA fieldB memory.val j
def originalPairFamily (p : Nat) (fieldA fieldB : SourceField) (j : Nat)
    (memory : Fin (p+1)) : Machine (originalPairCap j) := originalPairRow fieldA fieldB memory.val j
def noReadyPorts (p j : Nat) (_memory : Fin (p+1)) (_local : Fin (originalReadyCap j+1)) :
    Option (Fin (p+1) × Fin (originalReadyCap j+1)) := none
def noPairPorts (p j : Nat) (_memory : Fin (p+1)) (_local : Fin (originalPairCap j+1)) :
    Option (Fin (p+1) × Fin (originalPairCap j+1)) := none
def originalReadyMachine (p : Nat) (fieldA fieldB : SourceField) (j : Nat) :
    Machine (totalStates p (originalReadyCap j)) :=
  blockMachine (originalReadyFamily p fieldA fieldB j) (noReadyPorts p j)
def originalPairMachine (p : Nat) (fieldA fieldB : SourceField) (j : Nat) :
    Machine (totalStates p (originalPairCap j)) :=
  blockMachine (originalPairFamily p fieldA fieldB j) (noPairPorts p j)

/-- The memory comes from the incoming actual control row. The two saved
original LSB writes are installed in every row before any input is seen. -/
theorem original_ready_contract (p : Nat) (fieldA fieldB : SourceField) (j : Nat)
    (memory : Fin (p+1)) (first : RecordSpec) (records : List RecordSpec) (hj : records.length=j)
    (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool) (gap : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (originalReadyMachine p fieldA fieldB j)
        (blockCfg memory (⟨0,originalWorkHeader sx counter nxTail dxTail nyTail dyTail first records gap⟩ :
          MachineState (originalReadyCap j))) trace
        (blockCfg memory (⟨originalReadyPort j,originalBReady sx counter nxTail dxTail nyTail dyTail first records gap
          (restoredDigits fieldA memory.val nxTail dxTail nyTail dyTail)
          (restoredDigits fieldB memory.val nxTail dxTail nyTail dyTail)⟩ : MachineState (originalReadyCap j))) ∧
      trace.length≤originalReadyFee fieldA fieldB memory.val j first records nxTail dxTail nyTail dyTail gap ∧
      ∀ k inputLength, visitedSpace (originalReadyMachine p fieldA fieldB j) inputLength (trace.take k)≤
        inputLength+2*originalReadyFee fieldA fieldB memory.val j first records nxTail dxTail nyTail dyTail gap+1 := by
  obtain ⟨trace,hr,hl⟩ := original_ready_bounded fieldA fieldB memory.val j first records hj sx counter
    nxTail dxTail nyTail dyTail gap
  have lifted := block_runsFrom (originalReadyFamily p fieldA fieldB j) (noReadyPorts p j) memory _ _ _ hr rfl
  refine ⟨trace.map (blockCfg (s:=originalReadyCap j) memory),lifted,?_,?_⟩
  · simpa only [List.length_map] using hl
  · intro k inputLength
    have hs := PSTRTMTrace002.visitedSpace_le (originalReadyMachine p fieldA fieldB j) inputLength
      ((trace.map (blockCfg (s:=originalReadyCap j) memory)).take k)
    have ht : ((trace.map (blockCfg (s:=originalReadyCap j) memory)).take k).length≤trace.length := by
      simp only [List.length_take,List.length_map]
      omega
    omega

theorem original_pair_contract (p : Nat) (fieldA fieldB : SourceField) (j : Nat)
    (memory : Fin (p+1)) (first : RecordSpec) (records : List RecordSpec) (hj : records.length=j)
    (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool) (gap a b : Nat)
    (ha : restoredDigits fieldA memory.val nxTail dxTail nyTail dyTail=PA17TMRatArithmeticPairEncode017.payload a)
    (hb : restoredDigits fieldB memory.val nxTail dxTail nyTail dyTail=PA17TMRatArithmeticPairEncode017.payload b) :
    ∃ trace, PSTRTMSeq005.RunsFrom (originalPairMachine p fieldA fieldB j)
        (blockCfg memory (⟨0,originalWorkHeader sx counter nxTail dxTail nyTail dyTail first records gap⟩ :
          MachineState (originalPairCap j))) trace
        (blockCfg memory (⟨originalPairPort j,originalNativeInput sx counter nxTail dxTail nyTail dyTail
          first records gap a b⟩ : MachineState (originalPairCap j))) ∧
      trace.length≤originalPairFee fieldA fieldB memory.val j first records nxTail dxTail nyTail dyTail gap a b ∧
      ∀ k inputLength, visitedSpace (originalPairMachine p fieldA fieldB j) inputLength (trace.take k)≤
        inputLength+2*originalPairFee fieldA fieldB memory.val j first records nxTail dxTail nyTail dyTail gap a b+1 := by
  obtain ⟨trace,hr,hl⟩ := original_pair_bounded fieldA fieldB memory.val j first records hj sx counter
    nxTail dxTail nyTail dyTail gap a b ha hb
  have lifted := block_runsFrom (originalPairFamily p fieldA fieldB j) (noPairPorts p j) memory _ _ _ hr rfl
  refine ⟨trace.map (blockCfg (s:=originalPairCap j) memory),lifted,?_,?_⟩
  · simpa only [List.length_map] using hl
  · intro k inputLength
    have hs := PSTRTMTrace002.visitedSpace_le (originalPairMachine p fieldA fieldB j) inputLength
      ((trace.map (blockCfg (s:=originalPairCap j) memory)).take k)
    have ht : ((trace.map (blockCfg (s:=originalPairCap j) memory)).take k).length≤trace.length := by
      simp only [List.length_take,List.length_map]
      omega
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPair054
