module
public import Structure.PA17_TM_RatArithmetic_CachedPair_054b
public import Structure.PA17_TM_RatArithmetic_CachedLoad_038p

/-! Actual cached-field observation remains inside the fixed loader. Its
observed HALT port is transferred by a paid Seq transition; an enclosing
pair row therefore retains opaque old carry without taking a bit answer.
This module is checked only after038p's complete shared-loader freeze. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPair054

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticCachedLoad038
open PA17TMRatArithmeticFarLoad031 PA17TMRatArithmeticMul047 PA17TMRatArithmeticPairInput050

def plainKernelCap (j : Nat) : Nat := totalStates 2 (cachedPlainLocalCap j)
def sharedKernelCap (j : Nat) : Nat := totalStates 2 (cachedSharedLocalCap j)
attribute [local implicit_reducible] plainKernelCap sharedKernelCap totalStates

def sharedKernel (j : Nat) : Machine (sharedKernelCap j) :=
  observeThenMachine (cached_shared_reader_room j) (cachedSharedBodies j)

theorem plain_kernel_bounded (j : Nat) (records : List RecordSpec) (hj : records.length=j)
    (archive tail : List Bool) (bit : Bool) (gap : Nat) :
    BoundedRun (cachedPlainMachine j)
      (Tape.mk₂ (false::archive) (cachedWord records (bit::tail) (plainWorkSuffix gap [])))
      (observedPort (cachedPlainEnds j) bit)
      (Tape.mk₂ (destinationLeft .plain (cachedFinish records (false::archive) (bit::tail)) [] gap true)
        (PA17TMRatArithmeticCopy006.workspace (bit::tail))) (2+cachedPlainBodyFee j records tail gap) := by
  have hb := cached_plain_body_bounded (observedPhase bit) j records hj archive tail gap
  rw [seen_observed_bit] at hb
  have hp := bounded_pad (cached_plain_body_room j) hb
  let suffix := true::(PSTRTMIncrement009.blocks tail++false::
    (cacheContext records++true::plainWorkSuffix gap []))
  have bodyRun : BoundedRun (cachedPlainBodies j (observedPhase bit))
      (Tape.mk₂ (false::archive) (false::suffix)) (cachedPlainEnds j (observedPhase bit))
      (Tape.mk₂ (destinationLeft .plain (cachedFinish records (false::archive) (bit::tail)) [] gap true)
        (PA17TMRatArithmeticCopy006.workspace (bit::tail))) (cachedPlainBodyFee j records tail gap) := by
    simpa only [cachedPlainBodies,cachedPlainEnds,cachedWord,flagged_cons,suffix,List.cons_append] using hp
  have h := observe_then_bounded (cached_plain_reader_room j) (cachedPlainBodies j)
    (cachedPlainEnds j) (false::archive) suffix bit _ (cachedPlainBodyFee j records tail gap) bodyRun
  simpa only [cachedPlainMachine,cachedWord,flagged_cons,suffix,List.cons_append] using h

theorem shared_kernel_bounded (j : Nat) (records : List RecordSpec) (hj : records.length=j)
    (archive tail a : List Bool) (bit : Bool) (gap : Nat) :
    BoundedRun (sharedKernel j)
      (Tape.mk₂ (false::archive) (cachedWord records (bit::tail)
        (PA17TMRatArithmeticPairExcursion041.workSuffix gap a [])))
      (observedPort (cachedSharedEnds j) bit)
      (Tape.mk₂ (destinationLeft .shared (cachedFinish records (false::archive) (bit::tail)) a gap true)
        (PA17TMRatArithmeticCopy006.workspace (bit::tail))) (2+cachedSharedBodyFee j records tail a gap) := by
  have hb := cached_shared_body_bounded (observedPhase bit) j records hj archive tail a gap
  rw [seen_observed_bit] at hb
  have hp := bounded_pad (cached_shared_body_room j) hb
  let suffix := true::(PSTRTMIncrement009.blocks tail++false::
    (cacheContext records++true::PA17TMRatArithmeticPairExcursion041.workSuffix gap a []))
  have bodyRun : BoundedRun (cachedSharedBodies j (observedPhase bit))
      (Tape.mk₂ (false::archive) (false::suffix)) (cachedSharedEnds j (observedPhase bit))
      (Tape.mk₂ (destinationLeft .shared (cachedFinish records (false::archive) (bit::tail)) a gap true)
        (PA17TMRatArithmeticCopy006.workspace (bit::tail))) (cachedSharedBodyFee j records tail a gap) := by
    simpa only [cachedSharedBodies,cachedSharedEnds,cachedWord,flagged_cons,suffix,List.cons_append] using hp
  have h := observe_then_bounded (cached_shared_reader_room j) (cachedSharedBodies j)
    (cachedSharedEnds j) (false::archive) suffix bit _ (cachedSharedBodyFee j records tail a gap) bodyRun
  simpa only [sharedKernel,cachedWord,flagged_cons,suffix,List.cons_append] using h

def selectedPlainCap (total sourceLater : Nat) : Nat := locatorCap total sourceLater+plainKernelCap sourceLater+1
def selectedSharedCap (total sourceLater : Nat) : Nat := locatorCap total sourceLater+sharedKernelCap sourceLater+1
attribute [local implicit_reducible] selectedPlainCap selectedSharedCap

def selectedPlainMachine (total sourceLater : Nat) : Machine (selectedPlainCap total sourceLater) :=
  PSTRTMSeq005.seqMachine (a:=locatorCap total sourceLater) (b:=plainKernelCap sourceLater)
    (locatorMachine total sourceLater) (cachedPlainMachine sourceLater)
def selectedSharedMachine (total sourceLater : Nat) : Machine (selectedSharedCap total sourceLater) :=
  PSTRTMSeq005.seqMachine (a:=locatorCap total sourceLater) (b:=sharedKernelCap sourceLater)
    (locatorMachine total sourceLater) (sharedKernel sourceLater)
def selectedPlainPort (total sourceLater : Nat) (bit : Bool) : Fin (selectedPlainCap total sourceLater+1) :=
  PSTRTMSeq005.rightLabel (a:=locatorCap total sourceLater) (observedPort (cachedPlainEnds sourceLater) bit)
def selectedSharedPort (total sourceLater : Nat) (bit : Bool) : Fin (selectedSharedCap total sourceLater+1) :=
  PSTRTMSeq005.rightLabel (a:=locatorCap total sourceLater) (observedPort (cachedSharedEnds sourceLater) bit)

def selectedPlainFee (total sourceLater : Nat) (nxTail dxTail nyTail dyTail : List Bool)
    (before : List RecordSpec) (source : RecordSpec) (following : List RecordSpec) (gap : Nat) : Nat :=
  locatorFee total sourceLater nxTail dxTail nyTail dyTail before source following+
    (2+cachedPlainBodyFee sourceLater following source.digits.tail gap)
def selectedSharedFee (total sourceLater : Nat) (nxTail dxTail nyTail dyTail : List Bool)
    (before : List RecordSpec) (source : RecordSpec) (following : List RecordSpec) (a : List Bool) (gap : Nat) : Nat :=
  locatorFee total sourceLater nxTail dxTail nyTail dyTail before source following+
    (2+cachedSharedBodyFee sourceLater following source.digits.tail a gap)

theorem selected_plain_bounded (total sourceLater : Nat) (before : List RecordSpec) (source : RecordSpec)
    (following : List RecordSpec) (htotal : (before++source::following).length=total)
    (hsource : following.length=sourceLater) (bit : Bool) (tail : List Bool) (hdigits : source.digits=bit::tail)
    (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool) (gap : Nat) :
    BoundedRun (selectedPlainMachine total sourceLater)
      (headerInput sx counter nxTail dxTail nyTail dyTail (before++source::following) (plainWorkSuffix gap []))
      (selectedPlainPort total sourceLater bit)
      (Tape.mk₂ (destinationLeft .plain
        (bankLeftAny false (globalSourceLeft sx counter nxTail dxTail nyTail dyTail) (before++source::following))
        [] gap true) (PA17TMRatArithmeticCopy006.workspace source.digits))
      (selectedPlainFee total sourceLater nxTail dxTail nyTail dyTail before source following gap) := by
  have locate := locator_bounded total sourceLater before source following htotal hsource sx counter
    nxTail dxTail nyTail dyTail (plainWorkSuffix gap [])
  have load := plain_kernel_bounded sourceLater following hsource
    (cachedSourceArchive (globalSourceLeft sx counter nxTail dxTail nyTail dyTail) before source) tail bit gap
  rw [←hdigits,←latestLeft_split] at load
  have combined := locate.seq load
  simpa only [selectedPlainMachine,selectedPlainPort,selectedPlainCap,selectedPlainFee,sourceOutput,
    hdigits,List.tail_cons] using combined

theorem selected_shared_bounded (total sourceLater : Nat) (before : List RecordSpec) (source : RecordSpec)
    (following : List RecordSpec) (htotal : (before++source::following).length=total)
    (hsource : following.length=sourceLater) (bit : Bool) (tail : List Bool) (hdigits : source.digits=bit::tail)
    (sx : Bool) (counter nxTail dxTail nyTail dyTail a : List Bool) (gap : Nat) :
    BoundedRun (selectedSharedMachine total sourceLater)
      (headerInput sx counter nxTail dxTail nyTail dyTail (before++source::following)
        (PA17TMRatArithmeticPairExcursion041.workSuffix gap a [])) (selectedSharedPort total sourceLater bit)
      (Tape.mk₂ (destinationLeft .shared
        (bankLeftAny false (globalSourceLeft sx counter nxTail dxTail nyTail dyTail) (before++source::following))
        a gap true) (PA17TMRatArithmeticCopy006.workspace source.digits))
      (selectedSharedFee total sourceLater nxTail dxTail nyTail dyTail before source following a gap) := by
  have locate := locator_bounded total sourceLater before source following htotal hsource sx counter
    nxTail dxTail nyTail dyTail (PA17TMRatArithmeticPairExcursion041.workSuffix gap a [])
  have load := shared_kernel_bounded sourceLater following hsource
    (cachedSourceArchive (globalSourceLeft sx counter nxTail dxTail nyTail dyTail) before source) tail a bit gap
  rw [←hdigits,←latestLeft_split] at load
  have combined := locate.seq load
  simpa only [selectedSharedMachine,selectedSharedPort,selectedSharedCap,selectedSharedFee,sourceOutput,
    hdigits,List.tail_cons] using combined

def cachedFirstCap (j sourceLater : Nat) : Nat := selectedPlainCap (j+1) sourceLater+
  PA17TMRatArithmeticWorkHome046.withCacheCap j+1
attribute [local implicit_reducible] cachedFirstCap
def cachedFirstMachine (j sourceLater : Nat) : Machine (cachedFirstCap j sourceLater) :=
  PSTRTMSeq005.seqMachine (a:=selectedPlainCap (j+1) sourceLater)
    (b:=PA17TMRatArithmeticWorkHome046.withCacheCap j)
    (selectedPlainMachine (j+1) sourceLater) (PA17TMRatArithmeticWorkHome046.withCacheMachine j)
def cachedFirstPort (j sourceLater : Nat) : Fin (cachedFirstCap j sourceLater+1) :=
  PSTRTMSeq005.rightLabel (a:=selectedPlainCap (j+1) sourceLater)
    (PA17TMRatArithmeticWorkHome046.withCachePort j)
def cachedFirstFee (j sourceLater : Nat) (first : RecordSpec) (records before : List RecordSpec)
    (source : RecordSpec) (following : List RecordSpec) (nxTail dxTail nyTail dyTail : List Bool) (gap : Nat) : Nat :=
  selectedPlainFee (j+1) sourceLater nxTail dxTail nyTail dyTail before source following gap+
    originalHomeFee j first records nxTail dxTail nyTail dyTail gap

theorem cached_first_bounded (j sourceLater : Nat) (first : RecordSpec) (records before : List RecordSpec)
    (source : RecordSpec) (following : List RecordSpec) (hj : records.length=j)
    (hbank : before++source::following=first::records) (hsource : following.length=sourceLater)
    (bit : Bool) (tail : List Bool) (hdigits : source.digits=bit::tail) (sx : Bool)
    (counter nxTail dxTail nyTail dyTail : List Bool) (gap : Nat) :
    BoundedRun (cachedFirstMachine j sourceLater)
      (originalWorkHeader sx counter nxTail dxTail nyTail dyTail first records gap) (cachedFirstPort j sourceLater)
      (headerInput sx counter nxTail dxTail nyTail dyTail (first::records)
        (copyWork .shared gap source.digits []))
      (cachedFirstFee j sourceLater first records before source following nxTail dxTail nyTail dyTail gap) := by
  have htotal : (before++source::following).length=j+1 := by rw [hbank]; simp only [List.length_cons,hj]
  have load := selected_plain_bounded (j+1) sourceLater before source following htotal hsource bit tail hdigits
    sx counter nxTail dxTail nyTail dyTail gap
  rw [hbank] at load
  have home := PA17TMRatArithmeticWorkHome046.with_cache_work_home_bounded j first records hj sx counter
    (false::nxTail) (false::dxTail) (false::nyTail) dyTail gap (PA17TMRatArithmeticCopy006.workspace source.digits)
  change BoundedRun (PA17TMRatArithmeticWorkHome046.withCacheMachine j)
    (Tape.mk₂ (destinationLeft .plain
      (originalBankLeft sx counter nxTail dxTail nyTail dyTail first records) [] gap true)
      (PA17TMRatArithmeticCopy006.workspace source.digits)) (PA17TMRatArithmeticWorkHome046.withCachePort j)
    (PA17TMRatArithmeticReturnHome037.homeOutput sx counter
      (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail) first records
      (List.replicate gap false++true::false::PA17TMRatArithmeticCopy006.workspace source.digits)) _ at home
  rw [shared_empty_bank_tape] at home
  have combined := load.seq home
  simpa only [cachedFirstMachine,cachedFirstPort,cachedFirstCap,cachedFirstFee,originalHomeFee,
    originalWorkHeader,headerInput,copyWork,plainWorkSuffix,originalBankLeft,
    PA17TMRatArithmeticFarLoad031.bankWidth,PA17TMRatArithmeticWidth018.bankWidth] using combined

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPair054
