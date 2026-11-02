module
public import Structure.PA17_TM_RatArithmetic_CachedPair_054d

/-! Two statically selected cached records become real operands A/B.
Both source LSBs are actually read and restored by038; both destination
LSBs are restored before the true BReady halt. No bank values, observed
bits, widths or runtime record counts parameterize the executable code. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPair054

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticCachedLoad038
open PA17TMRatArithmeticFarLoad031 PA17TMRatArithmeticMul047

def cachedReadyCap (j aLater bLater : Nat) : Nat := cachedFirstCap j aLater+selectedSharedCap (j+1) bLater+1
def cachedPairCap (j aLater bLater : Nat) : Nat := cachedReadyCap j aLater bLater+47+1
attribute [local implicit_reducible] cachedReadyCap cachedPairCap cachedFirstCap selectedSharedCap
  selectedPlainCap locatorCap latestCap plainKernelCap sharedKernelCap totalStates

def cachedReadyRow (j aLater bLater : Nat) : Machine (cachedReadyCap j aLater bLater) :=
  PSTRTMSeq005.seqMachine (a:=cachedFirstCap j aLater) (b:=selectedSharedCap (j+1) bLater)
    (cachedFirstMachine j aLater) (selectedSharedMachine (j+1) bLater)
def cachedReadyPort (j aLater bLater : Nat) (bitB : Bool) : Fin (cachedReadyCap j aLater bLater+1) :=
  PSTRTMSeq005.rightLabel (a:=cachedFirstCap j aLater) (selectedSharedPort (j+1) bLater bitB)
def cachedPairRow (j aLater bLater : Nat) : Machine (cachedPairCap j aLater bLater) :=
  PSTRTMSeq005.seqMachine (a:=cachedReadyCap j aLater bLater) (b:=47)
    (cachedReadyRow j aLater bLater) PA17TMRatArithmeticPairEncode017.plainMachine
def cachedPairPort (j aLater bLater : Nat) : Fin (cachedPairCap j aLater bLater+1) :=
  PSTRTMSeq005.rightLabel (a:=cachedReadyCap j aLater bLater) (47 : Fin 48)

def cachedReadyFee (j aLater bLater : Nat) (first : RecordSpec) (records beforeA : List RecordSpec)
    (sourceA : RecordSpec) (followingA beforeB : List RecordSpec) (sourceB : RecordSpec)
    (followingB : List RecordSpec) (nxTail dxTail nyTail dyTail : List Bool) (gap : Nat) : Nat :=
  cachedFirstFee j aLater first records beforeA sourceA followingA nxTail dxTail nyTail dyTail gap+
    selectedSharedFee (j+1) bLater nxTail dxTail nyTail dyTail beforeB sourceB followingB sourceA.digits gap
def cachedPairFee (j aLater bLater : Nat) (first : RecordSpec) (records beforeA : List RecordSpec)
    (sourceA : RecordSpec) (followingA beforeB : List RecordSpec) (sourceB : RecordSpec)
    (followingB : List RecordSpec) (nxTail dxTail nyTail dyTail : List Bool) (gap a b : Nat) : Nat :=
  cachedReadyFee j aLater bLater first records beforeA sourceA followingA beforeB sourceB followingB
    nxTail dxTail nyTail dyTail gap+
    64*((PA17TMRatArithmeticPairEncode017.payload a).length+
      (PA17TMRatArithmeticPairEncode017.payload b).length+1)^2

theorem cached_ready_bounded (j aLater bLater : Nat) (first : RecordSpec)
    (records beforeA : List RecordSpec) (sourceA : RecordSpec) (followingA beforeB : List RecordSpec)
    (sourceB : RecordSpec) (followingB : List RecordSpec) (hj : records.length=j)
    (hbankA : beforeA++sourceA::followingA=first::records) (haLater : followingA.length=aLater)
    (hbankB : beforeB++sourceB::followingB=first::records) (hbLater : followingB.length=bLater)
    (bitA bitB : Bool) (tailA tailB : List Bool) (hdA : sourceA.digits=bitA::tailA) (hdB : sourceB.digits=bitB::tailB)
    (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool) (gap : Nat) :
    BoundedRun (cachedReadyRow j aLater bLater)
      (originalWorkHeader sx counter nxTail dxTail nyTail dyTail first records gap) (cachedReadyPort j aLater bLater bitB)
      (originalBReady sx counter nxTail dxTail nyTail dyTail first records gap sourceA.digits sourceB.digits)
      (cachedReadyFee j aLater bLater first records beforeA sourceA followingA beforeB sourceB followingB
        nxTail dxTail nyTail dyTail gap) := by
  have firstRun := cached_first_bounded j aLater first records beforeA sourceA followingA hj hbankA haLater
    bitA tailA hdA sx counter nxTail dxTail nyTail dyTail gap
  have htotal : (beforeB++sourceB::followingB).length=j+1 := by rw [hbankB]; simp only [List.length_cons,hj]
  have secondRun := selected_shared_bounded (j+1) bLater beforeB sourceB followingB htotal hbLater
    bitB tailB hdB sx counter nxTail dxTail nyTail dyTail sourceA.digits gap
  rw [hbankB] at secondRun
  have combined := firstRun.seq secondRun
  simpa only [cachedReadyRow,cachedReadyPort,cachedReadyCap,cachedReadyFee,
    originalBReady,originalBankLeft,copyWork] using combined

theorem cached_pair_bounded (j aLater bLater : Nat) (first : RecordSpec)
    (records beforeA : List RecordSpec) (sourceA : RecordSpec) (followingA beforeB : List RecordSpec)
    (sourceB : RecordSpec) (followingB : List RecordSpec) (hj : records.length=j)
    (hbankA : beforeA++sourceA::followingA=first::records) (haLater : followingA.length=aLater)
    (hbankB : beforeB++sourceB::followingB=first::records) (hbLater : followingB.length=bLater)
    (bitA bitB : Bool) (tailA tailB : List Bool) (hdA : sourceA.digits=bitA::tailA) (hdB : sourceB.digits=bitB::tailB)
    (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool) (gap a b : Nat)
    (ha : sourceA.digits=PA17TMRatArithmeticPairEncode017.payload a)
    (hb : sourceB.digits=PA17TMRatArithmeticPairEncode017.payload b) :
    BoundedRun (cachedPairRow j aLater bLater)
      (originalWorkHeader sx counter nxTail dxTail nyTail dyTail first records gap) (cachedPairPort j aLater bLater)
      (originalNativeInput sx counter nxTail dxTail nyTail dyTail first records gap a b)
      (cachedPairFee j aLater bLater first records beforeA sourceA followingA beforeB sourceB followingB
        nxTail dxTail nyTail dyTail gap a b) := by
  have ready := cached_ready_bounded j aLater bLater first records beforeA sourceA followingA beforeB sourceB followingB
    hj hbankA haLater hbankB hbLater bitA bitB tailA tailB hdA hdB sx counter nxTail dxTail nyTail dyTail gap
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
  simpa only [cachedPairRow,cachedPairPort,cachedPairCap,cachedPairFee] using combined

def cachedReadyFamily (p j aLater bLater : Nat) (_memory : Fin (p+1)) : Machine (cachedReadyCap j aLater bLater) :=
  cachedReadyRow j aLater bLater
def cachedPairFamily (p j aLater bLater : Nat) (_memory : Fin (p+1)) : Machine (cachedPairCap j aLater bLater) :=
  cachedPairRow j aLater bLater
def noCachedReadyPorts (p j aLater bLater : Nat) (_memory : Fin (p+1))
    (_local : Fin (cachedReadyCap j aLater bLater+1)) :
    Option (Fin (p+1) × Fin (cachedReadyCap j aLater bLater+1)) := none
def noCachedPairPorts (p j aLater bLater : Nat) (_memory : Fin (p+1))
    (_local : Fin (cachedPairCap j aLater bLater+1)) :
    Option (Fin (p+1) × Fin (cachedPairCap j aLater bLater+1)) := none
def cachedReadyMachine (p j aLater bLater : Nat) : Machine (totalStates p (cachedReadyCap j aLater bLater)) :=
  blockMachine (cachedReadyFamily p j aLater bLater) (noCachedReadyPorts p j aLater bLater)
def cachedPairMachine (p j aLater bLater : Nat) : Machine (totalStates p (cachedPairCap j aLater bLater)) :=
  blockMachine (cachedPairFamily p j aLater bLater) (noCachedPairPorts p j aLater bLater)

/-- BReady has two genuine final ports determined by the actual B read,
while old carry is unchanged. A caller must pay its transfer from either
real port. No host evaluation of B or final sign is claimed here. -/
theorem cached_ready_contract (p j aLater bLater : Nat) (memory : Fin (p+1)) (first : RecordSpec)
    (records beforeA : List RecordSpec) (sourceA : RecordSpec) (followingA beforeB : List RecordSpec)
    (sourceB : RecordSpec) (followingB : List RecordSpec) (hj : records.length=j)
    (hbankA : beforeA++sourceA::followingA=first::records) (haLater : followingA.length=aLater)
    (hbankB : beforeB++sourceB::followingB=first::records) (hbLater : followingB.length=bLater)
    (bitA bitB : Bool) (tailA tailB : List Bool) (hdA : sourceA.digits=bitA::tailA) (hdB : sourceB.digits=bitB::tailB)
    (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool) (gap : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (cachedReadyMachine p j aLater bLater)
        (blockCfg memory (⟨0,originalWorkHeader sx counter nxTail dxTail nyTail dyTail first records gap⟩ :
          MachineState (cachedReadyCap j aLater bLater))) trace
        (blockCfg memory (⟨cachedReadyPort j aLater bLater bitB,
          originalBReady sx counter nxTail dxTail nyTail dyTail first records gap sourceA.digits sourceB.digits⟩ :
          MachineState (cachedReadyCap j aLater bLater))) ∧
      trace.length≤cachedReadyFee j aLater bLater first records beforeA sourceA followingA beforeB sourceB followingB
        nxTail dxTail nyTail dyTail gap ∧
      ∀ k inputLength, visitedSpace (cachedReadyMachine p j aLater bLater) inputLength (trace.take k)≤
        inputLength+2*cachedReadyFee j aLater bLater first records beforeA sourceA followingA beforeB sourceB followingB
          nxTail dxTail nyTail dyTail gap+1 := by
  obtain ⟨trace,hr,hl⟩ := cached_ready_bounded j aLater bLater first records beforeA sourceA followingA beforeB sourceB
    followingB hj hbankA haLater hbankB hbLater bitA bitB tailA tailB hdA hdB sx counter nxTail dxTail nyTail dyTail gap
  have lifted := block_runsFrom (cachedReadyFamily p j aLater bLater) (noCachedReadyPorts p j aLater bLater)
    memory _ _ _ hr rfl
  refine ⟨trace.map (blockCfg (s:=cachedReadyCap j aLater bLater) memory),lifted,?_,?_⟩
  · simpa only [List.length_map] using hl
  · intro k inputLength
    have hs := PSTRTMTrace002.visitedSpace_le (cachedReadyMachine p j aLater bLater) inputLength
      ((trace.map (blockCfg (s:=cachedReadyCap j aLater bLater) memory)).take k)
    have ht : ((trace.map (blockCfg (s:=cachedReadyCap j aLater bLater) memory)).take k).length≤trace.length := by
      simp only [List.length_take,List.length_map]
      omega
    omega

theorem cached_pair_contract (p j aLater bLater : Nat) (memory : Fin (p+1)) (first : RecordSpec)
    (records beforeA : List RecordSpec) (sourceA : RecordSpec) (followingA beforeB : List RecordSpec)
    (sourceB : RecordSpec) (followingB : List RecordSpec) (hj : records.length=j)
    (hbankA : beforeA++sourceA::followingA=first::records) (haLater : followingA.length=aLater)
    (hbankB : beforeB++sourceB::followingB=first::records) (hbLater : followingB.length=bLater)
    (bitA bitB : Bool) (tailA tailB : List Bool) (hdA : sourceA.digits=bitA::tailA) (hdB : sourceB.digits=bitB::tailB)
    (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool) (gap a b : Nat)
    (ha : sourceA.digits=PA17TMRatArithmeticPairEncode017.payload a)
    (hb : sourceB.digits=PA17TMRatArithmeticPairEncode017.payload b) :
    ∃ trace, PSTRTMSeq005.RunsFrom (cachedPairMachine p j aLater bLater)
        (blockCfg memory (⟨0,originalWorkHeader sx counter nxTail dxTail nyTail dyTail first records gap⟩ :
          MachineState (cachedPairCap j aLater bLater))) trace
        (blockCfg memory (⟨cachedPairPort j aLater bLater,
          originalNativeInput sx counter nxTail dxTail nyTail dyTail first records gap a b⟩ :
          MachineState (cachedPairCap j aLater bLater))) ∧
      trace.length≤cachedPairFee j aLater bLater first records beforeA sourceA followingA beforeB sourceB followingB
        nxTail dxTail nyTail dyTail gap a b ∧
      ∀ k inputLength, visitedSpace (cachedPairMachine p j aLater bLater) inputLength (trace.take k)≤
        inputLength+2*cachedPairFee j aLater bLater first records beforeA sourceA followingA beforeB sourceB followingB
          nxTail dxTail nyTail dyTail gap a b+1 := by
  obtain ⟨trace,hr,hl⟩ := cached_pair_bounded j aLater bLater first records beforeA sourceA followingA beforeB sourceB
    followingB hj hbankA haLater hbankB hbLater bitA bitB tailA tailB hdA hdB sx counter nxTail dxTail nyTail dyTail
    gap a b ha hb
  have lifted := block_runsFrom (cachedPairFamily p j aLater bLater) (noCachedPairPorts p j aLater bLater)
    memory _ _ _ hr rfl
  refine ⟨trace.map (blockCfg (s:=cachedPairCap j aLater bLater) memory),lifted,?_,?_⟩
  · simpa only [List.length_map] using hl
  · intro k inputLength
    have hs := PSTRTMTrace002.visitedSpace_le (cachedPairMachine p j aLater bLater) inputLength
      ((trace.map (blockCfg (s:=cachedPairCap j aLater bLater) memory)).take k)
    have ht : ((trace.map (blockCfg (s:=cachedPairCap j aLater bLater) memory)).take k).length≤trace.length := by
      simp only [List.length_take,List.length_map]
      omega
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPair054
