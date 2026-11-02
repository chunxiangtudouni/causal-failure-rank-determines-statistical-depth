module
public import Structure.PA17_TM_RatArithmetic_CachedLoad_038h

/-! A paid cached-source EOF hook. The actual observed bit is in a finite
control row. Rewind and restore SOURCE, follow TRUE cache ends, reach the
plain/shared destination, then really restore its LSB. One shared042 copy
loop produces this hook's already resident clamped destination. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticAllocatePass023 (pushField)

def cachedRestoredOutCap (j : Nat) : Nat := 7+cachedOutCap j+1
def cachedRestoredToDestCap (j : Nat) : Nat := cachedRestoredOutCap j+6+1
def cachedDoneCap (j : Nat) : Nat := cachedRestoredToDestCap j+1+1

def cachedRestoredOutMachine {p : Nat} (phase : Fin (2*p+2)) (j : Nat) : Machine (cachedRestoredOutCap j) :=
  PSTRTMSeq005.seqMachine (a:=7) (b:=cachedOutCap j) (sourceRestoreRow phase) (cachedOutMachine j)

def cachedRestoredToDestMachine {p : Nat} (phase : Fin (2*p+2)) (j : Nat)
    (kind : Destination) : Machine (cachedRestoredToDestCap j) :=
  PSTRTMSeq005.seqMachine (a:=cachedRestoredOutCap j) (b:=6)
    (cachedRestoredOutMachine phase j) (destinationMachine kind)

def cachedDoneRow {p : Nat} (phase : Fin (2*p+2)) (j : Nat) (kind : Destination) : Machine (cachedDoneCap j) :=
  PSTRTMSeq005.seqMachine (a:=cachedRestoredToDestCap j) (b:=1)
    (cachedRestoredToDestMachine phase j kind)
    (PA17TMRatArithmeticAllocate013.setMarkerMachine (seenBit phase))

def cachedDonePort (j : Nat) : Fin (cachedDoneCap j+1) :=
  PSTRTMSeq005.rightLabel (a:=cachedRestoredToDestCap j) 1

def copiedTail (tail suffix : List Bool) : List Bool :=
  true::(PSTRTMIncrement009.blocks tail++[false,false]++suffix)

def cachedDoneFee (j : Nat) (kind : Destination) (records : List RecordSpec)
    (sourceWidth aWidth gap : Nat) : Nat :=
  4*sourceWidth+totalGap records+2*totalWidth records+9*j+destinationFee kind aWidth gap+14

theorem cached_done_row_bounded {p : Nat} (phase : Fin (2*p+2)) (j : Nat)
    (records : List RecordSpec) (hj : records.length=j) (kind : Destination)
    (archive tail a suffix : List Bool) (gap : Nat) :
    BoundedRun (cachedDoneRow phase j kind)
      (Tape.mk₂ (pushField (false::archive) (false::tail))
        (cacheContext records++true::destinationSuffix kind a (copiedTail tail suffix) gap))
      (cachedDonePort j)
      (Tape.mk₂ (destinationLeft kind (cachedFinish records (false::archive) (seenBit phase::tail)) a gap true)
        (PSTRTMIncrement009.blocks (seenBit phase::tail)++[false,false]++suffix))
      (cachedDoneFee j kind records (false::tail).length a.length gap) := by
  have hs := sourceRestore_row_bounded phase archive tail
    (cacheContext records++true::destinationSuffix kind a (copiedTail tail suffix) gap)
  have ho := cached_out_bounded j records hj (false::archive) (seenBit phase::tail)
    (destinationSuffix kind a (copiedTail tail suffix) gap)
  have hd := destination_bounded kind true
    (cachedFinish records (false::archive) (seenBit phase::tail)) a (copiedTail tail suffix) gap
  have hw : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine (seenBit phase))
      (Tape.mk₂ (destinationLeft kind (cachedFinish records (false::archive) (seenBit phase::tail)) a gap true)
        (false::copiedTail tail suffix)) 1
      (Tape.mk₂ (destinationLeft kind (cachedFinish records (false::archive) (seenBit phase::tail)) a gap true)
        (PSTRTMIncrement009.blocks (seenBit phase::tail)++[false,false]++suffix)) 2 := by
    refine ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace false (seenBit phase)
      (destinationLeft kind (cachedFinish records (false::archive) (seenBit phase::tail)) a gap true)
      (copiedTail tail suffix),?_,by rfl⟩
    exact PA17TMRatArithmeticAllocate013.setMarker_runsFrom false (seenBit phase)
      (destinationLeft kind (cachedFinish records (false::archive) (seenBit phase::tail)) a gap true)
      (copiedTail tail suffix)
  have result := ((hs.seq ho).seq hd).seq hw
  have hc : ((2*(false::tail).length+7)+(2*(seenBit phase::tail).length+totalGap records+
      2*totalWidth records+9*j+5))+destinationFee kind a.length gap+2≤
      cachedDoneFee j kind records (false::tail).length a.length gap := by
    simp only [cachedDoneFee,List.length_cons]
    omega
  simpa only [cachedDoneRow,cachedRestoredToDestMachine,cachedRestoredOutMachine,
    cachedDonePort,cachedDoneCap,cachedRestoredToDestCap,cachedRestoredOutCap,cachedWord] using result.mono hc

def cachedDoneRows (p j : Nat) (kind : Destination) : Fin (2*p+2) → Machine (cachedDoneCap j) :=
  fun phase => cachedDoneRow phase j kind
def cachedDonePorts (p j : Nat) : Fin (2*p+2) → Fin (cachedDoneCap j+1) →
    Option (Fin (2*p+2) × Fin (cachedDoneCap j+1)) := fun _ _ => none
def cachedDoneFamily (p j : Nat) (kind : Destination) : Machine (totalStates (2*p+1) (cachedDoneCap j)) :=
  blockMachine (cachedDoneRows p j kind) (cachedDonePorts p j)

/-- The source bit is read by earlier CORE code; here it only describes
that actual incoming control row. Both SOURCE and DEST restore are real
WRITEs, and the old carry plus observation stay in the final row. -/
theorem cached_done_contract (p : Nat) (memory : Fin (p+1)) (bit : Bool) (j : Nat)
    (records : List RecordSpec) (hj : records.length=j) (kind : Destination)
    (archive tail a suffix : List Bool) (gap inputLength : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (cachedDoneFamily p j kind)
      (blockCfg (seenPhase p memory bit)
        (⟨0,Tape.mk₂ (pushField (false::archive) (false::tail))
          (cacheContext records++true::destinationSuffix kind a (copiedTail tail suffix) gap)⟩ :
          MachineState (cachedDoneCap j))) trace
      (blockCfg (seenPhase p memory bit)
        (⟨cachedDonePort j,Tape.mk₂
          (destinationLeft kind (cachedFinish records (false::archive) (bit::tail)) a gap true)
          (PSTRTMIncrement009.blocks (bit::tail)++[false,false]++suffix)⟩ :
          MachineState (cachedDoneCap j))) ∧
      trace.length≤cachedDoneFee j kind records (false::tail).length a.length gap ∧
      ∀ k, visitedSpace (cachedDoneFamily p j kind) inputLength (trace.take k) ≤
        inputLength+2*cachedDoneFee j kind records (false::tail).length a.length gap+1 := by
  obtain ⟨trace,hr,hl⟩ := cached_done_row_bounded (seenPhase p memory bit) j records hj kind archive tail a suffix gap
  rw [seenBit_eq] at hr
  have hb := block_runsFrom (cachedDoneRows p j kind) (cachedDonePorts p j)
    (seenPhase p memory bit) _ _ trace hr rfl
  refine ⟨trace.map (blockCfg (seenPhase p memory bit)),hb,?_,?_⟩
  · simpa only [List.length_map] using hl
  · intro k
    have hs := PSTRTMTrace002.visitedSpace_le (cachedDoneFamily p j kind) inputLength
      ((trace.map (blockCfg (seenPhase p memory bit))).take k)
    have hk : ((trace.map (blockCfg (seenPhase p memory bit))).take k).length≤trace.length := by
      simp only [List.length_take,List.length_map]
      omega
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
