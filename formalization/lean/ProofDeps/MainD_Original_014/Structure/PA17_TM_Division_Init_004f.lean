module
public import Structure.PA17_TM_Division_Init_004e

@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2400000
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionInit004
open PSTRTMBinaryAdd024
open PSTRTMCompareCode054 (leftColumns)

def residentHigh (pairs : List (Bool × Bool)) : List (Bool × Bool) := residentPairs pairs ++ [(false,false)]

def prefixTrace (pairs : List (Bool × Bool)) : List (MachineState 66) :=
  splice (splice (copyLoopTrace pairs.reverse []) (triggerTrace (archiveLeft pairs) (markerTail pairs)))
    (cleanupTrace (sep (archiveLeft pairs)) pairs)

def prefixFinal (pairs : List (Bool × Bool)) : MachineState 66 :=
  state 66 (leftColumns (residentHigh pairs).reverse ++ sep (archiveLeft pairs)) []

theorem prefix_segment (pairs : List (Bool × Bool)) :
    Segment (copyState pairs.reverse []) (prefixTrace pairs) (prefixFinal pairs) := by
  have hc : Segment (copyState pairs.reverse []) (copyLoopTrace pairs.reverse []) (copyState [] pairs) := by
    simpa only [List.reverse_reverse,List.append_nil] using copyLoop_segment pairs.reverse []
  have ht : Segment (copyState [] pairs) (triggerTrace (archiveLeft pairs) (markerTail pairs))
      (state 60 (sep (archiveLeft pairs)) (markedColumns pairs ++ [false,false])) := by
    simpa only [copyState,residentWord,List.reverse_nil,operandColumns,List.flatMap_nil,List.nil_append,marked_decompose] using
      trigger_segment (archiveLeft pairs) (markerTail pairs)
  exact segment_splice (segment_splice hc ht) (cleanup_segment (sep (archiveLeft pairs)) pairs)

theorem prefix_runsFrom (pairs : List (Bool × Bool)) :
    PSTRTMSeq005.RunsFrom prefixMachine (copyState pairs.reverse []) (prefixTrace pairs) (prefixFinal pairs) :=
  ⟨(prefix_segment pairs).1,(prefix_segment pairs).2.1,(prefix_segment pairs).2.2,prefix_halt _ _⟩

theorem prefix_length_le (pairs : List (Bool × Bool)) :
    (prefixTrace pairs).length ≤ 8*pairs.length^2+42*pairs.length+13 := by
  have h1 := splice_length_le (copyLoopTrace pairs.reverse []) (triggerTrace (archiveLeft pairs) (markerTail pairs))
  have h2 := splice_length_le
    (splice (copyLoopTrace pairs.reverse []) (triggerTrace (archiveLeft pairs) (markerTail pairs)))
    (cleanupTrace (sep (archiveLeft pairs)) pairs)
  have hc := copyLoop_length_le pairs.reverse []
  simp only [List.length_reverse,List.length_nil,Nat.add_zero] at hc
  rw [trigger_length] at h1
  rw [cleanup_length] at h2
  change (prefixTrace pairs).length ≤ _ at h2
  nlinarith

def initMachine : Machine 72 := PSTRTMSeq005.seqMachine prefixMachine PSTRTMColumnRewind067.rewindMachine

def initTrace (pairs : List (Bool × Bool)) : List (MachineState 72) :=
  (prefixTrace pairs).map (PSTRTMSeq005.leftCfg (b := 5)) ++
    (PSTRTMColumnRewind067.fullTrace (false::false::archiveLeft pairs) (residentHigh pairs).reverse []).map
      (PSTRTMSeq005.rightCfg (a := 66))

def initInitial (pairs : List (Bool × Bool)) : MachineState 72 := PSTRTMSeq005.leftCfg (b := 5) (copyState pairs.reverse [])
def initFinal (pairs : List (Bool × Bool)) : MachineState 72 :=
  PSTRTMSeq005.rightCfg (a := 66) (PSTRTMColumnRewind067.state 5 (sep (archiveLeft pairs)) (operandColumns (residentHigh pairs)))

/-- All archive/zeroing/restore/allocation movements and the final real rewind
occur on the SAME whole tape, including the real head-preserving transfer. -/
theorem init_retained_runsFrom (pairs : List (Bool × Bool)) :
    PSTRTMSeq005.RunsFrom initMachine (initInitial pairs) (initTrace pairs) (initFinal pairs) := by
  apply PSTRTMSeq005.seq_runsFrom prefixMachine PSTRTMColumnRewind067.rewindMachine
    (copyState pairs.reverse []) (prefixFinal pairs)
    (PSTRTMColumnRewind067.state 5 (sep (archiveLeft pairs)) (operandColumns (residentHigh pairs)))
    (prefixTrace pairs)
    (PSTRTMColumnRewind067.fullTrace (false::false::archiveLeft pairs) (residentHigh pairs).reverse [])
  · exact prefix_runsFrom pairs
  · simpa only [prefixFinal,sep,List.append_nil,state,PSTRTMColumnRewind067.state] using
      PSTRTMColumnRewind067.rewind_runsFrom (false::false::archiveLeft pairs) (residentHigh pairs) []

theorem residentHigh_length (pairs : List (Bool × Bool)) : (residentHigh pairs).length = pairs.length+1 := by
  simp only [residentHigh,residentPairs,List.length_append,List.length_map,List.length_singleton]

theorem init_length_le (pairs : List (Bool × Bool)) :
    (initTrace pairs).length ≤ 64*(pairs.length+1)^2 := by
  have hp := prefix_length_le pairs
  simp only [initTrace,List.length_append,List.length_map,PSTRTMColumnRewind067.full_length,
    List.length_reverse,residentHigh_length]
  nlinarith

theorem init_visitedSpace_le (pairs : List (Bool × Bool)) :
    visitedSpace initMachine (operandColumns pairs).length (initTrace pairs) ≤ 256*(pairs.length+1)^2 := by
  have hs := PSTRTMTrace002.visitedSpace_le initMachine (operandColumns pairs).length (initTrace pairs)
  have ht := init_length_le pairs
  rw [operandColumns_length] at hs ⊢
  nlinarith

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionInit004
