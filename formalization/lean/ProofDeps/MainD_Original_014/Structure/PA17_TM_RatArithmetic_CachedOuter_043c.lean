module
public import Structure.PA17_TM_RatArithmetic_CachedOuter_043b

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedOuter043
open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticCachedPass036 PA17TMRatArithmeticOuter025

def cachedLoopCap (j k : Nat) : Nat := totalStates 1 (cachedPassCap j k+16)
attribute [local implicit_reducible] cachedLoopCap

def cachedLoopMachine (j k : Nat) : Machine (cachedLoopCap j k) := loopMachine (cachedPassMachine j k)

/-- The actual empty-counter HALT port, not a fictitious max-label halt. -/
def cachedLoopPort (j k : Nat) : Fin (cachedLoopCap j k+1) :=
  label (p:=1) (s:=cachedPassCap j k+16) 0
    (padLabel (by omega : 15≤cachedPassCap j k+16) (7 : Fin 16))

theorem cachedLoopPort_value (j k : Nat) : (cachedLoopPort j k).val=7 := by
  simp [cachedLoopPort,label,padLabel]

def loopFee (j k : Nat) (records : List RecordSpec) (width : Nat) : Nat :=
  (width+1)*(2*width+(2*width)*((k*width)*width)+
    (width*((2*k+4)*width+4*k+2*totalGap records+4*totalWidth records+21*j+74)+48)+16)

theorem bodyFee_affine (j k : Nat) (records : List RecordSpec) (width n : Nat) :
    cachedPassFee j k records width n=
      (2*width)*n+(width*((2*k+4)*width+4*k+2*totalGap records+4*totalWidth records+21*j+74)+48) := by
  unfold cachedPassFee
  ring

theorem counted_cost_le (j k : Nat) (records : List RecordSpec) (width : Nat) :
    loopCost (cachedPassFee j k records width) (k*width) width 0≤loopFee j k records width := by
  have fee : cachedPassFee j k records width=
      fun n => (2*width)*n+
        (width*((2*k+4)*width+4*k+2*totalGap records+4*totalWidth records+21*j+74)+48) := by
    funext n
    exact bodyFee_affine j k records width n
  rw [fee]
  simpa only [loopFee,Nat.zero_add] using linear_loopCost_le (2*width)
    (width*((2*k+4)*width+4*k+2*totalGap records+4*totalWidth records+21*j+74)+48)
    (k*width) width 0

/-- This merely instantiates the already-frozen real pop/port loop. No
new counter, iteration fuel or caller count is installed in the program. -/
theorem counted_loop_bounded (j k : Nat) (records : List RecordSpec) (hj : records.length=j)
    (sx : Bool) (nxTail dxTail nyTail dyTail : List Bool) :
    BoundedRun (s:=cachedLoopCap j k) (cachedLoopMachine j k)
      (Tape.mk₂ (false::ROOTTMGCDCounter011.ones (sourceWidth nxTail dxTail nyTail dyTail))
        (prefixRight sx (sourceWord nxTail dxTail nyTail dyTail (cachedTail records 0))))
      (cachedLoopPort j k)
      (Tape.mk₂ [false] (prefixRight sx (sourceWord nxTail dxTail nyTail dyTail
        (cachedTail records (k*(sourceWidth nxTail dxTail nyTail dyTail)^2)))))
      (loopFee j k records (sourceWidth nxTail dxTail nyTail dyTail)) := by
  let width := sourceWidth nxTail dxTail nyTail dyTail
  let bankAt := fun n => sourceWord nxTail dxTail nyTail dyTail (cachedTail records n)
  have bodyRun : ∀ h n, ∃ trace,
      PSTRTMSeq005.RunsFrom (cachedPassMachine j k)
        ⟨0,(popNxFound h sx (bankAt n)).Tape⟩ trace
        ⟨Fin.last (cachedPassCap j k),(popNxInitial h sx (bankAt (n+k*width))).Tape⟩ ∧
        trace.length≤cachedPassFee j k records width n := by
    intro h n
    obtain ⟨trace,hr,hl⟩ := cached_pass_bounded j k records hj sx h n nxTail dxTail nyTail dyTail
    refine ⟨trace,?_,hl⟩
    simpa only [popNxFound,popNxInitial,blockCfg_tape,sevenState,ROOTTMGCDPop016.state,
      prefixLeft,nxContext,listPrefixLeft,bankAt,sourceWord,sourceWidth,width,
      ROOTTMGCDPop016.ones,ROOTTMGCDCounter011.ones,List.cons_append,List.nil_append] using hr
  obtain ⟨trace,hr,hl⟩ := loop_runsFrom (cachedPassMachine j k) sx bankAt (k*width)
    (cachedPassFee j k records width) bodyRun width 0
  have index : 0+(k*width)*width=k*width^2 := by ring
  rw [index] at hr
  have first : loopInitial (cachedPassMachine j k) width sx (bankAt 0)=
      ⟨0,Tape.mk₂ (false::ROOTTMGCDCounter011.ones width) (prefixRight sx (bankAt 0))⟩ := by
    simp [loopInitial,popNxInitial,blockCfg,padCfg,padLabel,label,ROOTTMGCDPop016.state]
  have last : loopFinal (cachedPassMachine j k) sx (bankAt (k*width^2))=
      ⟨cachedLoopPort j k,Tape.mk₂ [false] (prefixRight sx (bankAt (k*width^2)))⟩ := by
    simp [loopFinal,popNxEmpty,cachedLoopPort,blockCfg,padCfg,padLabel,label,ROOTTMGCDPop016.state]
  rw [first,last] at hr
  exact ⟨trace,hr,hl.trans (counted_cost_le j k records width)⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedOuter043
