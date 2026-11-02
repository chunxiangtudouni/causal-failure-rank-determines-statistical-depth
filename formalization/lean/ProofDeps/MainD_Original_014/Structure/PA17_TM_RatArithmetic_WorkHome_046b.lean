module
public import Structure.PA17_TM_RatArithmetic_WorkHome_046a

/-! With at least one previous cache, the unfinished A workspace is after
a real TRUE cache end. Reuse the frozen return-to-boundary and full cache
return programs, preserving the entire A workspace as arbitrary suffix. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWorkHome046

open Turing PA17TMRatArithmeticWidth018 PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticReturnHome037

def withCacheCap (j : Nat) : Nat := 4+homeCap j+1

def withCacheMachine (j : Nat) : Machine (withCacheCap j) :=
  PSTRTMSeq005.seqMachine (a:=4) (b:=homeCap j)
    PA17TMRatArithmeticFarLoad031.backFromDataMachine (returnHomeMachine j)

def withCachePort (j : Nat) : Fin (withCacheCap j+1) :=
  PSTRTMSeq005.rightLabel (a:=4) (homePort j)

def cachedWorkInput (sx : Bool) (counter nx dx ny dy : List Bool)
    (first : RecordSpec) (later : List RecordSpec) (gap : Nat) (word : List Bool) : Tape Bool :=
  Tape.mk₂
    (false::true::(List.replicate gap false++true::bankLeft (firstLeft sx counter nx dx ny dy first) later)) word

theorem with_cache_work_home_bounded (j : Nat) (first : RecordSpec) (later : List RecordSpec)
    (hj : later.length=j) (sx : Bool) (counter nx dx ny dyTail : List Bool) (gap : Nat) (word : List Bool) :
    BoundedRun (withCacheMachine j)
      (cachedWorkInput sx counter nx dx ny (false::dyTail) first later gap word) (withCachePort j)
      (homeOutput sx counter nx dx ny (false::dyTail) first later
        (List.replicate gap false++true::false::word))
      (gap+totalGap (first::later)+2*totalWidth (first::later)+12*j+
        2*bankWidth nx dx ny (false::dyTail)+54) := by
  let archive := bankLeft (firstLeft sx counter nx dx ny (false::dyTail) first) later
  have hb := PA17TMRatArithmeticFarLoad031.backFromData_bounded gap archive word
  change BoundedRun PA17TMRatArithmeticFarLoad031.backFromDataMachine
    (cachedWorkInput sx counter nx dx ny (false::dyTail) first later gap word) 4
    (homeInput sx counter nx dx ny (false::dyTail) first later
      (List.replicate gap false++true::false::word)) (gap+5) at hb
  have hr := returnHome_bounded j first later hj sx counter nx dx ny dyTail
    (List.replicate gap false++true::false::word)
  have combined := hb.seq hr
  have cost : (gap+5)+(totalGap (first::later)+2*totalWidth (first::later)+12*j+
      2*bankWidth nx dx ny (false::dyTail)+49) ≤
      gap+totalGap (first::later)+2*totalWidth (first::later)+12*j+
      2*bankWidth nx dx ny (false::dyTail)+54 := by omega
  simpa only [withCacheMachine,withCachePort,withCacheCap] using combined.mono cost

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWorkHome046
