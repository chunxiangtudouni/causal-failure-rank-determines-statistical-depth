module
public import Structure.PA17_TM_RatArithmetic_PairEncode_017c
public import Structure.PA17_TM_RatArithmetic_Prefix_020b
public import Structure.PA17_TM_RatArithmetic_FinalClean_039c

/-! Real marked-pair/prefix geometry and the common return/cleanup tail.
Sign appears only as the actual existing020 control entry, never code data. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticOutputFinish044

open Turing
open PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticReturnHome037
open PA17TMRatArithmeticFinalClean039
open PA17TMRatArithmeticPrefix020
open PA17TMRatArithmeticAllocate013

def latestLeft (sx : Bool) (nx dxTail ny dyTail : List Bool) (first : RecordSpec)
    (later : List RecordSpec) : List Bool :=
  bankLeft (firstLeft sx [false] nx (false::dxTail) ny (false::dyTail) first) later

def workArchive (gap : Nat) (cacheLeft : List Bool) : List Bool :=
  true::(List.replicate gap false++true::cacheLeft)

def pairInput (gap : Nat) (cacheLeft : List Bool) (u v : Nat) : Tape Bool :=
  Tape.mk₂ (false::PA17TMRatArithmeticPairEncode017.aArchive (workArchive gap cacheLeft) u)
    (PSTRTMIncrement009.blocks (PA17TMRatArithmeticPairEncode017.payload v)++[false,false])

def rawPair (u v : Nat) : List Bool := encodeNat u++encodeNat v++[true]
def physicalWord (negative : Bool) (u v : Nat) : List Bool := prefixWord negative (rawPair u v)
def physicalTail (negative : Bool) (u v : Nat) : List Bool :=
  false::true::true::negative::rawPair u v

def pairOutput (gap : Nat) (cacheLeft : List Bool) (u v : Nat) : Tape Bool :=
  Tape.mk₂ (false::workArchive gap cacheLeft) (rawPair u v)

private theorem padding_three (gap : Nat) (hgap : 3≤gap) (tail : List Bool) :
    List.replicate gap false++tail=false::false::false::(List.replicate (gap-3) false++tail) := by
  have hg : gap=3+(gap-3) := by omega
  calc
    _ = List.replicate (3+(gap-3)) false++tail := by rw [←hg]
    _ = (List.replicate 3 false++List.replicate (gap-3) false)++tail :=
      congrArg (fun bits : List Bool => bits++tail) (List.replicate_add 3 (gap-3) false)
    _ = _ := rfl

def localPrefixTrace (negative : Bool) (gap : Nat) (cacheLeft : List Bool) (u v : Nat) :
    List (MachineState 21) := prefixTrace negative false true false false false
      (List.replicate (gap-3) false++true::cacheLeft) (rawPair u v)

/-- Five real LEFT/WRITEs consume guard, old workanchor and three actual
padding cells. The old workanchor is now INSIDE the output, not an old cache. -/
theorem localPrefix_runsFrom (negative : Bool) (gap : Nat) (hgap : 3≤gap)
    (cacheLeft : List Bool) (u v : Nat) :
    PSTRTMSeq005.RunsFrom prefixMachine
      ⟨prefixLabel negative 0,pairOutput gap cacheLeft u v⟩
      (localPrefixTrace negative gap cacheLeft u v)
      ⟨prefixLabel negative 10,Tape.mk₂ (List.replicate (gap-3) false++true::cacheLeft)
        (physicalWord negative u v)⟩ := by
  have hleft : false::workArchive gap cacheLeft =
      false::true::false::false::false::(List.replicate (gap-3) false++true::cacheLeft) := by
    unfold workArchive
    rw [padding_three gap hgap]
  have hr := prefix_runsFrom negative false true false false false
    (List.replicate (gap-3) false++true::cacheLeft) (rawPair u v)
  rw [←hleft] at hr
  simpa only [prefixState,pairOutput,localPrefixTrace,physicalWord] using hr

def prefixSeekMachine : Machine 23 := PSTRTMSeq005.seqMachine prefixMachine (gapSeekMachine .left)
def prefixSeekEntry (negative : Bool) : Fin 24 :=
  PSTRTMSeq005.leftLabel (b:=1) (prefixLabel negative 0)

def prefixSeekTrace (negative : Bool) (gap : Nat) (cacheLeft : List Bool) (u v : Nat) :
    List (MachineState 23) :=
  (localPrefixTrace negative gap cacheLeft u v).map (PSTRTMSeq005.leftCfg (b:=1)) ++
    (returnGapTrace (gap-3) cacheLeft (physicalTail negative u v)).map (PSTRTMSeq005.rightCfg (a:=21))

def returnedTape (negative : Bool) (gap : Nat) (cacheLeft : List Bool) (u v : Nat) : Tape Bool :=
  Tape.mk₂ cacheLeft (true::(List.replicate (gap-3) false++physicalWord negative u v))

theorem prefixSeek_runsFrom (negative : Bool) (gap : Nat) (hgap : 3≤gap)
    (cacheLeft : List Bool) (u v : Nat) :
    PSTRTMSeq005.RunsFrom prefixSeekMachine
      ⟨prefixSeekEntry negative,pairOutput gap cacheLeft u v⟩
      (prefixSeekTrace negative gap cacheLeft u v)
      ⟨23,returnedTape negative gap cacheLeft u v⟩ := by
  have hp := localPrefix_runsFrom negative gap hgap cacheLeft u v
  have hs := returnGap_runsFrom (gap-3) cacheLeft (physicalTail negative u v)
  have h := PSTRTMSeq005.seq_runsFrom prefixMachine (gapSeekMachine .left)
    ⟨prefixLabel negative 0,pairOutput gap cacheLeft u v⟩
    ⟨prefixLabel negative 10,Tape.mk₂ (List.replicate (gap-3) false++true::cacheLeft) (physicalWord negative u v)⟩
    (seekState 1 cacheLeft (true::(List.replicate (gap-3) false++true::physicalTail negative u v)))
    (localPrefixTrace negative gap cacheLeft u v)
    (returnGapTrace (gap-3) cacheLeft (physicalTail negative u v)) hp hs
  simpa [prefixSeekMachine,prefixSeekEntry,prefixSeekTrace,PSTRTMSeq005.leftCfg,
    PSTRTMSeq005.rightCfg,PSTRTMSeq005.rightLabel,seekState,returnedTape,
    physicalWord,physicalTail,prefixWord] using h

theorem prefixSeekTrace_length (negative : Bool) (gap : Nat) (cacheLeft : List Bool) (u v : Nat) :
    (prefixSeekTrace negative gap cacheLeft u v).length=(gap-3)+13 := by
  unfold prefixSeekTrace localPrefixTrace
  rw [List.length_append,List.length_map,List.length_map,prefix_length,returnGap_length]
  omega

def tailCap (j : Nat) : Nat := 23+finalCap j+1
attribute [local implicit_reducible] tailCap
def tailMachine (j : Nat) : Machine (tailCap j) := PSTRTMSeq005.seqMachine prefixSeekMachine (finalCleanMachine j)
def tailEntry (j : Nat) (negative : Bool) : Fin (tailCap j+1) :=
  PSTRTMSeq005.leftLabel (b:=finalCap j) (prefixSeekEntry negative)
def tailPort (j : Nat) : Fin (tailCap j+1) := PSTRTMSeq005.rightLabel (a:=23) (finalPort j)

def tailFee (j : Nat) (first : RecordSpec) (later : List RecordSpec) (nx dxTail ny dyTail : List Bool)
    (gap : Nat) : Nat :=
  4*cacheGap first later+14*cacheWidth first later+54*j+10*sourceWidth nx dxTail ny dyTail+2*gap+164

/-- The actual existing020 entry0/11 is retained through the two Seq
embeddings. It is not replaced with initial0 for the negative path. -/
theorem tail_bounded (j : Nat) (negative : Bool) (first : RecordSpec) (later : List RecordSpec)
    (hj : later.length=j) (sx : Bool) (nx dxTail ny dyTail : List Bool)
    (gap : Nat) (hgap : 3≤gap) (u v : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (tailMachine j)
        ⟨tailEntry j negative,pairOutput gap (latestLeft sx nx dxTail ny dyTail first later) u v⟩ trace
        ⟨tailPort j,Tape.mk₁ (physicalWord negative u v)⟩ ∧
      trace.length≤tailFee j first later nx dxTail ny dyTail gap := by
  let cacheLeft := latestLeft sx nx dxTail ny dyTail first later
  obtain ⟨tc,hc,hlc⟩ := finalClean_bounded j first later hj sx nx dxTail ny dyTail (gap-3) (physicalTail negative u v)
  have hp := prefixSeek_runsFrom negative gap hgap cacheLeft u v
  have h := PSTRTMSeq005.seq_runsFrom prefixSeekMachine (finalCleanMachine j)
    ⟨prefixSeekEntry negative,pairOutput gap cacheLeft u v⟩
    ⟨23,returnedTape negative gap cacheLeft u v⟩
    ⟨finalPort j,Tape.mk₁ (physicalWord negative u v)⟩
    (prefixSeekTrace negative gap cacheLeft u v) tc hp hc
  refine ⟨(prefixSeekTrace negative gap cacheLeft u v).map (PSTRTMSeq005.leftCfg (b:=finalCap j)) ++
    tc.map (PSTRTMSeq005.rightCfg (a:=23)),?_,?_⟩
  · simpa only [tailMachine,tailEntry,tailPort,PSTRTMSeq005.leftCfg,PSTRTMSeq005.rightCfg] using h
  · rw [List.length_append,List.length_map,List.length_map,prefixSeekTrace_length]
    dsimp [tailFee]
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticOutputFinish044
