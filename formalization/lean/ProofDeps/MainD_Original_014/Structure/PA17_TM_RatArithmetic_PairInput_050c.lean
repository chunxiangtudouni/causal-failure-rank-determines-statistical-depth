module
public import Structure.PA17_TM_RatArithmetic_PairInput_050b

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairInput050

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticFarLoad031 PA17TMRatArithmeticMul047
attribute [local implicit_reducible] pairCap totalStates

/-- A/B are metadata of already-produced fields. Their canonical facts
are later derived from014's actual observations, not given to original code. -/
theorem pairRow_bounded (fieldA fieldB : SourceField) (memory : Nat) (sx : Bool)
    (counter nxTail dxTail nyTail dyTail : List Bool) (gap a b : Nat)
    (ha : restoredDigits fieldA memory nxTail dxTail nyTail dyTail=
      PA17TMRatArithmeticPairEncode017.payload a)
    (hb : restoredDigits fieldB memory nxTail dxTail nyTail dyTail=
      PA17TMRatArithmeticPairEncode017.payload b) :
    BoundedRun (pairRow fieldA fieldB memory) (headerTape sx counter nxTail dxTail nyTail dyTail gap) 1009
      (nativeInputTape sx counter nxTail dxTail nyTail dyTail gap a b)
      (pairFee fieldA fieldB memory nxTail dxTail nyTail dyTail gap a b) := by
  have first := firstRow_bounded fieldA memory sx counter nxTail dxTail nyTail dyTail gap
  rw [ha] at first
  have second := secondRow_bounded fieldB memory sx counter nxTail dxTail nyTail dyTail
    (PA17TMRatArithmeticPairEncode017.payload a) gap
  rw [hb] at second
  let archive := pairArchive sx counter nxTail dxTail nyTail dyTail gap
  have hleft : PA17TMRatArithmeticPairExcursion041.destinationLeft (secondRoute fieldB) gap
      (globalSourceLeft sx counter nxTail dxTail nyTail dyTail)
      (PA17TMRatArithmeticPairEncode017.payload a)=
      false::PA17TMRatArithmeticPairEncode017.aArchive archive a := rfl
  rw [hleft] at second
  have serialize : BoundedRun PA17TMRatArithmeticPairEncode017.plainMachine
      (Tape.mk₂ (false::PA17TMRatArithmeticPairEncode017.aArchive archive a)
        (PA17TMRatArithmeticCopy006.workspace (PA17TMRatArithmeticPairEncode017.payload b))) 47
      (nativeInputTape sx counter nxTail dxTail nyTail dyTail gap a b)
      (64*((PA17TMRatArithmeticPairEncode017.payload a).length+
        (PA17TMRatArithmeticPairEncode017.payload b).length+1)^2) :=
    ⟨PA17TMRatArithmeticPairEncode017.plainTrace archive a b,
      PA17TMRatArithmeticPairEncode017.plain_runsFrom archive a b,
      PA17TMRatArithmeticPairEncode017.pair_time_le false archive a b []⟩
  have combined := (first.seq second).seq serialize
  change BoundedRun (s:=1009) (pairRow fieldA fieldB memory) _ (1009 : Fin 1010) _ _ at combined
  simpa only [pairFee,ha] using combined

theorem pairInput_contract (p : Nat) (fieldA fieldB : SourceField) (memory : Fin (p+1)) (sx : Bool)
    (counter nxTail dxTail nyTail dyTail : List Bool) (gap a b : Nat)
    (ha : restoredDigits fieldA memory.val nxTail dxTail nyTail dyTail=
      PA17TMRatArithmeticPairEncode017.payload a)
    (hb : restoredDigits fieldB memory.val nxTail dxTail nyTail dyTail=
      PA17TMRatArithmeticPairEncode017.payload b) :
    ∃ trace, PSTRTMSeq005.RunsFrom (pairInputMachine p fieldA fieldB)
        ⟨pairEntry p memory,headerTape sx counter nxTail dxTail nyTail dyTail gap⟩ trace
        ⟨pairPort p memory,nativeInputTape sx counter nxTail dxTail nyTail dyTail gap a b⟩ ∧
      trace.length≤pairFee fieldA fieldB memory.val nxTail dxTail nyTail dyTail gap a b ∧
      ∀ prefixLength chargedL, visitedSpace (pairInputMachine p fieldA fieldB) chargedL (trace.take prefixLength)≤
        chargedL+2*pairFee fieldA fieldB memory.val nxTail dxTail nyTail dyTail gap a b+1 := by
  obtain ⟨trace,hr,hl⟩ := pairRow_bounded fieldA fieldB memory.val sx counter nxTail dxTail nyTail dyTail gap a b ha hb
  have hh := block_runsFrom (pairFamily p fieldA fieldB) (pairPorts p) memory _ _ _ hr rfl
  refine ⟨trace.map (blockCfg (s:=1009) memory),?_,?_,?_⟩
  · simpa only [pairInputMachine,pairEntry,pairPort,blockCfg] using hh
  · simpa only [List.length_map] using hl
  · intro prefixLength chargedL
    have hs := PSTRTMTrace002.visitedSpace_le (pairInputMachine p fieldA fieldB) chargedL
      ((trace.map (blockCfg (s:=1009) memory)).take prefixLength)
    have ht : ((trace.map (blockCfg (s:=1009) memory)).take prefixLength).length≤trace.length := by
      simp only [List.length_take,List.length_map]
      omega
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairInput050
