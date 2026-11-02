module
public import Structure.PA17_TM_RatArithmetic_FirstMul_051a
public import Structure.PA17_TM_RatArithmetic_PairInput_050c

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFirstMul051

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticFarLoad031 PA17TMRatArithmeticPairInput050
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticReturnHome037
open PA17TMRatArithmeticWideCache045 PA17TMRatArithmeticNativeCache030
attribute [local implicit_reducible] cycleCap totalStates homeCap firstCap

theorem native_cache_home (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool)
    (newGap value : Nat) :
    Tape.mk₂ (PA17TMRatArithmeticStore019.recordLeft
      (List.replicate newGap false++false::globalSourceLeft sx counter nxTail dxTail nyTail dyTail) value)
      [true]=homeInput sx counter (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail)
        (cacheRecord newGap value) [] [] := by
  rw [globalSourceLeft_footer]
  rfl

/-- The native callee's actual final label is retained until the real
Seq HALT transition transfers into returnHome. Its head is never reset. -/
theorem cycleRow_bounded (fieldA fieldB : SourceField) (memory : Nat) (sx : Bool)
    (counter nxTail dxTail nyTail dyTail : List Bool) (gap a b : Nat)
    (ha : restoredDigits fieldA memory nxTail dxTail nyTail dyTail=
      PA17TMRatArithmeticPairEncode017.payload a)
    (hb : restoredDigits fieldB memory nxTail dxTail nyTail dyTail=
      PA17TMRatArithmeticPairEncode017.payload b)
    (room : window a b-2≤gap) :
    ∃ newGap, 6≤newGap ∧ newGap≤gap+window a b ∧
      BoundedRun (cycleRow fieldA fieldB memory)
        (headerTape sx counter nxTail dxTail nyTail dyTail gap) cycleRowPort
        (cycleOutput sx counter nxTail dxTail nyTail dyTail newGap (a*b))
        (cycleFee fieldA fieldB memory nxTail dxTail nyTail dyTail gap newGap a b) := by
  let archive := false::globalSourceLeft sx counter nxTail dxTail nyTail dyTail
  obtain ⟨newGap,trace,last,run,whole,lower,upper,time,_space⟩ :=
    mul_wide_runsFrom a b gap archive room
  let output := Tape.mk₂
    (PA17TMRatArithmeticStore019.recordLeft (List.replicate newGap false++archive) (a*b)) [true]
  have last_eq : last=⟨last.q,output⟩ := by
    cases last
    simp_all only [output]
  have native : BoundedRun mulCacheMachine
      (nativeInputTape sx counter nxTail dxTail nyTail dyTail gap a b) last.q output
      (65536*(scale a b)^2) := by
    refine ⟨trace,?_,time⟩
    rw [last_eq] at run
    simpa only [mulCacheMachine,nativeInputTape,pairArchive,archive] using run
  have input := pairRow_bounded fieldA fieldB memory sx counter nxTail dxTail nyTail dyTail gap a b ha hb
  have home := returnHome_bounded 0 (cacheRecord newGap (a*b)) [] rfl sx counter
    (false::nxTail) (false::dxTail) (false::nyTail) dyTail []
  have output_eq : output=homeInput sx counter (false::nxTail) (false::dxTail) (false::nyTail)
      (false::dyTail) (cacheRecord newGap (a*b)) [] [] :=
    native_cache_home sx counter nxTail dxTail nyTail dyTail newGap (a*b)
  rw [←output_eq] at home
  have combined : BoundedRun (s:=2078) _ _ _ _ _ :=
    (input.seq (a:=1009) (b:=1016) native).seq (a:=2026) (b:=51) home
  change BoundedRun (s:=2078) (cycleRow fieldA fieldB memory)
    (headerTape sx counter nxTail dxTail nyTail dyTail gap) cycleRowPort
    (cycleOutput sx counter nxTail dxTail nyTail dyTail newGap (a*b)) _ at combined
  refine ⟨newGap,lower,upper,?_⟩
  apply combined.mono
  simp only [cycleFee,totalGap,totalWidth,
    cacheRecord,PSTRTMNatValue017.rawPayload,List.length_ofFn,PA17TMRatArithmeticFarLoad031.bankWidth,
    PA17TMRatArithmeticWidth018.bankWidth,Nat.mul_zero,Nat.add_zero]; omega

theorem cycle_contract (p : Nat) (fieldA fieldB : SourceField) (memory : Fin (p+1)) (sx : Bool)
    (counter nxTail dxTail nyTail dyTail : List Bool) (gap a b : Nat)
    (ha : restoredDigits fieldA memory.val nxTail dxTail nyTail dyTail=
      PA17TMRatArithmeticPairEncode017.payload a)
    (hb : restoredDigits fieldB memory.val nxTail dxTail nyTail dyTail=
      PA17TMRatArithmeticPairEncode017.payload b)
    (room : window a b-2≤gap) :
    ∃ newGap trace, 6≤newGap ∧ newGap≤gap+window a b ∧
      PSTRTMSeq005.RunsFrom (cycleMachine p fieldA fieldB)
        ⟨cycleEntry p memory,headerTape sx counter nxTail dxTail nyTail dyTail gap⟩ trace
        ⟨cyclePort p memory,cycleOutput sx counter nxTail dxTail nyTail dyTail newGap (a*b)⟩ ∧
      trace.length≤cycleFee fieldA fieldB memory.val nxTail dxTail nyTail dyTail gap newGap a b ∧
      ∀ prefixLength chargedL, visitedSpace (cycleMachine p fieldA fieldB) chargedL
        (trace.take prefixLength)≤chargedL+
          2*cycleFee fieldA fieldB memory.val nxTail dxTail nyTail dyTail gap newGap a b+1 := by
  obtain ⟨newGap,lower,upper,trace,hr,hl⟩ :=
    cycleRow_bounded fieldA fieldB memory.val sx counter nxTail dxTail nyTail dyTail gap a b ha hb room
  have hh := block_runsFrom (cycleFamily p fieldA fieldB) (cyclePorts p) memory _ _ _ hr rfl
  refine ⟨newGap,trace.map (blockCfg (s:=2078) memory),lower,upper,?_,?_,?_⟩
  · simpa only [cycleMachine,cycleEntry,cyclePort,blockCfg] using hh
  · simpa only [List.length_map] using hl
  · intro prefixLength chargedL
    have hs := PSTRTMTrace002.visitedSpace_le (cycleMachine p fieldA fieldB) chargedL
      ((trace.map (blockCfg (s:=2078) memory)).take prefixLength)
    have ht : ((trace.map (blockCfg (s:=2078) memory)).take prefixLength).length≤trace.length := by
      simp only [List.length_take,List.length_map]
      omega
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFirstMul051
