module
public import Structure.PA17_TM_RatArithmetic_NativeTail_055a

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticNativeTail055

open Turing PA17TMRatArithmeticWidth018 PA17TMRatArithmeticNativeRecord022
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticReturnHome037
open PA17TMRatArithmeticWideCache045 PA17TMRatArithmeticNativeCache030
attribute [local implicit_reducible] tailCap nativeRecordCap

/-- Composition consumes a real native run, keeps its actual final label,
then pays the actual transition and return over every old cache record. -/
theorem nativeTail_bounded {states : Nat} (native : Machine states) (j : Nat)
    (first : RecordSpec) (later : List RecordSpec) (hj : later.length=j)
    (sx : Bool) (counter nx dx ny dyTail : List Bool) (gap a b value : Nat)
    (actual : WideCacheResult native a b value
      (true::lastArchive sx counter nx dx ny (false::dyTail) first later) gap) :
    ∃ newGap, 6≤newGap ∧ newGap≤gap+window a b ∧
      BoundedRun (nativeTailMachine native j)
        (tailInput sx counter nx dx ny (false::dyTail) first later gap a b) (tailPort states j)
        (tailOutput sx counter nx dx ny (false::dyTail) first later newGap value)
        (tailFee j first later nx dx ny (false::dyTail) newGap a b value) := by
  obtain ⟨newGap,trace,last,run,whole,lower,upper,time,_space⟩ := actual
  let output := Tape.mk₂ (PA17TMRatArithmeticStore019.recordLeft
    (List.replicate newGap false++true::lastArchive sx counter nx dx ny (false::dyTail) first later) value) [true]
  have last_eq : last=⟨last.q,output⟩ := by cases last;simp_all only [output]
  have call : BoundedRun (recordMachine native)
      (tailInput sx counter nx dx ny (false::dyTail) first later gap a b) last.q output
      (65536*(scale a b)^2) := by
    rw [last_eq] at run
    exact ⟨trace,run,time⟩
  have hlen : (later++[resultRecord newGap value]).length=j+1 := by
    simp only [List.length_append,List.length_singleton,hj]
  have home := returnHome_bounded (j+1) first (later++[resultRecord newGap value]) hlen
    sx counter nx dx ny dyTail []
  have output_eq : output=homeInput sx counter nx dx ny (false::dyTail) first
      (later++[resultRecord newGap value]) [] :=
    newRecord_home sx counter nx dx ny (false::dyTail) first later newGap value
  rw [←output_eq] at home
  have combined : BoundedRun (s:=tailCap states j) _ _ _ _ _ := call.seq home
  change BoundedRun (s:=tailCap states j) (nativeTailMachine native j)
    (tailInput sx counter nx dx ny (false::dyTail) first later gap a b) (tailPort states j)
    (tailOutput sx counter nx dx ny (false::dyTail) first later newGap value) _ at combined
  refine ⟨newGap,lower,upper,?_⟩
  apply combined.mono
  simp only [tailFee,totalGap,totalWidth,
    totalGap_append,totalWidth_append,resultRecord,PSTRTMNatValue017.rawPayload,
    List.length_ofFn,Nat.add_zero,Nat.add_assoc]; omega

theorem mulTail_bounded (j : Nat) (first : RecordSpec) (later : List RecordSpec) (hj : later.length=j)
    (sx : Bool) (counter nx dx ny dyTail : List Bool) (gap a b : Nat) (room : window a b-2≤gap) :
    ∃ newGap, 6≤newGap ∧ newGap≤gap+window a b ∧
      BoundedRun (nativeTailMachine PSTRTMNativeMul112.nativeMulMachine j)
        (tailInput sx counter nx dx ny (false::dyTail) first later gap a b) (tailPort 982 j)
        (tailOutput sx counter nx dx ny (false::dyTail) first later newGap (a*b))
        (tailFee j first later nx dx ny (false::dyTail) newGap a b (a*b)) :=
  nativeTail_bounded _ j first later hj sx counter nx dx ny dyTail gap a b (a*b)
    (mul_wide_runsFrom a b gap _ room)

theorem gcdTail_bounded (j : Nat) (first : RecordSpec) (later : List RecordSpec) (hj : later.length=j)
    (sx : Bool) (counter nx dx ny dyTail : List Bool) (gap a b : Nat) (room : window a b-2≤gap) :
    ∃ newGap, 6≤newGap ∧ newGap≤gap+window a b ∧
      BoundedRun (nativeTailMachine ROOTTMGCDDispatch018.nativeGcdMachine j)
        (tailInput sx counter nx dx ny (false::dyTail) first later gap a b) (tailPort 3564 j)
        (tailOutput sx counter nx dx ny (false::dyTail) first later newGap (Nat.gcd a b))
        (tailFee j first later nx dx ny (false::dyTail) newGap a b (Nat.gcd a b)) :=
  nativeTail_bounded _ j first later hj sx counter nx dx ny dyTail gap a b (Nat.gcd a b)
    (gcd_wide_runsFrom a b gap _ room)

theorem quotientTail_bounded (j : Nat) (first : RecordSpec) (later : List RecordSpec) (hj : later.length=j)
    (sx : Bool) (counter nx dx ny dyTail : List Bool) (gap a b : Nat) (room : window a b-2≤gap) :
    ∃ newGap, 6≤newGap ∧ newGap≤gap+window a b ∧
      BoundedRun (nativeTailMachine PA17TMDivisionFull012.quotientMachine j)
        (tailInput sx counter nx dx ny (false::dyTail) first later gap a b) (tailPort 1136 j)
        (tailOutput sx counter nx dx ny (false::dyTail) first later newGap (a/b))
        (tailFee j first later nx dx ny (false::dyTail) newGap a b (a/b)) :=
  nativeTail_bounded _ j first later hj sx counter nx dx ny dyTail gap a b (a/b)
    (quotient_wide_runsFrom a b gap _ room)

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticNativeTail055
