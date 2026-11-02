module
public import Structure.PA17_TM_RatArithmetic_NativeCache_030a

/-! A genuinely allocated gap may exceed a native callee's proved window.
Split that SAME zero tape; retain the surplus in the untouched archive.
No shift, head reset, input-dependent code or supplied arithmetic answer. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWideCache045

open Turing PA17TMRatArithmeticNativeCache030 PA17TMRatArithmeticNativeRecord022

def WideCacheResult {states : Nat} (machine : Machine states) (a b result : Nat)
    (archive : List Bool) (gap : Nat) : Prop :=
  ∃ (newGap : Nat) (trace : List (MachineState (5+(states+27+1)+1)))
      (last : MachineState (5+(states+27+1)+1)),
    PSTRTMSeq005.RunsFrom (recordMachine machine)
      ⟨0,Tape.mk₂ (false::true::(List.replicate gap false++archive))
        (encodeNat a++encodeNat b)⟩ trace last ∧
    last.Tape=Tape.mk₂
      (PA17TMRatArithmeticStore019.recordLeft (List.replicate newGap false++archive) result) [true] ∧
    6≤newGap ∧ newGap≤gap+window a b ∧
    trace.length≤65536*(scale a b)^2 ∧ ∀ prefixLength inputLength,
      visitedSpace (recordMachine machine) inputLength (trace.take prefixLength) ≤
        inputLength+131072*(scale a b)^2+1

private theorem widen_actual_cache {states : Nat} (machine : Machine states)
    (a b result : Nat) (archive : List Bool) (gap : Nat)
    (room : window a b-2≤gap)
    (actual : CacheResult machine a b result
      (List.replicate (gap-(window a b-2)) false++archive)) :
    WideCacheResult machine a b result archive gap := by
  let spare := gap-(window a b-2)
  obtain ⟨left,right,trace,last,hrun,htape,hl,hr,hsum,htime,hspace⟩ := actual
  have hs : 1≤scale a b := by unfold scale;omega
  have hw : 8≤window a b := by unfold window;omega
  have hleft : 8≤left := by omega
  have split_length : (window a b-2)+spare=gap := by dsimp [spare];omega
  have initial_zeros : List.replicate (window a b-2) false++
      (List.replicate spare false++archive)=List.replicate gap false++archive := by
    rw [←List.append_assoc,←List.replicate_add,split_length]
  let newGap := left-2+spare
  have output_zeros : List.replicate (left-2) false++
      (List.replicate spare false++archive)=List.replicate newGap false++archive := by
    rw [←List.append_assoc,←List.replicate_add]
  have lower : 6≤newGap := by dsimp [newGap];omega
  have upper : newGap≤gap+window a b := by dsimp [newGap,spare];omega
  refine ⟨newGap,trace,last,?_,?_,lower,upper,htime,hspace⟩
  · change PSTRTMSeq005.RunsFrom (recordMachine machine)
      ⟨0,Tape.mk₂ (false::true::(List.replicate (window a b-2) false++
        (List.replicate spare false++archive))) (encodeNat a++encodeNat b)⟩ trace last at hrun
    simpa only [initial_zeros] using hrun
  · change last.Tape=Tape.mk₂
      (PA17TMRatArithmeticStore019.recordLeft
        (List.replicate (left-2) false++(List.replicate spare false++archive)) result) [true] at htape
    simpa only [output_zeros] using htape

theorem add_wide_runsFrom (a b gap : Nat) (archive : List Bool) (room : window a b-2≤gap) :
    WideCacheResult PSTRTMNativeAdd053.nativeAddMachine a b (a+b) archive gap :=
  widen_actual_cache _ a b (a+b) archive gap room
    (add_record_runsFrom a b (List.replicate (gap-(window a b-2)) false++archive))

theorem sub_wide_runsFrom (a b gap : Nat) (archive : List Bool) (room : window a b-2≤gap) :
    WideCacheResult PA17TMRatArithmeticSub016.nativeSubMachine a b (a-b) archive gap :=
  widen_actual_cache _ a b (a-b) archive gap room
    (sub_record_runsFrom a b (List.replicate (gap-(window a b-2)) false++archive))

theorem mul_wide_runsFrom (a b gap : Nat) (archive : List Bool) (room : window a b-2≤gap) :
    WideCacheResult PSTRTMNativeMul112.nativeMulMachine a b (a*b) archive gap :=
  widen_actual_cache _ a b (a*b) archive gap room
    (mul_record_runsFrom a b (List.replicate (gap-(window a b-2)) false++archive))

theorem gcd_wide_runsFrom (a b gap : Nat) (archive : List Bool) (room : window a b-2≤gap) :
    WideCacheResult ROOTTMGCDDispatch018.nativeGcdMachine a b (Nat.gcd a b) archive gap :=
  widen_actual_cache _ a b (Nat.gcd a b) archive gap room
    (gcd_record_runsFrom a b (List.replicate (gap-(window a b-2)) false++archive))

theorem quotient_wide_runsFrom (a b gap : Nat) (archive : List Bool) (room : window a b-2≤gap) :
    WideCacheResult PA17TMDivisionFull012.quotientMachine a b (a/b) archive gap :=
  widen_actual_cache _ a b (a/b) archive gap room
    (quotient_record_runsFrom a b (List.replicate (gap-(window a b-2)) false++archive))

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWideCache045
