module
public import Structure.PA17_TM_RatArithmetic_NativeRecord_022b
public import Structure.PA17_TM_RatArithmetic_FrameBudget_008b

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticNativeRecord022

open Turing PA17TMRatArithmeticFrameBudget008

/-- One concrete fixed native multiplication followed by genuine caching.
This entry requires its displayed physical reserve, not a supplied budget. -/
def mulRecordMachine : Machine 1016 := recordMachine PSTRTMNativeMul112.nativeMulMachine

theorem mul_record_runsFrom (a b : Nat) (archive : List Bool) :
    ∃ (left right : Nat) (trace : List (MachineState 1016)) (last : MachineState 1016),
      PSTRTMSeq005.RunsFrom mulRecordMachine
        ⟨0,Tape.mk₂ (false::true::(List.replicate (mulWindow a b-2) false++archive))
          (encodeNat a++encodeNat b)⟩ trace last ∧
      last.Tape=Tape.mk₂
        (PA17TMRatArithmeticStore019.recordLeft (List.replicate (left-2) false++archive) (a*b)) [true] ∧
      8*mulScale a b≤left ∧ 8*mulScale a b≤right ∧ left+right=2*mulWindow a b ∧
      trace.length≤32768*(mulScale a b)^2 ∧
      ∀ prefixLength inputLength,
        visitedSpace mulRecordMachine inputLength (trace.take prefixLength) ≤
          inputLength+65536*(mulScale a b)^2+1 := by
  have hs : 1≤mulScale a b := by unfold mulScale;omega
  obtain ⟨left,right,trace,last,hrun,htape,hl,hr,hsum,htime,hspace⟩ :=
    record_runsFrom PSTRTMNativeMul112.nativeMulMachine (encodeNat a++encodeNat b)
      (PSTRTMNativeMul112.nativeTrace a b) (PSTRTMNativeMul112.nativeFinal a b)
      (a*b) (16384*(mulScale a b)^2) (8*mulScale a b)
      (PSTRTMNativeMul112.native_runs a b) (PSTRTMNativeMul112.native_final_tape_canonical a b)
      (PSTRTMNativeMul112.native_length_le a b) (mul_input_length a b) (mul_output_length a b)
      (by omega) archive
  have hbits : natBits (a*b)+1≤4*mulScale a b := by
    have hp := mul_output_length a b
    rw [PSTRTMLength004.encodeNat_length] at hp
    omega
  have hsq0 : (natBits (a*b)+1)^2≤(4*mulScale a b)^2 := by
    simpa only [pow_two] using Nat.mul_le_mul hbits hbits
  have hsq : (natBits (a*b)+1)^2≤16*(mulScale a b)^2 := by
    have he : (4*mulScale a b)^2=16*(mulScale a b)^2 := by ring
    simpa only [he] using hsq0
  have hsquare : 1≤(mulScale a b)^2 := by
    simpa only [pow_two,one_mul] using Nat.mul_le_mul hs hs
  have hcost : 16384*(mulScale a b)^2+32*(natBits (a*b)+1)^2+6≤32768*(mulScale a b)^2 := by
    omega
  refine ⟨left,right,trace,last,?_,htape,hl,hr,?_,?_,?_⟩
  · simpa only [mulRecordMachine,mulWindow,record_first_zero] using hrun
  · simpa only [mulWindow] using hsum
  · omega
  · intro prefixLength inputLength
    have hsp := hspace prefixLength inputLength
    change visitedSpace (recordMachine PSTRTMNativeMul112.nativeMulMachine) inputLength
      (trace.take prefixLength) ≤ inputLength+65536*(mulScale a b)^2+1
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticNativeRecord022
