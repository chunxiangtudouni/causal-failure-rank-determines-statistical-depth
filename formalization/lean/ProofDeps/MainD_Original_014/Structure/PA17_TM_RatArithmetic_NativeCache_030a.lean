module
public import Structure.PA17_TM_RatArithmetic_NativeRecord_022c
public import Structure.PA17_TM_RatArithmetic_Sub_016f
public import Structure.PA17_TM_RatArithmetic_GCDCall_010a

/-! Close every native arithmetic-to-cache call needed by the fixed rational
call graph. Every public operation below has a fixed actual machine before
all a,b, including zero. The common physical window is an entry contract,
whose dynamic producer remains the allocator rather than an original input.
No new arithmetic kernel or abstract runtime oracle is introduced. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticNativeCache030

open Turing PA17TMRatArithmeticNativeRecord022

def scale (a b : Nat) : Nat := natBits a+natBits b+1

def window (a b : Nat) : Nat := 32768*(scale a b)^2+8*scale a b

/-- A notation for the WHOLE actual cached run, not a field in the machine
and never an assumed original scalar result. The following five theorems
prove it from existing closed ordinary native machines. -/
def CacheResult {states : Nat} (machine : Machine states) (a b result : Nat)
    (archive : List Bool) : Prop :=
  ∃ (left right : Nat) (trace : List (MachineState (5+(states+27+1)+1)))
      (last : MachineState (5+(states+27+1)+1)),
    PSTRTMSeq005.RunsFrom (recordMachine machine)
      ⟨0,Tape.mk₂ (false::true::(List.replicate (window a b-2) false++archive))
        (encodeNat a++encodeNat b)⟩ trace last ∧
    last.Tape=Tape.mk₂
      (PA17TMRatArithmeticStore019.recordLeft (List.replicate (left-2) false++archive) result) [true] ∧
    8*scale a b≤left ∧ 8*scale a b≤right ∧ left+right=2*window a b ∧
    trace.length≤65536*(scale a b)^2 ∧
    ∀ prefixLength inputLength,
      visitedSpace (recordMachine machine) inputLength (trace.take prefixLength) ≤
        inputLength+131072*(scale a b)^2+1

private theorem cache_of_native {states : Nat} (machine : Machine states)
    (a b result : Nat) (archive : List Bool) (original : List (MachineState states))
    (final : MachineState states) (run : Runs machine (encodeNat a++encodeNat b) original final)
    (whole : final.Tape=Tape.mk₁ (encodeNat result))
    (timeBound : original.length≤32768*(scale a b)^2)
    (bitsBound : natBits result≤2*scale a b) : CacheResult machine a b result archive := by
  have hs : 1≤scale a b := by unfold scale;omega
  have hi : (encodeNat a++encodeNat b).length≤8*scale a b := by
    simp only [List.length_append,PSTRTMLength004.encodeNat_length,scale]
    omega
  have ho : (encodeNat result).length≤8*scale a b := by
    rw [PSTRTMLength004.encodeNat_length]
    omega
  obtain ⟨left,right,trace,last,hrun,htape,hl,hr,hsum,htime,hspace⟩ :=
    record_runsFrom machine (encodeNat a++encodeNat b) original final result
      (32768*(scale a b)^2) (8*scale a b) run whole timeBound hi ho (by omega) archive
  have hbits : natBits result+1≤4*scale a b := by omega
  have hsq0 : (natBits result+1)^2≤(4*scale a b)^2 := by
    simpa only [pow_two] using Nat.mul_le_mul hbits hbits
  have hsq : (natBits result+1)^2≤16*(scale a b)^2 := by
    have he : (4*scale a b)^2=16*(scale a b)^2 := by ring
    simpa only [he] using hsq0
  have hsquare : 1≤(scale a b)^2 := by
    simpa only [pow_two,one_mul] using Nat.mul_le_mul hs hs
  have hcost : 32768*(scale a b)^2+32*(natBits result+1)^2+6≤65536*(scale a b)^2 := by
    omega
  refine ⟨left,right,trace,last,?_,htape,hl,hr,?_,?_,?_⟩
  · simpa only [window,record_first_zero] using hrun
  · simpa only [window] using hsum
  · omega
  · intro prefixLength inputLength
    have hsp := hspace prefixLength inputLength
    omega

def addCacheMachine : Machine 503 := recordMachine PSTRTMNativeAdd053.nativeAddMachine
def subCacheMachine : Machine 630 := recordMachine PA17TMRatArithmeticSub016.nativeSubMachine
def mulCacheMachine : Machine 1016 := recordMachine PSTRTMNativeMul112.nativeMulMachine
def gcdCacheMachine : Machine 3598 := recordMachine ROOTTMGCDDispatch018.nativeGcdMachine
def quotientCacheMachine : Machine 1170 := recordMachine PA17TMDivisionFull012.quotientMachine

theorem add_record_runsFrom (a b : Nat) (archive : List Bool) :
    CacheResult PSTRTMNativeAdd053.nativeAddMachine a b (a+b) archive := by
  apply cache_of_native PSTRTMNativeAdd053.nativeAddMachine a b (a+b) archive
    (PSTRTMNativeAdd053.nativeTrace a b) (PSTRTMNativeAdd053.nativeFinal a b)
    (PSTRTMNativeAdd053.native_runs a b) (PSTRTMNativeAdd053.native_final_tape_canonical a b)
  · have ht := PSTRTMNativeAdd053.native_length_le a b
    change (PSTRTMNativeAdd053.nativeTrace a b).length≤32768*(natBits a+natBits b+1)^2
    omega
  · have hb := PSTRTMArithmetic008.natBits_add_le a b
    unfold scale
    omega

theorem sub_record_runsFrom (a b : Nat) (archive : List Bool) :
    CacheResult PA17TMRatArithmeticSub016.nativeSubMachine a b (a-b) archive := by
  apply cache_of_native PA17TMRatArithmeticSub016.nativeSubMachine a b (a-b) archive
    (PA17TMRatArithmeticSub016.nativeTrace a b) (PA17TMRatArithmeticSub016.nativeFinal a b)
    (PA17TMRatArithmeticSub016.native_runs a b) (PA17TMRatArithmeticSub016.native_final_tape a b)
  · have ht := PA17TMRatArithmeticSub016.native_length_le a b
    change (PA17TMRatArithmeticSub016.nativeTrace a b).length≤32768*(natBits a+natBits b+1)^2
    omega
  · have hb := PSTRTMArithmetic008.natBits_mono (Nat.sub_le a b)
    unfold scale
    omega

theorem mul_record_runsFrom (a b : Nat) (archive : List Bool) :
    CacheResult PSTRTMNativeMul112.nativeMulMachine a b (a*b) archive := by
  apply cache_of_native PSTRTMNativeMul112.nativeMulMachine a b (a*b) archive
    (PSTRTMNativeMul112.nativeTrace a b) (PSTRTMNativeMul112.nativeFinal a b)
    (PSTRTMNativeMul112.native_runs a b) (PSTRTMNativeMul112.native_final_tape_canonical a b)
  · have ht := PSTRTMNativeMul112.native_length_le a b
    change (PSTRTMNativeMul112.nativeTrace a b).length≤32768*(natBits a+natBits b+1)^2
    omega
  · have hb := PSTRTMNativeMul112.product_payload_length_le a b
    simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn] at hb
    unfold scale
    omega

theorem gcd_record_runsFrom (a b : Nat) (archive : List Bool) :
    CacheResult ROOTTMGCDDispatch018.nativeGcdMachine a b (Nat.gcd a b) archive := by
  apply cache_of_native ROOTTMGCDDispatch018.nativeGcdMachine a b (Nat.gcd a b) archive
    (ROOTTMGCDNative037.nativeTrace a b) (ROOTTMGCDNative037.nativeFinal a b)
    (ROOTTMGCDNative037.native_runs a b) (ROOTTMGCDNative037.native_final_tape a b)
  · have ht := ROOTTMGCDNative037.native_length_le a b
    change (ROOTTMGCDNative037.nativeTrace a b).length≤32768*(natBits a+natBits b+1)^2
    omega
  · have hb := PA17TMRatArithmeticGCDCall010.gcd_bits_le_sum a b
    unfold scale
    omega

theorem quotient_record_runsFrom (a b : Nat) (archive : List Bool) :
    CacheResult PA17TMDivisionFull012.quotientMachine a b (a/b) archive := by
  obtain ⟨trace,final,run,whole,timeBound,_⟩ :=
    (PA17TMRatArithmeticNatDivCall011.div_mod_whole_runs a b).1
  apply cache_of_native PA17TMDivisionFull012.quotientMachine a b (a/b) archive
    trace final run whole timeBound
  have hb := PSTRTMArithmetic008.natBits_mono (Nat.div_le_self a b)
  unfold scale
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticNativeCache030
