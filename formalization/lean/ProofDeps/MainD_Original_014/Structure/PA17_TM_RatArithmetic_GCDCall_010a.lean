module
public import Common.ROOT_TM_GCD_Native_037
public import Structure.PA17_TM_RatArithmetic_FrameBudget_008a
public import Structure.PA17_TM_RatArithmetic_Size_007d

/-! The SAME fixed native gcd runs in a real owned finite window. The two
outside frames are arbitrary and remain at their physical boundaries. The
producer of the displayed blank padding is separate, actual charged code. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticGCDCall010
open Turing
open ROOTTMGCDNative037 ROOTTMGCDDispatch018
open PA17TMRatArithmeticFrame005 PA17TMRatArithmeticFrameBudget008
open PSTRTMArithmetic008 PSTRTMLength004

def gcdScale (magnitude denominator : Nat) : Nat := natBits magnitude+natBits denominator+1
def gcdWindow (magnitude denominator : Nat) : Nat :=
  16384*(gcdScale magnitude denominator)^2+8*gcdScale magnitude denominator
def callInput (magnitude denominator : Nat) : List Bool := encodeNat magnitude++encodeNat denominator
def callOutput (magnitude denominator : Nat) : List Bool := encodeNat (Nat.gcd magnitude denominator)

def callInitial (magnitude denominator : Nat) (archive suffix : List Bool) : MachineState 3564 :=
  ⟨0,Tape.mk₂ (List.replicate (gcdWindow magnitude denominator) false ++ archive)
    (callInput magnitude denominator ++
      List.replicate (gcdWindow magnitude denominator+1-(callInput magnitude denominator).length) false ++ suffix)⟩

def callFinal (magnitude denominator left right : Nat) (archive suffix : List Bool) : MachineState 3564 :=
  ⟨(nativeFinal magnitude denominator).q,
    Tape.mk₂ (List.replicate left false ++ archive)
      (callOutput magnitude denominator ++
        List.replicate (right+1-(callOutput magnitude denominator).length) false ++ suffix)⟩

theorem gcd_bits_le_sum (magnitude denominator : Nat) :
    natBits (Nat.gcd magnitude denominator) ≤ natBits magnitude+natBits denominator := by
  by_cases hd : denominator = 0
  · simp [hd]
  · have hg := natBits_mono (Nat.gcd_le_right magnitude (Nat.pos_of_ne_zero hd))
    omega

theorem call_input_length (magnitude denominator : Nat) :
    (callInput magnitude denominator).length ≤ 8*gcdScale magnitude denominator := by
  simp only [callInput,List.length_append,encodeNat_length,gcdScale]
  omega

theorem call_output_length (magnitude denominator : Nat) :
    (callOutput magnitude denominator).length ≤ 8*gcdScale magnitude denominator := by
  have hg := gcd_bits_le_sum magnitude denominator
  simp only [callOutput,encodeNat_length,gcdScale]
  omega

theorem prefix_space (trace framed : List (MachineState 3564))
    (same : framed.map (displacement nativeGcdMachine) = trace.map (displacement nativeGcdMachine))
    (prefixLength inputLength : Nat) :
    visitedSpace nativeGcdMachine inputLength (framed.take prefixLength) =
      visitedSpace nativeGcdMachine inputLength (trace.take prefixLength) := by
  apply visitedSpace_of_displacements
  simpa only [List.map_take] using congrArg (List.take prefixLength) same

/-- The witnessed trace runs the fixed3565-label native gcd, including its
true HALT and complete canonical encoded result. Padding is a displayed real
entry layout, not an added qualification on the original Rat inputs. -/
theorem nativeGcd_framed (magnitude denominator : Nat) (archive suffix : List Bool) :
    ∃ (finalLeft finalRight : Nat) (trace : List (MachineState 3564)),
      PSTRTMSeq005.RunsFrom nativeGcdMachine (callInitial magnitude denominator archive suffix) trace
        (callFinal magnitude denominator finalLeft finalRight archive suffix) ∧
      8*gcdScale magnitude denominator ≤ finalLeft ∧
      8*gcdScale magnitude denominator ≤ finalRight ∧
      finalLeft+finalRight = 2*gcdWindow magnitude denominator ∧
      trace.length ≤ 16384*(gcdScale magnitude denominator)^2 ∧
      trace.map (displacement nativeGcdMachine) =
        (nativeTrace magnitude denominator).map (displacement nativeGcdMachine) ∧
      (∀ prefixLength inputLength,
        visitedSpace nativeGcdMachine inputLength (trace.take prefixLength) =
          visitedSpace nativeGcdMachine inputLength ((nativeTrace magnitude denominator).take prefixLength)) ∧
      ∀ inputLength, visitedSpace nativeGcdMachine inputLength trace ≤
        inputLength+32768*(gcdScale magnitude denominator)^2+1 := by
  have run := native_runs magnitude denominator
  have htime : (nativeTrace magnitude denominator).length ≤ 16384*(gcdScale magnitude denominator)^2 :=
    native_length_le magnitude denominator
  have hroom : (nativeTrace magnitude denominator).length ≤ gcdWindow magnitude denominator := by
    unfold gcdWindow
    omega
  have hfrom : PSTRTMSeq005.RunsFrom nativeGcdMachine (TM0.init (callInput magnitude denominator))
      (nativeTrace magnitude denominator) (nativeFinal magnitude denominator) :=
    ⟨run.1,run.2.1,run.2.2.1,run.2.2.2.1⟩
  obtain ⟨finalLeft,finalRight,trace,hfrun,hlen,hmap,hsum,hlend,hrend⟩ :=
    frame_runsFrom_budget nativeGcdMachine archive suffix (nativeTrace magnitude denominator)
      (TM0.init (callInput magnitude denominator)) (nativeFinal magnitude denominator)
      (gcdWindow magnitude denominator) (gcdWindow magnitude denominator) hfrom hroom hroom
  have hleft : 8*gcdScale magnitude denominator ≤ finalLeft := by
    unfold gcdWindow at hlend
    omega
  have hright : 8*gcdScale magnitude denominator ≤ finalRight := by
    unfold gcdWindow at hrend
    omega
  have inputFits : (callInput magnitude denominator).length ≤ gcdWindow magnitude denominator+1 := by
    have hb := call_input_length magnitude denominator
    unfold gcdWindow
    omega
  have outputFits : (callOutput magnitude denominator).length ≤ finalRight+1 := by
    have hb := call_output_length magnitude denominator
    omega
  have hi : frameCfg (gcdWindow magnitude denominator) (gcdWindow magnitude denominator) archive suffix
      (TM0.init (callInput magnitude denominator)) = callInitial magnitude denominator archive suffix := by
    unfold frameCfg TM0.init callInitial
    rw [frameTape_mk₁ _ _ _ _ _ inputFits]
    simp only [Fin.default_eq_zero]
  have hf : frameCfg finalLeft finalRight archive suffix (nativeFinal magnitude denominator) =
      callFinal magnitude denominator finalLeft finalRight archive suffix := by
    unfold frameCfg callFinal
    unfold callOutput at outputFits ⊢
    rw [native_final_tape,frameTape_mk₁ _ _ _ _ _ outputFits]
  rw [hi,hf] at hfrun
  refine ⟨finalLeft,finalRight,trace,hfrun,hleft,hright,?_,?_,hmap,?_,?_⟩
  · omega
  · omega
  · exact prefix_space (nativeTrace magnitude denominator) trace hmap
  · intro inputLength
    have hs := PSTRTMTrace002.visitedSpace_le nativeGcdMachine inputLength trace
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticGCDCall010
